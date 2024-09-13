#!/usr/bin/python3

import math
import gi
gi.require_version("Gtk", "3.0")
from gi.repository import Gtk, Gdk, GLib
import cairo
from logic import *
from env import GrasshopperEnv
from prover import FailedProof, extract_subst
import itertools
from collections import defaultdict

from graphics import *

def remove_prefix(text, prefix):
    if text.startswith(prefix):
        return text[len(prefix):]
    return text

class Splittable(GObject):
    def __init__(self, gui, coor_abstract, length_abstract, x_offset = 0):
        super().__init__()
        self.gui = gui
        self.env = self.gui.env
        self.coor_abstract = coor_abstract
        self.coor = self.env.ctx.model[coor_abstract].value()
        self.length_abstract = length_abstract
        self.length = self.env.ctx.model[length_abstract].value()
        self.x_offset = x_offset

    def model_updated(self):
        self.coor = self.env.ctx.model[self.coor_abstract].value()
        self.length = self.env.ctx.model[self.length_abstract].value()

    def split(self, n):
        AB = self.split_raw(n)
        if AB is None: return None
        A,B = AB
        return A,B
    def join(self, other):
        if other == self: return None
        if not isinstance(other, type(self)): return None
        if other.coor.y != self.coor.y: return None
        if other.coor.x != self.coor.x + self.length: return None
        res = self.join_raw(other)
        return res

    def translate(self, shift):
        self.coor_abstract = self.coor_abstract + shift
        self.coor = self.env.ctx.model[self.coor_abstract].value()

    def endpoints(self):
        ax,ay = self.coor_abstract
        vx,xy = self.coor
        yield (
            self.coor.x_shift(self.x_offset),
            self.coor_abstract,
            (self, 0),
        )
        yield (
            self.coor.x_shift(self.x_offset+self.length),
            self.coor_abstract.x_shift(self.length_abstract),
            (self, 1),
        )

    def point_interpretations(self, point):
        return self.points_interpretations([(point)])

    def points_interpretations(self, points):
        model = self.env.ctx.model
        for i,point in enumerate(points):
            for value, abstract, src in self.endpoints():
                x_dist, y_dist = (value - point).map(abs)
                precedence = (x_dist, y_dist, i)
                interpretation = abstract - model[abstract] + point.map(math.floor)
                yield precedence, interpretation, (i,src)

class GJumps(Splittable):
    def __init__(self, gui, coor, jumps, layer = 0):
        self.layer = layer

        self.jumps = jumps
        assert isinstance(jumps, (Jumps, JumpSet))

        super().__init__(gui, coor, jumps.length)
        self.model_updated()

    def model_updated(self):
        Splittable.model_updated(self)
        if isinstance(self.jumps, Jumps):
            parts = self.jumps.subsequences
        else:
            parts = [self.jumps]

        self.numbers = [
            self.env.ctx.model[part.number].value()
            for part in parts
        ]
        self.lengths = [
            self.env.ctx.model[part.length].value()
            for part in parts
        ]

        self.splits = [] # cumsum of lengths
        split = 0
        for l in self.lengths[:-1]:
            split += l
            self.splits.append(split)

        self.labels = [] # numerical labels
        for l,n,split in zip(self.lengths, self.numbers, [0] + self.splits):
            if n > 1:
                label = GText(str(n), self.layer)
                label.scale(0.7 / label.bounding_box.height)
                label.move_center_to(ArithPair(split + l/2, 0.5))
                self.labels.append(label)

        self.raw_bounding_box = BoundingBox(1,0,0,self.length)

    def clone(self):
        return GJumps(self.gui, self.coor_abstract, self.jumps, self.layer)

    def draw_raw(self, cr, layer):
        if layer != self.layer: return

        cr.set_line_width(0.1)
        if isinstance(self.jumps, Jumps):
            cr.set_source_rgb(0,0,0)
        else:
            cr.set_source_rgb(0.5, 0, 1.0) # purple

        for l,n,split in zip(self.lengths, self.numbers, [0] + self.splits):
            if split > 0:
                cr.move_to(split, 1)
                cr.line_to(split, 0)
                cr.stroke()
            if n > 1:
                cr.move_to(max(split, 0.25), 0.5)
                cr.line_to(min(split + l, self.length - 0.25), 0.5)
                cr.stroke()

        cr.move_to(0, 0)
        cr.line_to(0.5, 1)
        cr.line_to(self.length-0.5, 1)
        cr.line_to(self.length, 0)
        cr.stroke()

        for label in self.labels:
            bb = label.bounding_box
            cr.set_source_rgb(1,1,1)
            cr.rectangle(bb.left - 0.1, bb.bottom, bb.width + 0.2, bb.height)
            cr.fill()
            label.draw(cr, layer)

    def split_raw(self, n):
        if isinstance(self.jumps, JumpSet): return None
        if n not in self.splits: return None
        index = self.splits.index(n)+1
        jumps0 = Jumps.concat(*self.jumps.parts[:index])
        jumps1 = Jumps.concat(*self.jumps.parts[index:])

        # print('Split:', self.jumps)
        # print('Left:', jumps0)
        # print('Right:', jumps1)
        # print()
        return (
            GJumps(self.gui, self.coor_abstract, jumps0),
            GJumps(self.gui, self.coor_abstract.x_shift(jumps0.length), jumps1),
        )

    def join_raw(self, other):
        if isinstance(self.jumps, JumpSet): return None
        if isinstance(other.jumps, JumpSet): return None
        # print('Left:', self.jumps)
        # print('Right:', other.jumps)
        res = GJumps(self.gui, self.coor_abstract, self.jumps + other.jumps)
        # print('Join:', res.jumps)
        # print()
        return res

class GMines(Splittable):
    def __init__(self, gui, coor, mines, layer = 0):
        self.layer = layer

        self.mines = mines

        super().__init__(gui, coor, mines.length, x_offset = -0.5)
        self.model_updated()

    def model_updated(self):
        Splittable.model_updated(self)

        self.mines_val = []
        for part in self.mines.parts:
            if isinstance(part, TermBool):
                length = 1
                count = int(self.env.ctx.model[part].value())
            elif isinstance(part, MineField):
                length = self.env.ctx.model[part.length].value()
                count = self.env.ctx.model[part.count].value()

            part_val = [False]*length
            pos_to_val = self.gui.mines_to_known.get(part, dict())
            remains = count
            for pos,val in pos_to_val.items():
                if val and 0 <= pos < length:
                    remains -= 1
                    part_val[pos] = True
            for pos in range(length):
                if not remains: break
                if pos not in pos_to_val:
                    part_val[pos] = True
                    remains -= 1
            self.mines_val.extend(part_val)

        self.raw_bounding_box = BoundingBox(0,-1,-0.5,self.length-0.5)

    def clone(self):
        return GMines(self.gui, self.coor_abstract, self.mines, self.layer)

    def draw_raw(self, cr, layer):
        if layer != self.layer: return

        hl_splits = set()
        last = 0
        for part in self.mines.subsequences:
            last += self.env.ctx.model[part.length].value()
            hl_splits.add(last)

        for i in range(1,self.length):
            cr.move_to(i-0.5, 0)
            cr.line_to(i-0.5, -1)
            if i in hl_splits:
                cr.set_source_rgb(0,0,0)
            else:
                cr.set_source_rgb(0.7,0.7,0.7)
            cr.set_line_width(0.1)
            cr.stroke()

        cr.move_to(0,-1)
        cr.line_to(self.length-1,-1)
        cr.arc(self.length-1, -0.5, 0.5, -math.pi/2, math.pi/2)
        cr.line_to(0,0)
        cr.arc(0, -0.5, 0.5, math.pi/2, 3*math.pi/2)
        cr.close_path()
        cr.set_source_rgb(0,0,0)
        cr.set_line_width(0.1)
        cr.stroke()

        for index, is_mine in enumerate(self.mines_val):
            if is_mine:
                cr.arc(index, -0.5, 0.2, 0, 2*math.pi)
                cr.fill()

    def split_raw(self, n):
        if not (1 <= n < self.length): return None
        index = 0
        split1 = 0
        for part in self.mines.subsequences:
            split2 = split1 + self.env.ctx.model[part.length].value()
            if n < split2: break
            index += 1
            split1 = split2

        x,y = self.coor_abstract
        vx,vy = self.coor
        assert split1 < split2
        if n == split1:
            mines0 = MineField.concat(*self.mines.parts[:index])
            mines1 = MineField.concat(*self.mines.parts[index:])
        else:
            part = self.mines.parts[index]
            assert isinstance(part, MineField)
            assert part.is_var
            (x2,_),_ = self.gui.point_interpretation(self.coor.x_shift(n-0.5))
            local_split = x2+(1-x)
            for ini_part in self.mines.subsequences[:index]:
                local_split = local_split - ini_part.length
            part0, part1 = self.env.split_mines(part, local_split)
            mines0 = self.mines.parts[:index] + (part0,)
            mines1 = (part1,) + self.mines.parts[index+1:]
            mines0 = MineField.concat(*mines0)
            mines1 = MineField.concat(*mines1)
        # print('Split:', self.mines)
        # print('Left:', mines0)
        # print('Right:', mines1)
        # print()
        self.gui.save_side_goals()
        self.gui.model_updated()
        return (
            GMines(self.gui, ArithPair(x,y), mines0),
            GMines(self.gui, ArithPair(x+mines0.length,y), mines1),
        )

    def join_raw(self, other):
        # print('Left:', self.mines)
        # print('Right:', other.mines)
        res = GMines(self.gui, self.coor_abstract, self.mines + other.mines)
        # print('Join:', res.mines)
        return res

    def filter(self, f):
        x,y = self.coor_abstract
        res = [([], x)]
        for part in self.mines.subsequences:
            x += part.length
            if not f(part):
                res.append(([], x))
            else:
                res[-1][0].append(part)
        res = [(parts, x) for (parts, x) in res if len(parts) > 0]
        res = [
            GMines(self.gui, ArithPair(x,y), MineField.concat(*parts))
            for parts,x in res
        ]
        return res

class ObjGrasp:
    def __init__(self, gui, objs, coor, ori_selection = set()):
        self.gui = gui
        self.objs = objs
        self.coor = coor
        self.last_match = []
        self.ori_selection = ori_selection
        self.moved = False

    def move_coor(self, coor):
        shift = (coor - self.coor + ArithPair(0.5, 0.5)).map(math.floor)
        if shift == ArithPair(0,0):
            return False

        grasp_points = itertools.chain.from_iterable(
            obj.endpoints()
            for obj in self.objs
        )
        grasp_points = [
            (coor + shift, abstract, src)
            for coor, abstract, src in grasp_points
        ]
        grasp_points.sort(
            key = lambda p: (p[0].x - coor.x)**2 + (p[0].y - coor.y)**2,
        )
        grasp_points_vals = [p[0] for p in grasp_points]
        abstract, (i,src) = self.gui.points_interpretation(
            grasp_points_vals,
            skip = set(self.objs)
        )
        if src is not None:
            _, rel_abstract, src2 = grasp_points[i]
            self.last_match = [src, src2]
            # print("abstract:", abstract)
            # print("rel_abstract:", rel_abstract)
            abstract_shift = abstract - rel_abstract
            # correct value (offset could have messed it up)
            abstract_shift = abstract_shift - self.gui.env.ctx.model[abstract_shift] + shift
        else:
            abstract_shift = shift
        for obj in self.objs:
            obj.translate(abstract_shift)
        self.coor = self.coor + shift
        self.moved = True
        return True

    def draw_match(self, cr):
        for obj,side in self.last_match:
            cr.save()
            cr.translate(*obj.coor)
            if isinstance(obj, GMines):
                cr.translate(-0.5, -1)
            if side:
                cr.translate(obj.length, 0)
                cr.scale(-1,1)
            cr.rectangle(0,0,0.2,1)

            pattern = cairo.LinearGradient(0,0,0.2,0) 
            pattern.add_color_stop_rgba(0, 0, 1, 0, 1)   
            pattern.add_color_stop_rgba(1, 0, 1, 0, 0)
            cr.set_source(pattern)

            cr.fill()
            cr.restore()

    def revert_selection(self):
        if self.moved:
            self.gui.selection = self.ori_selection

class GrasshopperGui(Gtk.Window):

    def __init__(self, win_size = (800, 600)):
        super().__init__()

        self.env = GrasshopperEnv(auto_assume = True)
        jumps = self.env.jumps
        mines = self.env.mines
        self.env.ctx.add_model_constraints(
            equals(jumps.length, 10),
            equals(mines.count, 3),
        )

        self.obj_grasp = None
        self.mb_grasp = None

        self.select_grasp = None
        self.selection = set()
        self.select_style = Style(fill = (0,0,1,0.1))
        self.mines_to_known = dict()

        self.darea = Gtk.DrawingArea()
        self.darea.connect("draw", self.on_draw)
        self.darea.set_events(Gdk.EventMask.BUTTON_PRESS_MASK |
                              Gdk.EventMask.BUTTON_RELEASE_MASK |
                              Gdk.EventMask.KEY_PRESS_MASK |
                              Gdk.EventMask.KEY_RELEASE_MASK |
                              Gdk.EventMask.SCROLL_MASK |
                              Gdk.EventMask.POINTER_MOTION_MASK)
        self.add(self.darea)

        self.darea.connect("button-press-event", self.on_button_press)
        self.darea.connect("button-release-event", self.on_button_release)
        self.darea.connect("scroll-event", self.on_scroll)
        self.darea.connect("motion-notify-event", self.on_motion)
        self.connect("key-press-event", self.on_key_press)
        self.connect("key-release-event", self.on_key_release)

        self.set_title("Grasshopper GUI")
        self.resize(*win_size)
        self.win_size = ArithPair(*win_size)
        self.set_position(Gtk.WindowPosition.CENTER)
        self.connect("delete-event", Gtk.main_quit)
        self.show_all()

        self.scale = 50
        self.shift = ArithPair(-3,0)

        self.objects = [
            GJumps(self, ArithPair(TermInt(-1),TermInt(0)), jumps),
            GMines(self, ArithPair(TermInt(0),TermInt(0)), mines),
        ]
        self.ctx_to_objects = dict()

    def update_win_size(self):
        self.win_size = ArithPair(
            self.darea.get_allocated_width(),
            self.darea.get_allocated_height(),
        )

    @property
    def win_width(self):
        return self.win_size.x
    @property
    def win_height(self):
        return self.win_size.y
    @property
    def sidebar_width(self):
        return self.sidebar.bounding_box.width * self.win_height

    def pixel_to_coor(self, pixel):
        return (pixel - self.win_size/2).y_flip() / self.scale - self.shift
    def coor_to_pixel(self, pos):
        return (pos + self.shift).y_flip() * self.scale + self.win_size/2
    def set_shift(self, pixel, coor):
        self.shift = (pixel - self.win_size/2).y_flip() / self.scale - coor

    def on_scroll(self,w,e):
        pixel = ArithPair(e.x, e.y)
        coor = self.pixel_to_coor(pixel)
        if e.direction == Gdk.ScrollDirection.DOWN: self.scale *= 0.9
        elif e.direction == Gdk.ScrollDirection.UP: self.scale /= 0.9
        # print("zoom {}".format(self.scale))
        self.set_shift(pixel, coor)
        self.darea.queue_draw()

    def add_object(self, obj):
        assert isinstance(obj, GObject)
        self.objects.append(obj)
    def remove_objects(self, *removed):
        removed = set(removed)
        self.selection.difference_update(removed)
        self.objects = [
            obj for obj in self.objects
            if obj not in removed
        ]

    def grasp_objects(self, objs, coor):
        ori_selection = self.selection
        self.selection = set(objs)
        self.obj_grasp = ObjGrasp(self, objs, coor, ori_selection = ori_selection)

    def start_selection(self, coor, keep = False):
        self.select_grasp = coor, coor
        if not keep: self.selection = set()
        self.darea.queue_draw()
    def select_bounding_box(self):
        return BoundingBox.union(
            obj.bounding_box
            for obj in self.selection
        )

    def get_object(self, coor):
        for obj in reversed(self.objects):
            if obj.bounding_box.contains(coor):
                return obj
        return None
    
    def on_button_press(self, w, e):
        pixel = ArithPair(e.x, e.y)
        if e.type != Gdk.EventType.BUTTON_PRESS: return
        if e.button == 1 and (e.state & Gdk.ModifierType.SHIFT_MASK):
            self.start_selection(self.pixel_to_coor(pixel), keep = True)
        elif e.button == 1:
            coor = self.pixel_to_coor(pixel)
            for obj in reversed(self.objects):
                if obj not in self.selection and obj.bounding_box.contains(coor):
                    self.grasp_objects([obj], coor)
                    self.darea.queue_draw()
                    break
            else:
                if self.select_bounding_box().contains(coor):
                    self.grasp_objects(self.selection, coor)
                else:
                    self.start_selection(coor)
        elif e.button == 2:
            self.mb_grasp = self.pixel_to_coor(pixel)
        elif e.button == 3:
            coor = self.pixel_to_coor(pixel)
            obj = self.get_object(coor)
            if obj is not None:
                n = int(math.floor(coor.x-obj.bounding_box.left+0.5))
                if n == 0: # join left
                    for obj2 in self.objects:
                        res = obj2.join(obj)
                        if res is not None:
                            self.remove_objects(obj, obj2)
                            self.objects.append(res)
                            self.darea.queue_draw()
                            break
                elif n == obj.length: # join left
                    for obj2 in self.objects:
                        res = obj.join(obj2)
                        if res is not None:
                            self.remove_objects(obj, obj2)
                            self.objects.append(res)
                            self.darea.queue_draw()
                            break
                else:
                    objs = obj.split(n)
                    if objs is not None:
                        self.remove_objects(obj)
                        self.objects.extend(objs)
                        self.darea.queue_draw()

    def on_button_release(self, w, e):
        pixel = ArithPair(e.x, e.y)
        if self.select_grasp is not None:
            select_box = BoundingBox.from_corners(*self.select_grasp)
            selection = set()
            for obj in self.objects:
                if select_box.contains(obj.coor):
                    selection.add(obj)
            self.select_grasp = None
            if e.state & Gdk.ModifierType.SHIFT_MASK:
                if not selection:
                    coor = self.pixel_to_coor(pixel)
                    for obj in reversed(self.objects):
                        if obj.bounding_box.contains(coor):
                            selection.add(obj)
                            break
                if all(obj in self.selection for obj in selection):
                    self.selection.difference_update(selection)
                else:
                    self.selection.update(selection)
            else:
                self.selection = selection
            self.darea.queue_draw()
        if e.button == 1:
            if self.obj_grasp:
                self.darea.queue_draw()
                self.obj_grasp.revert_selection()
                self.obj_grasp = None
        if e.button == 2:
            self.mb_grasp = None

    def on_motion(self,w,e):
        pixel = ArithPair(e.x, e.y)
        if self.select_grasp is not None:
            corner1, corner2 = self.select_grasp
            coor = self.pixel_to_coor(pixel)
            self.select_grasp = corner1, coor
            self.darea.queue_draw()
        if e.state & Gdk.ModifierType.BUTTON2_MASK:
            if self.mb_grasp is None: return
            self.set_shift(pixel, self.mb_grasp)
            self.darea.queue_draw()
        elif e.state & Gdk.ModifierType.BUTTON1_MASK:
            if self.obj_grasp is None: return
            coor = self.pixel_to_coor(pixel)
            if self.obj_grasp.move_coor(coor):
                self.darea.queue_draw()

    def on_key_press(self,w,e):
        keyval = e.keyval
        keyval_name = Gdk.keyval_name(keyval)
        # do not distinguish standard and numlock key variants
        keyval_name = remove_prefix(keyval_name, "KP_")
        if keyval_name == "Escape":
            Gtk.main_quit()
        elif keyval_name == 'm':
            self.pop_max_selected()
        elif keyval_name == 'i':
            self.induction_selected()
        elif keyval_name == 's':
            self.solve_with_jumps_selected()
        elif keyval_name == 'S': # Sorry
            print("!!! SORRY USED !!!")
            self.env._next_goal()
            self.restore_side_goal()
            self.model_updated()
        elif keyval_name == 'minus':
            self.change_length_selected(-1)
        elif keyval_name == 'equal':
            self.change_length_selected(1)
        elif keyval_name == 'underscore':
            self.change_count_selected(-1)
        elif keyval_name == 'plus':
            self.change_count_selected(1)
        elif keyval_name == 'f':
            self.pop_first_selected()
        elif keyval_name == '0':
            self.empty_mines_selected()
        elif keyval_name == 'c':
            self.cut_jumps_selected()
        elif keyval_name == 'u':
            self.union_mines_selected()
        elif keyval_name == 'z':
            self.undeconstruct_selected()
        elif keyval_name == 'a':
            self.pop_avoiding_selected()
        elif keyval_name == 'r':
            self.reset_mines()

        # debug commands
        elif keyval_name == 'u':
            self.model_updated()
            print("model updated")
        elif keyval_name == 'p':
            for obj in self.objects:
                print(obj)
                print('coor', obj.coor)
                print('coor_abstract:', obj.coor_abstract)
                print()
            self.env.ctx.model.show()
        # else: print("Press:", keyval_name)

    def on_key_release(self,w,e):
        keyval_name = Gdk.keyval_name(e.keyval)

    def on_draw(self, wid, cr):
        self.update_win_size()

        if self.env.proven:
            self.draw_solved(cr)
            return

        bg_color = (1,1,1)
        cr.rectangle(0,0,*self.win_size)
        cr.set_source_rgb(*bg_color)
        cr.fill()

        cr.save()
        cr.translate(*self.coor_to_pixel(ArithPair(0,0)))
        cr.scale(self.scale, -self.scale)

        # draw selection

        if self.selection:
            bb = self.select_bounding_box()
            self.select_bounding_box().draw(cr)
            self.select_style.paint(cr)
            # for obj in self.objects:
            #     if obj in self.selection: continue
            #     corners = obj.bounding_box.corners
            #     if any(bb.contains(*corner) for corner in corners):
            #         obj.bounding_box.add_offset(0.5).draw(cr)
            #         cr.set_source_rgb(*bg_color)
            #         cr.fill()
        if self.select_grasp is not None:
            (x1,y1),(x2,y2) = self.select_grasp
            cr.rectangle(x1,y2,x2-x1,y1-y2)
            self.select_style.paint(cr)

        if self.obj_grasp is not None:
            self.obj_grasp.draw_match(cr)

        # draw objects
        for layer in range(3):
            for obj in self.objects:
                obj.draw(cr, layer)

        cr.restore()

    def draw_solved(self, cr):
        bg_color = (0,1,0)
        w,h = self.win_size
        cr.rectangle(0,0,w,h)
        cr.set_source_rgb(*bg_color)
        cr.fill()
        screen_box = BoundingBox(0,-h,0,w)
        text = GText("Problem Solved!", 0)
        text.fit_to(screen_box)
        text.scale(0.8)
        text.move_center_to(screen_box.center)
        cr.scale(1,-1)
        text.draw(cr, 0)

    def save_side_goals(self):
        for ctx in reversed(self.env.ctx_stack):
            if ctx in self.ctx_to_objects: break
            self.ctx_to_objects[ctx] = [
                obj.clone()
                for obj in self.objects
            ]
    def restore_side_goal(self):
        if self.env.ctx in self.ctx_to_objects:
            self.objects = self.ctx_to_objects[self.env.ctx]

    def point_interpretation(self, coor, skip = ()):
        return self.points_interpretation([(coor)], skip)
    def points_interpretation(self, points, skip):
        if skip:
            objects = [
                obj for obj in self.objects
                if obj not in skip
            ]
        else:
            objects = self.objects
        if not objects:
            return points[0], (0,None)
        _, res, src = min(
            itertools.chain.from_iterable(
                obj.points_interpretations(points)
                for obj in objects
            ),
            key = lambda x: x[0]
        )
        return res, src

    def reset_mines(self):
        self.selection = set()
        _, subst = extract_subst(self.env.ctx.raw_facts)
        mines = subst[self.env.mines]
        part_to_remain = defaultdict(int)
        for part in mines.subsequences:
            part_to_remain[part] += 1

        part_to_found = defaultdict(int)
        def discard_main_part(part):
            if part_to_remain[part] == 0:
                return True
            part_to_remain[part] -= 1
            part_to_found[part] += 1
            return False

        rem_mines = []
        for obj in self.objects:
            if not isinstance(obj, GMines): continue
            rem_mines.extend(obj.filter(discard_main_part))
        self.objects = [
            obj for obj in self.objects
            if not isinstance(obj, GMines)
        ]

        def keep_found(part):
            if part_to_found[part] == 0:
                return False
            part_to_found[part] -= 1
            return True
        main_gmines = GMines(
            self,
            ArithPair(TermInt(0),TermInt(0)),
            mines
        )

        if any(obj.y == 0 for obj in rem_mines):
            for obj in rem_mines:
                obj.translate(ArithPair(0,-1))

        self.objects.extend(rem_mines)
        self.objects.extend(main_gmines.filter(keep_found))
        self.darea.queue_draw()

    ########
    # Model

    def model_updated(self):
        self.selection = set()
        self.mines_to_known = dict()

        if not self.env.proven:
            for prop, value in self.env.ctx.model.base_dict.items():
                if prop.f != MineField.getitem: continue
                mines, n = prop.args
                n = self.env.ctx.model[n].value()
                value = value.value()
                pos_to_value = self.mines_to_known.setdefault(mines, dict())
                pos_to_value[n] = value

            if not self.env.proven:
                for obj in self.objects:
                    obj.model_updated()

        self.darea.queue_draw()

    def change_length_selected(self, change):
        if len(self.selection) != 1: return
        [obj] = self.selection
        if isinstance(obj, GJumps):
            self.change_number(obj.jumps.length, change)
        elif isinstance(obj, GMines):
            self.change_number(obj.mines.length, change)

    def change_count_selected(self, change):
        if len(self.selection) != 1: return
        [obj] = self.selection
        if isinstance(obj, GJumps):
            self.change_number(obj.jumps.number, change)
        elif isinstance(obj, GMines):
            self.change_number(obj.mines.count, change)

    def change_number(self, number, change):
        value = self.env.ctx.model[number]
        selection = self.selection
        self.env.ctx.add_model_constraints(equals(number, value+TermInt(change)))
        self.model_updated()
        self.selection = selection

    # Model
    #####################
    # Environment steps

    def pop_max_selected(self):
        if len(self.selection) != 1: return
        [jumps] = self.selection
        if not isinstance(jumps, GJumps): return
        if not isinstance(jumps.jumps, JumpSet): return
        try:
            J, jumps_rest = self.pop_max(jumps)
        except Exception as e:
            print(e)
            return
        self.remove_objects(jumps)
        self.add_object(J)
        self.add_object(jumps_rest)
        self.darea.queue_draw()

    def pop_max(self, jumps):
        J, rest = self.env.pop_max_jump(jumps.jumps)
        J_gr = GJumps(self, jumps.coor_abstract, Jumps(J))
        rest_gr = GJumps(self, jumps.coor_abstract.x_shift(J.length), rest)
        self.save_side_goals()
        self.model_updated()
        return J_gr, rest_gr

    def pop_avoiding_selected(self):
        if len(self.selection) != 2: return
        [jumps,mines] = self.selection
        if isinstance(mines, GJumps): jumps, mines = mines, jumps
        if not isinstance(jumps, GJumps): return
        if not isinstance(jumps.jumps, JumpSet): return
        if not isinstance(mines, GMines): return
        if not jumps.x+1 == mines.x: return
        try:
            jump, jumpsr = self.pop_avoiding(jumps, mines)
        except Exception as e:
            print(e)
            return
        self.remove_objects(jumps)
        self.add_object(jump)
        self.add_object(jumpsr)
        self.darea.queue_draw()

    def pop_avoiding(self, gjumps, gmines):
        jump, jumpsr = self.env.pop_avoiding_jump(gjumps.jumps, gmines.mines)
        gjump = GJumps(self, gjumps.coor_abstract, Jumps(jump))
        gjumpsr = GJumps(self, gjumps.coor_abstract + ArithPair(jump.length, 0), jumpsr)
        self.save_side_goals()
        self.model_updated()
        return gjump, gjumpsr

    def induction_selected(self):
        if len(self.selection) != 2: return
        [jumps, mines] = self.selection
        if isinstance(mines, GJumps): jumps, mines = mines, jumps
        if not isinstance(jumps, GJumps): return
        if not isinstance(jumps.jumps, JumpSet): return
        if not isinstance(mines, GMines): return
        try:
            jumpso = self.induction(jumps, mines)
        except Exception as e:
            print(e)
            return
        self.remove_objects(jumps)
        self.add_object(jumpso)
        self.darea.queue_draw()

    def induction(self, jumps, mines):
        assert jumps.x+1 == mines.x
        assert jumps.length == mines.length+1
        jumpso = self.env.induction(jumps.jumps, mines.mines)
        jumpso_gr = GJumps(self, jumps.coor_abstract, jumpso)
        self.save_side_goals()
        self.model_updated()
        return jumpso_gr

    def solve_with_jumps_selected(self):
        if len(self.selection) != 1: return
        [jumps] = self.selection
        if not isinstance(jumps, GJumps): return
        if not isinstance(jumps.jumps, Jumps): return
        self.solve_with_jumps(jumps)

    def solve_with_jumps(self, jumps):
        try:
            self.env.solve_with_jumps(jumps.jumps)
            self.save_side_goals()
        except FailedProof:
            return
        self.restore_side_goal()
        self.model_updated()

    def pop_first_selected(self):
        if len(self.selection) != 1: return
        [obj] = self.selection
        if isinstance(obj, GJumps):
            res = self.pop_first_jump(obj)
        else:
            res = self.pop_first_mine(obj)
        if res is None: return
        self.remove_objects(obj)
        for res_obj in res: self.add_object(res_obj)
        self.darea.queue_draw()

    def pop_first_mine(self, gmines):
        mines = gmines.mines
        if not mines.is_var: return None
        if self.env.ctx.model[mines.count].value() == 0: return None
        mines0, mines1 = self.env.split_first_mine(mines)
        self.env.ctx.add_model_constraints(
            mines0.length > 0,
            mines1.length > 0,
        )
        gmines0 = GMines(self, gmines.coor_abstract, mines0)
        gmine = GMines(self, gmines.coor_abstract.x_shift(mines0.length), MineField([True]))
        gmines1 = GMines(self, gmines.coor_abstract.x_shift(mines0.length+1), mines1)
        self.save_side_goals()
        self.model_updated()
        return gmines0, gmine, gmines1

    def pop_first_jump(self, gjumps):
        jumps = gjumps.jumps
        if isinstance(jumps, JumpSet):
            return None
        if self.env.ctx.model[jumps.length].value() == 0:
            return None
        jump, jumpsr = self.env.pop_first_jump(jumps)
        gjump = GJumps(self, gjumps.coor_abstract, Jumps(jump))
        gjumpsr = GJumps(self, gjumps.coor_abstract.x_shift(jump.length), jumpsr)
        self.save_side_goals()
        self.model_updated()
        return gjump, gjumpsr

    def empty_mines_selected(self):
        if len(self.selection) != 1: return
        [gmines] = self.selection
        if not isinstance(gmines, GMines): return
        res = self.empty_mines(gmines)
        self.add_object(res)
        self.darea.queue_draw()        

    def empty_mines(self, gmines):
        mines = gmines.mines
        res = GMines(self, gmines.coor_abstract, mines.empty_copy)
        gmines.translate(ArithPair(0,-1))
        return res

    def cut_jumps_selected(self):
        if len(self.selection) != 2: return
        [jumps, mines] = self.selection
        if isinstance(mines, GJumps): jumps, mines = mines, jumps
        if not isinstance(jumps, GJumps): return
        if not isinstance(jumps.jumps, Jumps): return
        if not isinstance(mines, GMines): return
        res = self.cut_jumps(jumps, mines.coor_abstract.x)
        if res is None: return
        self.remove_objects(jumps)
        for res_obj in res: self.add_object(res_obj)
        self.darea.queue_draw()

    def cut_jumps(self, gjumps, pos):
        pos = pos - gjumps.coor_abstract.x - 1
        jumps0, jump, jumps1 = self.env.split_jump_landings(gjumps.jumps, pos)
        self.env.ctx.add_model_constraints(
            jumps0.number > 0,
            jumps1.number > 0,
        )
        gjumps0 = GJumps(self, gjumps.coor_abstract, jumps0)
        gjump = GJumps(self, gjumps.coor_abstract.x_shift(jumps0.length), Jumps([jump]))
        gjumps1 = GJumps(self, gjumps.coor_abstract.x_shift(jumps0.length+jump.length), jumps1)
        self.save_side_goals()
        self.model_updated()
        return gjumps0, gjump, gjumps1

    def union_mines_selected(self):
        if len(self.selection) != 2: return
        mines1, mines2 = self.selection
        if not isinstance(mines1, GMines): return
        if not isinstance(mines2, GMines): return
        res = self.union_mines(mines1, mines2)
        if res is None: return
        self.add_object(res)
        self.darea.queue_draw()

    def union_mines(self, gmines1, gmines2):
        if gmines1.x != gmines2.x:
            return None
        if gmines1.y < gmines2.y:
            gmines1, gmines2 = gmines2, gmines1
        mines_un = self.env.union_mines(gmines1.mines, gmines2.mines)
        gmines_un = GMines(self, gmines1.coor_abstract, mines_un)
        self.save_side_goals()
        self.model_updated()
        gmines1.translate(ArithPair(0,-1))
        gmines2.translate(ArithPair(0,-1))
        return gmines_un

    def undeconstruct_selected(self):
        has_jump_set = any(
            isinstance(obj, GJumps) and isinstance(obj.jumps, JumpSet)
            for obj in self.selection
        )
        if has_jump_set:
            if not all(isinstance(obj, GJumps) for obj in self.selection):
                return
            parts = []
            for gobj in self.selection:
                if isinstance(gobj.jumps, JumpSet):
                    parts.append(gobj.jumps)
                else:
                    parts.append(gobj.jumps.s)
            obj = JumpSet.merge(*parts)
        elif len(self.selection) == 1:
            [gobj] = self.selection
            if isinstance(gobj, GJumps): obj = gobj.jumps
            elif isinstance(gobj, GMines): obj = gobj.mines
            else: return
        else:
            return
        res = self.env.undeconstruct(obj)
        if res is None: return
        if isinstance(res, (Jumps, JumpSet)): gtype = GJumps
        elif isinstance(res, MineField): gtype = GMines
        gobj0 = min(self.selection, key = lambda obj: obj.x)
        gres = gtype(self, gobj0.coor_abstract, res)
        self.remove_objects(*self.selection)
        self.add_object(gres)
        self.darea.queue_draw()

if __name__ == "__main__":

    win = GrasshopperGui()
    Gtk.main()
