#!/usr/bin/python3

import math
import gi
gi.require_version("Gtk", "3.0")
from gi.repository import Gtk, Gdk, GLib
import cairo
from logic import *
from env import GrasshopperEnv
from prover import FailedProof
import itertools

from graphics import *

def remove_prefix(text, prefix):
    if text.startswith(prefix):
        return text[len(prefix):]
    return text

class Splittable(GObject):
    def __init__(self, gui, coor_base, length_abstract, x_offset = 0):
        super().__init__()
        self.gui = gui
        self.env = self.gui.env
        self.coor_base = coor_base
        x,y = coor_base
        self.coor_start = self.env.ctx.model[x].value(), self.env.ctx.model[y].value()
        self.coor = self.coor_start
        self.length_abstract = length_abstract
        self.length = self.env.ctx.model[x].value()
        self.x_offset = x_offset

    @property
    def coor_abstract(self):
        x_start, y_start = self.coor_start
        x,y = self.coor
        x_base, y_base = self.coor_base
        return (
            x_base + TermInt(x - x_start),
            y_base + TermInt(y - y_start),
        )

    def model_updated(self):
        x_start, y_start = self.coor_start
        x,y = self.coor
        x_base, y_base = self.coor_base
        x_start2 = self.env.ctx.model[x_base].value()
        y_start2 = self.env.ctx.model[y_base].value()
        self.coor = (
            x - x_start + x_start2,
            y - y_start + y_start2,
        )
        self.coor_start = (
            x_start2,
            y_start2,
        )
        self.length = self.env.ctx.model[self.length_abstract].value()

    def split(self, n):
        AB = self.split_raw(n)
        if AB is None: return None
        A,B = AB
        return A,B
    def join(self, other):
        if other == self: return None
        if not isinstance(other, type(self)): return None
        if other.coor[1] != self.coor[1]: return None
        if other.coor[0] != self.coor[0] + self.length: return None
        res = self.join_raw(other)
        return res

    def point_interpretations(self, x, y):
        ax0,ay = self.coor_abstract
        for ax in (ax0, ax0+self.length_abstract):
            vx = self.env.ctx.model[ax].value()
            vy = self.env.ctx.model[ay].value()
            x_dist = abs(vx + self.x_offset - x)
            y_dist = abs(vy - y)
            precedence = (x_dist, y_dist)
            interpretation = (
                ax + TermInt(- vx + math.floor(x)),
                ay + TermInt(- vy + math.floor(y)),
            )
            yield precedence, interpretation

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
                label.move_center_to(split + l/2, 0.5)
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
        x,y = self.coor_abstract
        return (
            GJumps(self.gui, (x,y), jumps0),
            GJumps(self.gui, (x+jumps0.length,y), jumps1),
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
            self.mines_val.extend([True]*count)
            self.mines_val.extend([False]*(length-count))

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
            x2,_ = self.gui.point_interpretation(vx+n-0.5, vy)
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
        return GMines(self.gui, (x,y), mines0), GMines(self.gui, (x+mines0.length,y), mines1)

    def join_raw(self, other):
        # print('Left:', self.mines)
        # print('Right:', other.mines)
        res = GMines(self.gui, self.coor_abstract, self.mines + other.mines)
        # print('Join:', res.mines)
        return res

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
        self.win_size = win_size
        self.set_position(Gtk.WindowPosition.CENTER)
        self.connect("delete-event", Gtk.main_quit)
        self.show_all()

        self.scale = 50
        self.shift = (-3,0)

        self.objects = [
            GJumps(self, (TermInt(-1),TermInt(0)), jumps),
            GMines(self, (TermInt(0),TermInt(0)), mines),
        ]
        self.ctx_to_objects = dict()

    def update_win_size(self):
        self.win_size = (self.darea.get_allocated_width(), self.darea.get_allocated_height())

    @property
    def win_width(self):
        return self.win_size[0]
    @property
    def win_height(self):
        return self.win_size[1]
    @property
    def sidebar_width(self):
        return self.sidebar.bounding_box.width * self.win_height

    def pixel_to_coor(self, pixel):
        px,py = pixel
        w,h = self.win_size
        sx,sy = self.shift
        x = (px - w/2) / self.scale - sx
        y = (h/2 - py) / self.scale - sy
        return (x,y)
    def coor_to_pixel(self, pos):
        w,h = self.win_size
        sx,sy = self.shift
        x,y = pos
        x = float(x)
        y = float(y)
        px = (x + sx) * self.scale + w/2
        py = h/2 - (y + sy) * self.scale
        return px,py
    def set_shift(self, pixel, coor):
        w,h = self.win_size
        px,py = pixel
        x,y = coor
        sx = (px - w/2) / self.scale - x
        sy = (h/2 - py) / self.scale - y
        self.shift = sx,sy

    def on_scroll(self,w,e):
        coor = self.pixel_to_coor((e.x, e.y))
        if e.direction == Gdk.ScrollDirection.DOWN: self.scale *= 0.9
        elif e.direction == Gdk.ScrollDirection.UP: self.scale /= 0.9
        # print("zoom {}".format(self.scale))
        self.set_shift((e.x, e.y), coor)
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

    def grasp_objects(self, objs, x,y):
        self.obj_grasp = []
        for obj in objs:
            cx,cy = obj.coor
            self.obj_grasp.append((obj, x-cx, y-cy))

    def start_selection(self, x,y, keep = False):
        self.select_grasp = (x,y), (x,y)
        if not keep: self.selection = set()
        self.darea.queue_draw()
    def select_bounding_box(self):
        return BoundingBox.union(
            obj.bounding_box
            for obj in self.selection
        )

    def get_object(self, x,y):
        for obj in reversed(self.objects):
            if obj.bounding_box.contains(x,y):
                return obj
        return None
    
    def on_button_press(self, w, e):
        if e.type != Gdk.EventType.BUTTON_PRESS: return
        if e.button == 1 and (e.state & Gdk.ModifierType.SHIFT_MASK):
            self.start_selection(*self.pixel_to_coor((e.x, e.y)), keep = True)
        elif e.button == 1:
            x,y = self.pixel_to_coor((e.x, e.y))
            for obj in reversed(self.objects):
                if obj not in self.selection and obj.bounding_box.contains(x,y):
                    self.grasp_objects([obj], x,y)
                    break
            else:
                if self.select_bounding_box().contains(x,y):
                    self.grasp_objects(self.selection, x,y)
                else:
                    self.start_selection(x,y)
        elif e.button == 2:
            self.mb_grasp = self.pixel_to_coor((e.x, e.y))
        elif e.button == 3:
            x,y = self.pixel_to_coor((e.x, e.y))
            obj = self.get_object(x,y)
            if obj is not None:
                n = int(math.floor(x-obj.bounding_box.left+0.5))
                if n == 0: # join left
                    for obj2 in self.objects:
                        res = obj2.join(obj)
                        if res is not None:
                            self.objects.remove(obj)
                            self.objects.remove(obj2)
                            self.objects.append(res)
                            self.darea.queue_draw()
                            break
                elif n == obj.length: # join left
                    for obj2 in self.objects:
                        res = obj.join(obj2)
                        if res is not None:
                            self.objects.remove(obj)
                            self.objects.remove(obj2)
                            self.objects.append(res)
                            self.darea.queue_draw()
                            break
                else:
                    objs = obj.split(n)
                    if objs is not None:
                        self.objects.remove(obj)
                        self.objects.extend(objs)
                        self.darea.queue_draw()

    def on_button_release(self, w, e):
        if self.select_grasp is not None:
            select_box = BoundingBox.from_corners(*self.select_grasp)
            selection = set()
            for obj in self.objects:
                if select_box.contains(*obj.coor):
                    selection.add(obj)
            self.select_grasp = None
            if e.state & Gdk.ModifierType.SHIFT_MASK:
                if not selection:
                    x,y = self.pixel_to_coor((e.x, e.y))
                    for obj in reversed(self.objects):
                        if obj.bounding_box.contains(x,y):
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
            self.obj_grasp = None
        if e.button == 2:
            self.mb_grasp = None

    def on_motion(self,w,e):
        if self.select_grasp is not None:
            corner1, corner2 = self.select_grasp
            x,y = self.pixel_to_coor((e.x, e.y))
            self.select_grasp = corner1, (x,y)
            self.darea.queue_draw()
        if e.state & Gdk.ModifierType.BUTTON2_MASK:
            if self.mb_grasp is None: return
            self.set_shift((e.x, e.y), self.mb_grasp)
            self.darea.queue_draw()
        elif e.state & Gdk.ModifierType.BUTTON1_MASK:
            if self.obj_grasp is None: return
            for obj, gx, gy in self.obj_grasp:
                x,y = self.pixel_to_coor((e.x, e.y))
                obj.coor = (math.floor(x-gx+0.5), math.floor(y-gy+0.5))
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

        # debug commands
        elif keyval_name == 'u':
            self.model_updated()
            print("model updated")
        elif keyval_name == 'p':
            for obj in self.objects:
                print(type(obj))
                print('coor', obj.coor)
                print('coor_start:', obj.coor_start)
                print('coor_base:', obj.coor_base)
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
        cr.translate(*self.coor_to_pixel((0,0)))
        cr.scale(self.scale, -self.scale)

        # draw selection

        if self.selection:
            bb = self.select_bounding_box()
            self.select_bounding_box().draw(cr)
            self.select_style.paint(cr)
            for obj in self.objects:
                if obj in self.selection: continue
                corners = obj.bounding_box.corners
                if any(bb.contains(*corner) for corner in corners):
                    obj.bounding_box.add_offset(0.5).draw(cr)
                    cr.set_source_rgb(*bg_color)
                    cr.fill()
        if self.select_grasp is not None:
            (x1,y1),(x2,y2) = self.select_grasp
            cr.rectangle(x1,y2,x2-x1,y1-y2)
            self.select_style.paint(cr)

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
        text.move_center_to(*screen_box.center)
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

    def point_interpretation(self, x, y, skip = ()):
        if skip:
            objects = [
                obj for obj in self.objects
                if obj not in skip
            ]
        else:
            objects = self.objects
        if not objects:
            return TermInt(math.floor(x)), TermInt(math.floor(y))
        _, res = min(
            itertools.chain.from_iterable(
                obj.point_interpretations(x,y)
                for obj in objects
            ),
            key = lambda x: x[0]
        )
        return res

    ########
    # Model

    def model_updated(self):
        self.selection = set()
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
        self.env.ctx.add_model_constraints(equals(number, value+TermInt(change)))
        self.model_updated()


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
        x,y = jumps.coor_abstract
        rest_gr = GJumps(self, (x+J.length, y), rest)
        self.save_side_goals()
        self.model_updated()
        return J_gr, rest_gr

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
        assert jumps.coor[0]+1 == mines.coor[0]
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
        x,y = gmines.coor_abstract
        gmines0 = GMines(self, (x, y), mines0)
        gmine = GMines(self, (x+mines0.length, y), MineField([True]))
        gmines1 = GMines(self, (x+mines0.length+1, y), mines1)
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
        x,y = gjumps.coor_abstract
        gjump = GJumps(self, gjumps.coor_abstract, Jumps(jump))
        gjumpsr = GJumps(self, (x+jump.length, y), jumpsr)
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
        x,y = gmines.coor_abstract
        res = GMines(self, (x, y), mines.empty_copy)
        gmines.translate(0,-1)
        return res

    def cut_jumps_selected(self):
        if len(self.selection) != 2: return
        [jumps, mines] = self.selection
        if isinstance(mines, GJumps): jumps, mines = mines, jumps
        if not isinstance(jumps, GJumps): return
        if not isinstance(jumps.jumps, Jumps): return
        if not isinstance(mines, GMines): return
        res = self.cut_jumps(jumps, mines.coor_abstract[0])
        if res is None: return
        self.remove_objects(jumps)
        for res_obj in res: self.add_object(res_obj)
        self.darea.queue_draw()

    def cut_jumps(self, gjumps, pos):
        pos = pos - gjumps.coor_abstract[0] - 1
        jumps0, jump, jumps1 = self.env.split_jump_landings(gjumps.jumps, pos)
        self.env.ctx.add_model_constraints(
            jumps0.number > 0,
            jumps1.number > 0,
        )
        x,y = gjumps.coor_abstract
        gjumps0 = GJumps(self, (x, y), jumps0)
        gjump = GJumps(self, (x+jumps0.length, y), Jumps([jump]))
        gjumps1 = GJumps(self, (x+jumps0.length+jump.length, y), jumps1)
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
        gmines1.translate(0,-1)
        gmines2.translate(0,-1)
        return gmines_un

    def undeconstruct_selected(self):
        if len(self.selection) != 1: return
        [gobj] = self.selection
        if isinstance(gobj, GJumps): obj = gobj.jumps
        elif isinstance(gobj, GMines): obj = gobj.mines
        else: return
        res = self.env.undeconstruct(obj)
        if res is None: return
        if isinstance(res, (Jumps, JumpSet)): gtype = GJumps
        elif isinstance(res, MineField): gtype = GMines
        gres = gtype(self, gobj.coor_abstract, res)
        self.remove_objects(gobj)
        self.add_object(gres)
        self.darea.queue_draw()

if __name__ == "__main__":

    win = GrasshopperGui()
    Gtk.main()
