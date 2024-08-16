#!/usr/bin/python3

import math
import gi
gi.require_version("Gtk", "3.0")
from gi.repository import Gtk, Gdk, GLib
import cairo
from logic import *
from env import GrasshopperEnv

from graphics import *

def remove_prefix(text, prefix):
    if text.startswith(prefix):
        return text[len(prefix):]
    return text

class Splittable(GObject):
    def __init__(self, gui, coor_base):
        super().__init__()
        self.gui = gui
        self.env = self.gui.env
        self.coor_base = coor_base
        x,y = coor_base
        self.coor_start = self.env.ctx.model[x].value(), self.env.ctx.model[y].value()
        self.coor = self.coor_start

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
        x,y = self.coor_abstract
        print(x, y)
        x = self.env.ctx.model[x]
        y = self.env.ctx.model[y]
        self.coor = x.value(), y.value()

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

class GJumps(Splittable):
    def __init__(self, gui, coor, jumps, layer = 0):
        self.layer = layer

        self.jumps = jumps
        assert isinstance(jumps, (Jumps, JumpSet))

        super().__init__(gui, coor)
        self.model_updated()

    def model_updated(self):
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
        self.length = sum(self.lengths)

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
        Splittable.model_updated(self)

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

        print('Split:', self.jumps)
        print('Left:', jumps0)
        print('Right:', jumps1)
        print()
        x,y = self.coor_abstract
        return (
            GJumps(self.gui, (x,y), jumps0),
            GJumps(self.gui, (x+jumps0.length,y), jumps1),
        )

    def join_raw(self, other):
        if isinstance(self.jumps, JumpSet): return None
        if isinstance(other.jumps, JumpSet): return None
        print('Left:', self.jumps)
        print('Right:', other.jumps)
        res = GJumps(self.gui, self.coor_abstract, self.jumps + other.jumps)
        print('Join:', res.jumps)
        print()
        return res

class GMines(Splittable):
    def __init__(self, gui, coor, mines, layer = 0):
        self.layer = layer

        self.mines = mines

        super().__init__(gui, coor)
        self.model_updated()

    def model_updated(self):
        self.length = self.env.ctx.model[self.mines.length].value()

        self.mines_val = []
        for part in self.mines.parts:
            length = self.env.ctx.model[part.length].value()
            count = self.env.ctx.model[part.count].value()
            self.mines_val.extend([True]*count)
            self.mines_val.extend([False]*(length-count))

        self.raw_bounding_box = BoundingBox(0,-1,-0.5,self.length-0.5)
        Splittable.model_updated(self)

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

        assert split1 < split2
        if n == split1:
            mines0 = MineField.concat(*self.mines.parts[:index])
            mines1 = MineField.concat(*self.mines.parts[index:])
        else:
            part = self.mines.parts[index]
            assert isinstance(part, MineField)
            assert part.is_var
            local_split = n-split1
            part0, part1 = self.env.split_mines(part, TermInt(local_split))
            self.gui.model_updated()
            mines0 = self.mines.parts[:index] + (part0,)
            mines1 = (part1,) + self.mines.parts[index+1:]
            mines0 = MineField.concat(*mines0)
            mines1 = MineField.concat(*mines1)
        print('Split:', self.mines)
        print('Left:', mines0)
        print('Right:', mines1)
        print()
        x,y = self.coor_abstract
        return GMines(self.gui, (x,y), mines0), GMines(self.gui, (x+mines0.length,y), mines1)

    def join_raw(self, other):
        print('Left:', self.mines)
        print('Right:', other.mines)
        res = GMines(self.gui, self.coor_abstract, self.mines + other.mines)
        print('Join:', res.mines)
        return res

class GrasshopperGui(Gtk.Window):

    def __init__(self, win_size = (800, 600)):
        super().__init__()

        self.env = GrasshopperEnv(auto_assume = True)
        jumps = self.env.jumps
        mines = self.env.mines
        self.env.ctx.add_model_constraints(
            equals(jumps.length, 7),
            equals(mines.count, 2),
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
        self.shift = (0,0)

        self.objects = [
            GJumps(self, (TermInt(-1),TermInt(0)), jumps),
            GMines(self, (TermInt(0),TermInt(0)), mines),
        ]

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
        # print("Press:", keyval_name)
        if keyval_name == "Escape":
            Gtk.main_quit()
        elif keyval_name == 'm':
            self.pop_max_selected()
        elif keyval_name == 'i':
            self.induction_selected()
        # elif keyval_name == "Right":
        #     self.inf_index = min(self.inf_index+1, len(self.ginferences)-1)
        #     self.darea.queue_draw()

    def on_key_release(self,w,e):
        keyval_name = Gdk.keyval_name(e.keyval)

    def on_draw(self, wid, cr):
        self.update_win_size()

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
        self.model_updated()
        J_gr = GJumps(self, jumps.coor_abstract, Jumps(J))
        x,y = jumps.coor_abstract
        rest_gr = GJumps(self, (x+J.length, y), rest)
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

    def model_updated(self):
        for obj in self.objects:
            obj.model_updated()

    def induction(self, jumps, mines):
        assert jumps.coor[0]+1 == mines.coor[0]
        assert jumps.length == mines.length+1
        jumpso = self.env.induction(jumps.jumps, mines.mines)
        self.model_updated()
        jumpso_gr = GJumps(self, jumpso.coor_abstract, jumpso)
        return jumpso_gr

if __name__ == "__main__":

    win = GrasshopperGui()
    Gtk.main()
