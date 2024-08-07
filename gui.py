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

    def split(self, n):
        AB = self.split_raw(n)
        if AB is None: return None
        A,B = AB
        A.center = self.center
        B.center = (self.center[0]+n, self.center[1])
        return A,B
    def join(self, other):
        if other == self: return None
        if not isinstance(other, type(self)): return None
        if other.center[1] != self.center[1]: return None
        if other.center[0] != self.center[0] + self.length: return None
        res = self.join_raw(other)
        res.center = self.center
        return res

class GJumps(Splittable):
    def __init__(self, env, model, jumps, layer = 0):
        self.layer = layer

        self.env = env
        self.model = model
        self.jumps = jumps
        self.jumps_val = model[jumps].value()

        self.length = model[jumps.length].value()

        self.splits = []
        split = 0
        for l in self.jumps_val[:-1]:
            split += l
            self.splits.append(split)
        self.raw_bounding_box = BoundingBox(1,0,0,self.length)
        super().__init__()

    def draw_raw(self, cr, layer):
        if layer != self.layer: return

        hl_splits = set()
        last = 0
        for part in self.jumps.subsequences:
            last += self.model[part.number].value()
            hl_splits.add(last)

        for i,split in enumerate(self.splits):
            cr.move_to(split, 1)
            cr.line_to(split, 0)
            if i+1 in hl_splits:
                cr.set_source_rgb(0,0,0)
            else:
                cr.set_source_rgb(0.7,0.7,0.7)
            cr.set_line_width(0.1)
            cr.stroke()

        cr.move_to(0, 0)
        cr.line_to(0.5, 1)
        cr.line_to(self.length-0.5, 1)
        cr.line_to(self.length, 0)
        cr.set_source_rgb(0,0,0)
        cr.set_line_width(0.1)
        cr.stroke()

    def _make_var(self, name, value):
        if len(value) == 1:
            v = Jump.shared_var(name)
            self.model[v] = Jump(value[0])
            return Jumps([v])
        else:
            v = Jumps.shared_var(name)
            self.model[v] = Jumps(value)
            return v

    def split_raw(self, n):
        if n not in self.splits: return None
        i = self.splits.index(n)+1
        del n

        index = 0
        split1 = 0
        for part in self.jumps.subsequences:
            split2 = split1 + self.model[part.number].value()
            if i < split2: break
            index += 1
            split1 = split2
        assert split1 < split2

        if i == split1:
            jumps0 = Jumps.concat(*self.jumps.parts[:index])
            jumps1 = Jumps.concat(*self.jumps.parts[index:])
        else:
            part = self.jumps.parts[index]
            assert isinstance(part, Jumps)
            assert part.is_var
            part_val = self.model[part].value()
            part0 = self._make_var(part.var_name+'0', part_val[:i-split1])
            part1 = self._make_var(part.var_name+'1', part_val[i-split1:])
            self.env.ctx.add_fact(equals(part0 + part1, part))
            jumps0 = self.jumps.parts[:index] + (part0,)
            jumps1 = (part1,) + self.jumps.parts[index+1:]
            jumps0 = Jumps.concat(*jumps0)
            jumps1 = Jumps.concat(*jumps1)

        print('Split:', self.jumps)
        print('Left:', jumps0)
        print('Right:', jumps1)
        print()
        return GJumps(self.env, self.model, jumps0), GJumps(self.env, self.model, jumps1)

    def join_raw(self, other):
        print('Left:', self.jumps)
        print('Right:', other.jumps)
        res = GJumps(self.env, self.model, self.jumps + other.jumps)
        print('Join:', res.jumps)
        print()
        return res

class GMines(Splittable):
    def __init__(self, env, model, mines, layer = 0):
        self.layer = layer

        self.env = env
        self.model = model
        self.mines = mines
        self.mines_val = model[mines].value()

        self.length = model[mines.length].value()

        self.raw_bounding_box = BoundingBox(0,-1,-0.5,self.length-0.5)
        super().__init__()

    def draw_raw(self, cr, layer):
        if layer != self.layer: return

        hl_splits = set()
        last = 0
        for part in self.mines.subsequences:
            last += self.model[part.length].value()
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

    def _make_var(self, name, value):
        if len(value) == 1:
            v = TermBool.shared_var(name)
            self.model[v] = TermBool(value[0])
            return MineField(v)
        else:
            v = MineField.shared_var(name)
            self.model[v] = MineField(value)
            return v

    def split_raw(self, n):
        if not (1 <= n < self.length): return None
        index = 0
        split1 = 0
        for part in self.mines.subsequences:
            split2 = split1 + self.model[part.length].value()
            if n < split2: break
            index += 1
            split1 = split2

        assert split1 < split2
        print(split1, n, split2)
        print(split1, n, split1 == n)
        print(type(split1), type(n), split1 == n)
        if n == split1:
            print('case A')
            mines0 = MineField.concat(*self.mines.parts[:index])
            mines1 = MineField.concat(*self.mines.parts[index:])
        else:
            print('case B')
            part = self.mines.parts[index]
            assert isinstance(part, MineField)
            assert part.is_var
            part_val = self.model[part].value()
            part0 = self._make_var(part.var_name+'0', part_val[:n-split1])
            part1 = self._make_var(part.var_name+'1', part_val[n-split1:])
            self.env.ctx.add_fact(equals(part0 + part1, part))
            mines0 = self.mines.parts[:index] + (part0,)
            mines1 = (part1,) + self.mines.parts[index+1:]
            mines0 = MineField.concat(*mines0)
            mines1 = MineField.concat(*mines1)
        print('Split:', self.mines)
        print('Left:', mines0)
        print('Right:', mines1)
        print()
        return GMines(self.env, self.model, mines0), GMines(self.env, self.model, mines1)

    def join_raw(self, other):
        print('Left:', self.mines)
        print('Right:', other.mines)
        res = GMines(self.env, self.model, self.mines + other.mines)
        print('Join:', res.mines)
        return res

class Model:
    def __init__(self, base_dict):
        self.subst = Substitution(base_dict)
    def __getitem__(self, key):
        return self.subst[key]
    def __setitem__(self, key, value):
        base_dict = dict(self.subst.base_dict)
        base_dict[key] = value
        self.subst = Substitution(base_dict)

class GrasshopperGui(Gtk.Window):

    def __init__(self, win_size = (800, 600)):
        super().__init__()

        self.env = GrasshopperEnv()
        jumps = self.env.order_jumps(self.env.jumps)
        mines = self.env.mines
        self.model = Model({
            jumps : Jumps([1,2,4]),
            mines : MineField([0,0,1,0,1,0]),
        })

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
            GJumps(self.env, self.model, jumps),
            GMines(self.env, self.model, mines),
        ]
        self.objects[0].translate(-1,0)

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

    def grasp_objects(self, objs, x,y):
        self.obj_grasp = []
        for obj in objs:
            cx,cy = obj.center
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
                if select_box.contains(*obj.center):
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
                obj.center = (math.floor(x-gx+0.5), math.floor(y-gy+0.5))
            self.darea.queue_draw()

    def on_key_press(self,w,e):
        keyval = e.keyval
        keyval_name = Gdk.keyval_name(keyval)
        # do not distinguish standard and numlock key variants
        keyval_name = remove_prefix(keyval_name, "KP_")
        # print("Press:", keyval_name)
        if keyval_name == "Escape":
            Gtk.main_quit()
        # elif keyval_name == "Left":
        #     self.inf_index = max(self.inf_index-1, 0)
        #     self.darea.queue_draw()
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

if __name__ == "__main__":

    win = GrasshopperGui()
    Gtk.main()
