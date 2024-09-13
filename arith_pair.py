
class ArithPair:
    def __init__(self, x,y):
        self.x = x
        self.y = y
    def __iter__(self):
        return iter((self.x, self.y))
    def __add__(self, other):
        return ArithPair(self.x + other.x, self.y + other.y)
    def __sub__(self, other):
        return ArithPair(self.x - other.x, self.y - other.y)
    def __neg__(self, other):
        return ArithPair(self.x - other.x, self.y - other.y)
    def __hash__(self):
        return (self.x, self.y)
    def __eq__(self, other):
        return self.x == other.x and self.y == other.y
    def __mul__(self, c):
        return ArithPair(self.x*c, self.y*c)
    def __truediv__(self, c):
        return ArithPair(self.x/c, self.y/c)
    def value(self):
        return ArithPair(self.x.value(), self.y.value())
    def map(self, f):
        return ArithPair(f(self.x), f(self.y))
    def y_flip(self):
        return ArithPair(self.x, -self.y)
    def x_shift(self, x):
        return ArithPair(self.x+x, self.y)
    def __str__(self):
        return f"ArithPair({self.x}, {self.y})"
