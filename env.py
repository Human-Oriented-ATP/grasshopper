from logic import *

class Model:
    def __init__(self, base_dict):
        self.subst = Substitution(base_dict)
    def __getitem__(self, key):
        return self.subst[key]
    def __setitem__(self, key, value):
        base_dict = dict(self.subst.base_dict)
        base_dict[key] = value
        self.subst = Substitution(base_dict)

class GrasshopperEnv:
    def __init__(self):
        self.constraints = []

        self.jumps = Jumps.fixed_var('jumps')
        self.mines = MineField.fixed_var('mines')
        self.model = Model({
            self.jumps : Jumps([1,2,4]),
            self.mines : MineField([0,0,1,0,1,0]),
        })
        self.add_constraint(equals(self.mines.length, self.jumps.length))

    def add_constraint(self, constraint):
        self.constraints.append(constraint)
