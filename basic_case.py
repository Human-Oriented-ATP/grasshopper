import itertools

num_jumps = 3
jumps = ['x'+str(i+1) for i in range(num_jumps)]
mines = set()

class JumpOrder:
    def __init__(self, order):
        self.order = tuple(order)
        cur_pos = set()
        self.mid_landings = []
        for x in order[:-1]:
            cur_pos.add(x)
            self.mid_landings.append(frozenset(cur_pos))
    def __str__(self):
        res = ['0']
        for j,l in zip(self.order, self.mid_landings):
            res.append(f'-{j}->')
            pos = '+'.join(sorted(l))
            if l in mines: pos = '('+pos+')'
            else: pos = ' '+pos+' '
            res.append(pos)
        res.append(f'-{self.order[-1]}->')
        res.append('+'.join(sorted(jumps)))
        return '  '.join(res)

orders = [
    JumpOrder(order)
    for order in itertools.permutations(jumps)
]
mines.add(frozenset(['x1']))
mines.add(frozenset(['x1','x2']))
mines.add(frozenset(['x1','x2']))
for order in orders:
    print(order)
