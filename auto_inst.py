from logic import equals, TermBool, TermInt, conjunction, disjunction, Substitution
import itertools

class MatchTerm:
    def __init__(self, terms):
        self.terms = terms
        assert len(self.terms) > 0
    def matches(self, ground_terms):
        return self._match_rec(ground_terms, 0, Substitution({}))
    def _match_rec(self, ground_terms, i, subst0):
        if i == len(self.terms):
            yield subst0
        else:
            term = self.terms[i]
            for ground_term in ground_terms:
                subst1 = self._match1(term, subst0[ground_term])
                if subst1 is not None:
                    yield from self._match_rec(ground_terms, i+1, subst1)
    @staticmethod
    def _match1(template, ground):
        stack = [(template, ground)]
        res = dict()
        while stack:
            a,b = stack.pop()
            if a == b: continue
            if type(a) != type(b): return None
            if a.is_free_var:
                b2 = res.setdefault(a,b)
                if b != b2: return None
            elif a.f == TermInt._mk:
                for x, coef in zip(a.summands, a.muls):
                    if x.is_free_var:
                        if abs(coef) == 1 and x.is_free_var:
                            value = (b - a)*coef + x
                        if x in res: return None
                        if any(v.is_free_var for v in value.all_vars): return None
                        res[x] = value
                        break
                else:
                    return None
            elif a.is_var or b.is_var:
                return None
            elif a.f != b.f or len(a.args) != len(b.args):
                return None
            else:
                stack.extend(zip(a.args, b.args))
        res = Substitution(res)
        if res[template] != ground:
            print("Template:", template)
            print("Ground term:", ground)
            print("substitution:")
            for key,value in res.base_dict.items():
                print('  ', key, '->', value)
            raise Exception("Error in matching calculation")
        return res

class AbstractAutoInstance:
    def __init__(self, generic, matches):
        self.generic = generic
        self.matches = matches
    def get_instances(self, ground_terms):
        for m in self.matches:
            for subst in m.matches(ground_terms):
                yield subst[self.generic]

class AutoInstance(AbstractAutoInstance):
    def __init__(self, generic):
        free_vars = set(x for x in generic.all_vars if x.is_free_var)
        matches = []
        for leaf in generic.leaf_iter(self._is_leaf):
            if free_vars <= leaf.all_vars:
                matches.append(MatchTerm([leaf]))
        if not matches:
            raise Exception(f"Didn't find a single atom covering all free variables: {generic}")
        super().__init__(generic, matches)

    @staticmethod
    def _is_leaf(term):
        if term.f in (conjunction, disjunction, TermBool.invert, TermInt.le, TermInt._mk):
            return False
        elif term.f == equals:
            return not isinstance(term.args[0], (TermBool, TermInt))
        else:
            return True

if __name__ == "__main__":
    from logic import Jump
    thm = AutoInstance(Jump.X.length > 0)
    jump = Jump.fixed_var("jump")
    terms = [jump.length]
    print(thm.matches[0].terms[0])
    print("Instances:")
    for x in thm.get_instances(terms):
        print(x)
