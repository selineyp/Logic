import re
import itertools
import copy


def extractAtoms(theorem):
    # get signature
    atoms = set()
    t = theorem.replace('(', '')
    t = t.replace(')', '')
    t = t.replace('|', '')
    t = t.replace('>', '')
    t = t.replace(',', '')
    t = re.sub(r"\s+", "", t, flags=re.UNICODE)
    for char in t:
        atoms.add(char)
    return atoms


class Prover:
    def __init__(self, theorem: str):
        self.thm = theorem
        self.target = theorem.split('|')[1].strip()
        self.atoms = extractAtoms(theorem)
        self.derivation = []
        self.addAssumptions()
        mp = self.modusponens()
        # apply MP as much as possible
        while len(mp) > 0:
            for m in mp:
                self.derivation.append(m)
                mp = self.modusponens()

    def breakdown(self, s):
        # accumulate formulas from s
        if '>' not in s:
            return None, None
        if '(' == s[0]:
            opencnt = 1
            closedcnt = 0
            for idx, x in enumerate(s[1:]):
                if x == '(':
                    opencnt += 1
                elif x == ')':
                    closedcnt += 1
                if opencnt == closedcnt:
                    fass = s[0:idx+2]
                    break
        else:
            # accumulate assumptions
            f = re.findall('^(.*) > \(.*\)$', s)
            if len(f) > 0:
                fass = f[0][0]
            else:
                f = re.findall('^(.*) > .*$', s)
                fass = f[0][0]
        
        # parse targets
        if '{} > ('.format(fass) in s:
            target = s.replace('{} > ('.format(fass), '')
            target = target[:-1]
        else:
            target = s.replace('{} > '.format(fass), '')

        if '(' == fass[0]:
            fass = fass[1:-1]
        if '(' == target[0] and ')' == target[-1]:
            target = target[:-1]

        return fass, target

    def deductionthm(self):
        # parse formulas on lhs and rhs of derivation sign
        fass, target = self.breakdown(self.target)
        if fass is not None:
            # update theorem to be proven
            if len(self.assumptions) > 0:
                self.thm = '{},{} | {}'.format(','.join(self.assumptions), fass, target)
            else:
                self.thm = '{} | {}'.format(fass, target)
            self.addAssumptions()
            self.target = target
            return True
        return False

    def setDerivation(self, derivation):
        self.derivation = derivation

    def addAssumptions(self):
        self.assumptions = set()
        lhs = self.thm.split('|')[0]
        if len(lhs) == 0:
            return
        for idx, l in enumerate(lhs.split(',')):
            self.assumptions.add(l.strip())
            self.derivation.append(('Assumption {}'.format(idx), l.strip()))

    def modusponens(self):
        # apply modus ponens
        mp = set()
        # find all possible combinations where modus ponens can be applied
        for i, j in itertools.product(range(len(self.derivation)), repeat=2):
            if i != j:
                if '(' in self.derivation[j][1].strip():
                    rl = self.derivation[j][1].replace('(', '\(')
                    rl = rl.replace(')', '\)')
                    res = re.findall('^\({}\) > (.*)$'.format(rl), self.derivation[i][1])
                elif '(' not in self.derivation[j][1].strip() and '(' in self.derivation[i][1]:
                    res = re.findall('^{} > (.*)$'.format(self.derivation[j][1]), self.derivation[i][1])
                elif '(' not in self.derivation[i][1]:
                    res = re.findall('^{} > (.*)$'.format(self.derivation[j][1]), self.derivation[i][1])

                if len(res) > 0:
                    m = res[0]
                    if m[0] == '(' and m[-1] == ')':
                        # strip parantheses
                        m = m[1:-1]
                    ex = False
                    # check if this MP is already in the current derivation
                    # avoid repeating
                    for d in self.derivation:
                        if d[0] == 'MP {},{}'.format(i, j) or d[1] == m:
                            ex = True
                    if not ex:
                        mp.add(('MP {},{}'.format(i, j), m))

        return mp

    def generateFormulas(self, i: int):
        # generate formulas of max len i
        res = set()
        if i == 1:
            for atom in self.atoms:
                res.add(atom)
            return res
        # generate formulas of total len i
        for k in range(1, i):
            lenk = self.generateFormulas(k)
            lenik = self.generateFormulas(i-k)
            for fk in lenk:
                for fik in lenik:
                    # combine formulas of len k and i-k with implication
                    res.add('({} > {})'.format(fk, fik))
        return res

    def istargetAssumption(self):
        # check if target is a part of assumptions
        for a in self.assumptions:
            if a == self.target:
                return True
        return False

    def instanceH1(self, i: int):
        # F > (G > F)
        h1 = set()
        formulas = set()

        for j in range(1, i+1):
            formulas = formulas.union(self.generateFormulas(j))

        # apply H1
        if len(self.assumptions) == 0 and len(self.derivation) < 1:
            for (a1, a2) in itertools.product(formulas, repeat=2):
                h1.add(('H1', '{} > ({} > {})'.format(a1, a2, a1)))

        # iterate over possible formulas
        for a2 in formulas:
            if len(self.derivation) > 0:
                last = self.derivation[-1][1]
                if len(last) == 1:    
                    h = '{} > ({} > {})'.format(last, a2, last)
                else:
                    h = '({}) > ({} > ({}))'.format(last, a2, last)
                h1.add(('H1', h))

        if len(self.derivation) > 0:
            last = self.derivation[-1][1]
            # find possible applications
            lhs = re.findall('^\((.*) > \((.*) > (.*)\)\) > .*$', last)
            if len(lhs) > 0 and len(lhs[0]) == 3:
                if lhs[0][0] == lhs[0][2]:
                    h1.add(('H1', '{} > ({} > {})'.format(lhs[0][0], lhs[0][1], lhs[0][2])))
        return h1

    def instanceH2(self, i: int, prev: bool = False):
        # (F > (G > H)) > ((F > G) > (F > H))
        h2 = set()
        formulas = set()

        for j in range(1, i+1):
            formulas = formulas.union(self.generateFormulas(j))
        
        # apply H2 on generated formulas 
        if len(self.assumptions) == 0 and len(self.derivation) < 1:
            for (a1, a2, a3) in itertools.product(formulas, repeat=3):
                h2.add(('H2', '({} > ({} > {})) > (({} > {}) > ({} > {}))'.format(a1, a2, a3, a1, a2, a1, a3)))

        if len(self.derivation) > 0:
            last = self.derivation[-1][1]
            # find possible applications
            trip = re.findall('^(.*) > \((.*) > (.*)\)$', last)
            if len(trip) > 0:
                if len(trip[0]) == 3:
                    f = trip[0][0]
                    g = trip[0][1]
                    h = trip[0][2]
                    hax = '({} > ({} > {})) > (({} > {}) > ({} > {}))'.format(f, g, h, f, g, f, h)
                    h2.add(('H2', hax))
        return h2

    def instanceH3(self, i: int):
        # ((F > -) > -) > F
        h3 = set()
        formulas = set()
        for j in range(1, i+1):
            formulas = formulas.union(self.generateFormulas(j))
       
        # apply H3 on generated formulas 
        for a1 in formulas:
            h3.add(('H3', '(({} > -) > -) > {}'.format(a1, a1)))
        return h3

    def check(self):
        # check if target is in derivation
        if len(self.derivation) > 0:
            if self.derivation[-1][1].strip() == self.target.strip():
                return True
        return False


def step(thm, i, d):
    # depth is zero, in this case check if target is already in assumptions
    if d == 0:
        pr = Prover(thm)
        # stop if target is reached
        if pr.target == pr.derivation[-1][1] or pr.istargetAssumption():
            return pr.derivation
        h1 = pr.instanceH1(i)
        h2 = pr.instanceH2(i)
        h3 = pr.instanceH3(i)
        # create a pool of candidate axioms that can be applied
        pool = h1.union(h2).union(h3)
        # iterate over candidate derivaton steps
        for p in pool:
            prver = Prover(thm)
            pp = copy.copy(pr.derivation)
            pp.append(p)
            prver.setDerivation(pp)
            # apply mp
            mp = prver.modusponens()
            # add new derivations to cache
            if len(mp) > 0:
                pp.append(list(mp)[0])
                cache[0].append(pp)
            else:
                cache[0].append(pp)
        return

    # read cache
    if d > 0:
        prev = cache[d-1]

    # read candidates of prev
    for cand in prev:
        pr = Prover(thm)
        # return is target is found
        if cand[-1][1] == pr.target:
            return cand
        # set new derivation and get axioms
        pr.setDerivation(cand)
        # generate formulas and apply H1,H2,H3
        h1 = pr.instanceH1(i)
        h2 = pr.instanceH2(i)
        h3 = pr.instanceH3(i)
        pool = h1.union(h2).union(h3)
        # cache possibilities 
        if d == 0:
            for p in pool:
                cache[0].append(p)
            return
        # consider possible axioms to add
        for p in pool:
            pv = Prover(pr.thm)
            nextder = copy.copy(pr.derivation)
            nextder.append(p)
            pv.setDerivation(nextder)
            # apply MP
            mp = pv.modusponens()
            if len(mp) > 0:
                nextder.append(list(mp)[0])
                cache[d].append(nextder)
                pv.setDerivation(nextder)
                # if target is derived, return
                if pv.check():
                    return pv.derivation
            # if target is derived, return
            elif pv.check():
                return pv.derivation

cache = {}


def search(thm):
    pv = Prover(thm)
    # apply deduction thm as much as possible
    r = pv.deductionthm()
    while r is True:
        r = pv.deductionthm()
    dt = pv.thm
    if pv.thm != thm:
        # target is changed by deduction theorem
        print('Using deduction theorem and proving {}'.format(pv.thm))
    else:
        print('Deduction theorem not applicable')
    # for max length of formulas
    for max_len in range(1, 2):
        # for certain proof length(in this case, it is number of modus ponens applied)
        for depth in range(0, 2):
            # cache previous depths
            cache[depth] = []
            # try to find a derivation with max_len and with depth
            der = step(dt, max_len, depth)
            if der is not None:
                #if step returns a derivation, return it
                return der
            # if only way to extend dervation is to apply H1 (inventing new formulas)
            if depth > 0 and all([el[-2][0] == 'H1' for el in cache[depth]]) and all([el[-2][0] == 'H1' for el in cache[depth-1]]):
                print('No derivation found.')
                return False

if __name__ == '__main__':
    thm = input('Please write the theorem. (use | for derivation sign, > for implication and - for bottom) \n')
    der = search(thm)
    if der is not False:
        print('Derivation steps')
        for i, el in enumerate(der):
            print(i, el[1], '......', el[0])
