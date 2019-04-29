import networkx as nx

af = nx.DiGraph()
af.add_edges_from([('a','b'),('b','c'),('c','a')])
list(af.edges)

for i in af.nodes:
    af.nodes[i]['labelling'] = 'in'

def is_in(af, argument):
    for (attacker,_) in af.in_edges(argument):
        if af.nodes[attacker]['labelling'] != 'out':
            return False
    return True

def is_out(af, argument):
    for (attacker,_) in af.in_edges(argument):
        if af.nodes[attacker]['labelling'] == 'in':
            return True
    return False

def is_undec(af, argument):
    for (attacker,_) in af.in_edges(argument):
        if af.nodes[attacker]['labelling'] == 'in':
            return False
        if af.nodes[attacker]['labelling'] != 'out':
            return True
    return False

#labelling the set
def powerset(base_set):
    from itertools import chain, combinations
    base_list = list(base_set)
    combo_list = [ combinations(base_list, r) for r in range(len(base_set)+1)]

    powerset = set([])
    for ll in combo_list:
        list_of_frozensets = list(map(frozenset,map(list,ll)))
        set_of_frozensets = set(list_of_frozensets)
        powerset = powerset.union(set_of_frozensets)
    return powerset

def generateLabelling(args):
    output = []
    for ina in powerset(args):
        for outa in powerset(args-ina):
            output.append([ina,outa,(args-ina)-outa])
    return output

def extension(args):
    output = []
    for [ina, outa, undeca] in generateLabelling(args):
        i = 0
        for x in ina:
            af.nodes[x]['labelling'] = 'in'
        for x in outa:
            af.nodes[x]['labelling'] = 'out'
        for x in undeca:
            af.nodes[x]['labelling'] = 'undec'
        for x in ina:
            if is_in(af,x) == False:
                i = 1
                break
        if i == 1:
            continue
        for x in outa:
            if is_out(af,x) == False:
                i = 1
                break
        if i == 1:
            continue
        for x in undeca:
            if is_undec(af,x) == False:
                i = 1
                break
        if i == 0:
            output.append([ina,outa,undeca])
    return output

output = extension(af.nodes)
for i in output:
    print(i)

class Rule:
    def __init__(self, name, premises, conclusion, defeasible):
        self.name = name
        self.premises = set(premises)
        self.conclusion = set(conclusion)
        self.defeasible = defeasible
    def applicable(self, kb):
        return self.premises.issubset(kb)

class Argument:
    def __init__(self, name, subarguments,toprule):
        self.name = name
        subarguments.add(self)
        self.subarguments = subarguments
        self.toprule=toprule

def all_arguments(args):
    kb = set()
    arguments = set()
    kbLen = 0
    args0 = set()
    while 1:
        for rule in args.difference(args0):
            subarguments = set()
            if rule.premises.issubset(kb):
                for argument in arguments:
                    if argument.toprule.conclusion.issubset(rule.premises):
                        subarguments.add(argument)
                arguments.add(Argument(('A'+str(len(arguments))),subarguments,rule))
                kb = kb.union(rule.conclusion)
                kb.add(rule.name)
                args0.add(rule)
        if kbLen == len(arguments):
            break
        kbLen = len(arguments)
    return arguments

def to_af(args):
    af = nx.DiGraph()
    for argument in args:
        af.add_node(argument)
    for argument in af.nodes:
       for argumentB in af.nodes:
           for subargu in argumentB.subarguments:
               if argument.toprule.conclusion == ('!'+str(subargu.toprule.name)) and subargu.toprule.defeasible == 1:af.add_edge(argument,argumentB)
               for subconclu in subargu.toprule.conclusion:
                   for conclu in argument.toprule.conclusion:
                       if conclu == ('!'+str(subconclu)) or subconclu == ('!'+str(conclu)):
                           af.add_edge(argument,argumentB)
    return af


r1 = Rule('r1',[],['a'],0)
r2 = Rule('r2',[],['b'],0)
r3 = Rule('r3',['a','b'],['c'],0)
r4 = Rule('r4',['c'],['e'],1)
r5 = Rule('r5',[],['!e'],1)
rules = {r1,r2,r3,r4,r5}

arguments = all_arguments(rules)
for i in arguments:
    subarguments = set()
    for j in i.subarguments:
        subarguments.add(j.name)
    print(i.name,' subargu: ',subarguments,' toprule: ',i.toprule.name)

af1 = to_af(arguments)
for argu in af1:
    for [attacker,_] in af1.in_edges(argu):
        print(argu.name,' attacked by ',attacker.name)



