from itertools import product
import pprint

def fix_multichar_symbs(transitions):#assigns stand-in symbol for diacritics
	symbols = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'
	trans_dict = {}
	new_transitions = []
	i=0
	for x in transitions:
		if len(x[1]) > 1:
			if x[1] in trans_dict.keys():
				new_transition = x[:1] + (trans_dict[x[1]],) + x[2:]
			else:
				trans_dict[x[1]] = symbols[i]
				new_transition = x[:1] + (symbols[i],) + x[2:]
			new_transitions.append(new_transition)
			i += 1
		else:
			new_transitions.append(x)
	return new_transitions
	
def states_and_labels(transitions):#pulls set of states and transition labels from a list of transitions
	state_set = []
	label_set = []
	for transition in transitions:
		if transition[0] not in state_set:
			state_set.append(transition[0])
		if transition[1] not in label_set:
			label_set.append(transition[1])
		if transition[2] not in state_set:
			state_set.append(transition[2])
	return state_set, label_set
	
def merge_labels(transitions):#merges transition labels that have the same state actions (often all consonants, all vowels, etc.)
	glossary = {}
	transitions = [x for x in transitions if not x[1] in ['+','.','<','-']]
	new_transitions = []
	label_dict = {}
	states, labels = states_and_labels(transitions)
	no_boundaries = [x for x in labels if x not in ['#','%']]
	for label in labels:
		if label in no_boundaries:
			if label not in label_dict.keys():
				label_dict[label] = set()
			for x in transitions:
				if x[1] == label:
					label_dict[label].add((x[0],x[2],int(x[4])))
		else:
			for x in transitions:
				if x[1] == label:
					new_transitions.append((x[0],x[1],x[2],int(x[4])))
	clean_dict = {}
	for label in label_dict.keys():
		if label_dict[label] not in clean_dict.values():
			clean_dict[label] = label_dict[label]
			glossary[label] = []
		else:
			existing_label = find_key(clean_dict,label_dict[label])
			glossary[existing_label].append(label)
	#pprint.pprint(glossary)
	for key in clean_dict.keys():
		for val in clean_dict[key]:
			new_transitions.append((val[0],key,val[1],val[2]))
	return new_transitions
	
def clean_transitions(transitions):
	return fix_multichar_symbs(merge_labels(transitions))
	
def populate_dict(transitions):
	transitions = clean_transitions(transitions)
	mydict = {}
	for transition in transitions:
		if not transition[0] in mydict:
			mydict[transition[0]] = {}
		if not transition[2] in mydict:
			mydict[transition[2]] = {}
		mydict[transition[0]][transition[1]] = transition[2:]
	return mydict
	
def behaviors(symb, states, transition_dict):#computes behaviors for a particular alphabet symbol
	bll = []
	blr = []
	for state in states:
		if symb in transition_dict[state].keys():
			if transition_dict[state][symb][1] == 1:
				blr.append((state, transition_dict[state][symb][0]))
			elif transition_dict[state][symb][1] == -1:
				bll.append((state, transition_dict[state][symb][0]))
			else:
				print('mistake!!!' + str(transition_dict[state][symb]))
	brl = bll
	brr = blr
	return str(symb), sorted(bll), sorted(blr), sorted(brl), sorted(brr)

def trans_step(relation):
	new_relation = relation
	for ((x,y),(z,w)) in product(relation,relation):
		if y == z:
			if (x,w) not in new_relation:
				new_relation.append((x,w))
	return sorted(new_relation)
	
def refl_closure(relation):
	new_relation = relation
	states, labels = states_and_labels(transitions)
	for x in states:
		new_relation.append((x,x))
	return new_relation
	
def refl_trans_closure(relation):#computes the reflexive-transitive closure for a relation
	step = 0
	step_plus = relation
	while not step == step_plus:
		step = trans_step(step_plus)
		step_plus = trans_step(step)
	step_plus = refl_closure(step_plus)
	seen = set()
	new_relation = [x for x in step_plus if not (x in seen or seen.add(x))]
	return new_relation

def compose(rel1, rel2):#relation composition
	new_rel = []
	for x,y in rel1:
		for u,v in rel2:
			if y==u:
				new_rel.append((x,v))
	seen = set()
	new_rel = [x for x in new_rel if not (x in seen or seen.add(x))]
	return new_rel
	
def bll_compose(u_behaviors, v_behaviors):#left-left behavior composition
	name, u_bll, u_blr, u_brl, u_brr = u_behaviors
	name, v_bll, v_blr, v_brl, v_brr = v_behaviors
	
	mid_part = refl_trans_closure(compose(v_bll, u_brr))
	lefter = u_blr
	left = compose(lefter, mid_part)
	right = compose(left, v_bll)
	righter = u_bll + compose(right, u_brl)
	seen = set()
	final = [x for x in righter if not (x in seen or seen.add(x))]
	return sorted(final)

def blr_compose(u_behaviors, v_behaviors):#left-right behavior composition
	name, u_bll, u_blr, u_brl, u_brr = u_behaviors
	name, v_bll, v_blr, v_brl, v_brr = v_behaviors
	
	mid_part = refl_trans_closure(compose(v_bll,u_brr))
	left = compose(u_blr,mid_part)
	right = compose(left, v_blr)
	seen = set()
	final = [x for x in right if not (x in seen or seen.add(x))]
	return sorted(final)	
	
def brl_compose(u_behaviors, v_behaviors):#right-left behavior composition
	name, u_bll, u_blr, u_brl, u_brr = u_behaviors
	name, v_bll, v_blr, v_brl, v_brr = v_behaviors
	
	mid_part = refl_trans_closure(compose(u_brr,v_bll))
	left = compose(v_brl, mid_part)
	right = compose(left, u_brl)
	seen = set()
	final = [x for x in right if not (x in seen or seen.add(x))]
	return sorted(final)
	
def brr_compose(u_behaviors, v_behaviors):#right-right behavior composition
	name, u_bll, u_blr, u_brl, u_brr = u_behaviors
	name, v_bll, v_blr, v_brl, v_brr = v_behaviors
	
	mid_part = refl_trans_closure(compose(u_brr,v_bll))
	left = v_brl
	lefter = compose(left, mid_part)
	right = compose(lefter, u_brr)
	righter = v_brr + compose(right, v_blr)
	seen = set()
	final = [x for x in righter if not (x in seen or seen.add(x))]
	return sorted(final)
	
def bh_composition(bh1, bh2):#composes LL,LR,RL,RR components for two distinct tuples of behaviors
	return bh1[0] + bh2[0], bll_compose(bh1, bh2),blr_compose(bh1, bh2),brl_compose(bh1, bh2),brr_compose(bh1, bh2)

def check_if_in(element, elem_set):
	behaviors = [x[1:] for x in elem_set]
	elem_behaviors = element[1:]
	if elem_behaviors not in behaviors:
		return True

def elem_close_step(elem_set):
	product_set = product(elem_set,elem_set)
	for x,y in product_set:
		comp = bh_composition(x,y)
		if check_if_in(comp, elem_set):
			elem_set.append(comp)
	return elem_set

def elem_closure(elem_set):#closes a set of elements under behavior composition
	step = 0
	step_plus = elem_close_step(elem_set)
	while not step == step_plus:
		step = elem_close_step(step_plus)
		step_plus = elem_close_step(step)
		if step == step_plus:
			break
	return step_plus

def semigroup_dict(elem_set):
	semigroup_dict = {}
	for elem in elem_set:
		semigroup_dict[elem[0]] = elem[1:]
	return semigroup_dict

def nameless_compose(elem1, elem2):#composes two tuples of behaviors without a label
	elem1 = ('',) + elem1
	elem2 = ('',) + elem2
	name, bll, blr, brl, brr = bh_composition(elem1, elem2)
	return bll, blr, brl, brr
	
def resize(string, n):#resizes a string for use in constructing multiplication table
	if string == None:
		return '?' + ' '*(n-1)
	elif len(string) < n:
		string = string + ' '*(n-len(string))
	return string
	
def find_key(mydict, val):
	return next((k for k, v in mydict.items() if v == val), None)  

def cayley_table(semigroup_dict):#constructs multiplication table from a semigroup
	n = max([len(x) for x in semigroup_dict.keys()])
	lines = []
	header = '#'*n +' |' + ' | '.join([resize(x, n) for x in semigroup_dict.keys()])
	lines.append(header)
	for key in semigroup_dict:
		composition_list = [nameless_compose(semigroup_dict[key], y) for y in semigroup_dict.values()]
		row = resize(key, n) + ' |' + ' | '.join([resize(find_key(semigroup_dict, x), n) for x in composition_list])
		lines.append(row)
	return '\n'.join(lines)

def is_idempotent(elem, elem_sd):#checks whether an element of the semigroup is idempotent
	if elem_sd[elem] == nameless_compose(elem_sd[elem], elem_sd[elem]):
		return 1
	else:
		return 0	

def does_aLb(elem1,elem2,elem_sd):#checks if Green's L relation holds between two elements
	s1a = {elem1}
	s1b = {elem2}
	for key in elem_sd.keys():
		s1a_xy = nameless_compose(elem_sd[key],elem_sd[elem1])
		s1a.add(find_key(elem_sd,s1a_xy))
		s1b_xy = nameless_compose(elem_sd[key],elem_sd[elem2])
		s1b.add(find_key(elem_sd,s1b_xy))
	if s1a == s1b:
		return True
		
def does_aRb(elem1,elem2,elem_sd):#checks if Green's R relation holds between two elements
	as1 = {elem1}
	bs1 = {elem2}
	for key in elem_sd.keys():
		as1_xy = nameless_compose(elem_sd[elem1],elem_sd[key])
		as1.add(find_key(elem_sd,as1_xy))
		bs1_xy = nameless_compose(elem_sd[elem2],elem_sd[key])
		bs1.add(find_key(elem_sd,bs1_xy))
	if as1 == bs1:
		return True

def does_aJb(elem1,elem2,elem_sd):#checks if Green's J relation holds between two elements
	sas = {elem1}
	sbs = {elem2}
	for x,y in product(elem_sd.keys(),elem_sd.keys()):
		sas_xy = nameless_compose(nameless_compose(elem_sd[x],elem_sd[elem1]),elem_sd[y])
		sas.add(find_key(elem_sd,sas_xy))
		sbs_xy = nameless_compose(nameless_compose(elem_sd[x],elem_sd[elem2]),elem_sd[y])
		sbs.add(find_key(elem_sd,sbs_xy))
	if sas == sbs:
		return True

def is_DA(elem_sd):#checks whether a semigroup is in DA
	idempotents = []
	for elem in elem_sd.keys():
		if is_idempotent(elem, elem_sd):
			idempotents.append(elem_sd[elem])
	check = 1
	for x, y, z in product(elem_sd.keys(),elem_sd.keys(),elem_sd.keys()):
		xyz = nameless_compose(elem_sd[x],nameless_compose(elem_sd[y],elem_sd[z]))
		xyzw = 0
		while xyzw not in idempotents:
			xyzw = nameless_compose(xyz,xyz)
			xyz = xyzw
		if not nameless_compose(xyzw,nameless_compose(elem_sd[y],xyzw)) == xyzw:
			check = 0
			break
	if check == 1:
		return 'Is DA'
	else:
		return 'Not DA'
		
def is_Def(elem_sd):#checks whether a semigroup is Definite
	idempotents = []
	check = 1
	for elem in elem_sd.keys():
		if is_idempotent(elem, elem_sd):
			idempotents.append(elem)
	for idem in idempotents:
		composition_list = [nameless_compose(y, elem_sd[idem]) for y in elem_sd.values()]
		for x in composition_list:
			if not x == elem_sd[idem]:
				check = 0
				break
	if check == 1:
		return 'Is Definite'
	if check == 0:
		return 'Not Definite'
		
def is_RDef(elem_sd):#checks whether a semigroup is Reverse Definite
	check = 1
	for key in elem_sd.keys():
		if is_idempotent(key, elem_sd):
			composition_list = [nameless_compose(elem_sd[key],y) for y in elem_sd.values()]
			for x in composition_list:
				if not x == elem_sd[key]:
					check = 0
					break
	if check == 1:
		return 'Is Reverse Definite'
	if check == 0:
		return 'Not Reverse Definite'
		
def is_Rtriv(elem_sd):#checks whether a semigroup is R-trivial
	check = 1
	for elem1, elem2 in product(elem_sd.keys(),elem_sd.keys()):
		if does_aRb(elem1,elem2,elem_sd):
			if not elem1 == elem2:
				check = 0
				break
	if check == 1:
		return 'Is R-trivial'
	if check == 0:
		return 'Not R-trivial'
		
def is_Ltriv(elem_sd):#checks whether a semigroup is L-trivial
	check = 1
	for elem1, elem2 in product(elem_sd.keys(),elem_sd.keys()):
		if does_aLb(elem1,elem2,elem_sd):
			if not elem1 == elem2:
				check = 0
				break
	if check == 1:
		return 'Is L-trivial'
	if check == 0:
		return 'Not L-trivial'
		
def is_L1(elem_sd):#checks whether a semigroup is Generalized Definite
	check = 1
	idempotents = []
	for elem in elem_sd.keys():
		if is_idempotent(elem, elem_sd):
			idempotents.append(elem_sd[elem])
	for x,y in product(elem_sd.values(),elem_sd.values()):
		for idem in idempotents:
			if not nameless_compose(idem,nameless_compose(x,idem)) == idem:
				check = 0
				break
	if check == 1:
		return 'Is L1'
	if check == 0:
		return 'Not L1'
		
def is_LJ1(elem_sd):#checks whether a semigroup is Locally Testable
	check = 1
	idempotents = set()
	for elem in elem_sd.keys():
		if is_idempotent(elem, elem_sd):
			idempotents.add(elem)
	for idem in idempotents:
		for x,y in product(elem_sd.values(),elem_sd.values()):
			if not nameless_compose(elem_sd[idem],nameless_compose(x,nameless_compose(elem_sd[idem],nameless_compose(y,elem_sd[idem])))) == nameless_compose(elem_sd[idem],nameless_compose(y,nameless_compose(elem_sd[idem],nameless_compose(x,elem_sd[idem])))):
				check = 0
				break
	if check == 1:
		return 'Is LJ1'
	if check == 0:
		return 'Not LJ1'
		
def is_Trivial(elem_sd):#checks whether a semigroup is Trivial
	if len(elem_sd) == 1:
		return 'Is Trivial'
	else:
		return 'Not Trivial'
		
def main():
	elem_set = []
	transition_dict = populate_dict(transitions)
	states, labels = states_and_labels(clean_transitions(transitions))
	no_boundaries = [x for x in labels if x not in ['#','%']]
	for label in no_boundaries:
		elem_set.append(behaviors(label, states, transition_dict))
	#pprint.pprint(elem_set)
	elem_sd = semigroup_dict(elem_closure(elem_set))
	
	DA = is_DA(elem_sd)
	LJ1 = is_LJ1(elem_sd)
	L1 = is_L1(elem_sd)
	Ltriv = is_Ltriv(elem_sd)
	Rtriv = is_Rtriv(elem_sd)
	Def = is_Def(elem_sd)
	RDef = is_RDef(elem_sd)
	Trivial = is_Trivial(elem_sd)
	
	print(cayley_table(elem_sd))
	print(DA)
	print(LJ1)
	print(L1)
	print(Def)
	print(RDef)
	print(Trivial)

	pprint.pprint(elem_sd)
	print('\n')
	return DA, LJ1, L1, Def, RDef, Trivial
