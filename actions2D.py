from ast import literal_eval
import itertools
import math 
from SumOfNorms2D import sum_of_norms

# Core transformation/ordering utilities for BFS proof-state expansion.
# Each state is a sum of paired norms; functions below either transform states
# (Holder/product/expand/embed) or compare/prune them via regularity frontiers.

def is_stronger(x, y):
	# Compare two (regularity, Lebesgue exponent) pairs under the model's
	# partial order. Returns True if x can absorb y.

	it_is = False
	
	ks = [x[0], y[0]]; ps = [x[1], y[1]]
	l = max(ks); k = min(ks)
	imax = ks.index(l); imin = ks.index(k)
	q = ps[imax]; p = ps[imin]
	
	if k == l: q = max(ps); p = min(ps)
	
	if l > k:
		if x[0] == l: it_is = True
		
	else:
		if x[1] == q and y[1] < q: it_is = True
		
	#exceptions
	if l == k + 1 and p >= 2 and q < 2*p/(p + 2): it_is = False
	if l == k + 1 and p == math.inf and q <= 2: it_is = False
	if l == k + 2 and p == math.inf and abs(q - 1.0) < 1e-15: it_is = False
	
	
	
	return it_is
	
def stronger_or_equal(x, y):
	# Helper relation used in set-dominance checks.
	return x == y or is_stronger(x, y)

def dominates_any(frontier_a, frontier_b):
	# Aggressive mode: any stronger comparison is enough.
	if frontier_a == [] or frontier_b == []:
		return False
	for a in frontier_a:
		for b in frontier_b:
			if stronger_or_equal(a, b):
				return True
	return False

def dominates(frontier_a, frontier_b):
	# frontier_a dominates frontier_b only if every point in frontier_b
	# is matched by a stronger-or-equal point in frontier_a
	if frontier_a == [] or frontier_b == []:
		return False
	for b in frontier_b:
		if not any(stronger_or_equal(a, b) for a in frontier_a):
			return False
	return True
		

def HolderExponent(p, q):

	'''
	Returns the Hölder exponent of q w.r.t. p, i.e. a real number q', satisfying 1/q + 1/q' = 1/p.
	'''
	
	if abs(q - p) < 1e-15: qprime = math.inf
	elif q == math.inf: qprime = p
	else: qprime = q*p/(q - p)
	
	if p == math.inf: q = math.inf; qprime = math.inf
	
	return q, qprime


def expand(norms, r, s):

	'''
	Expands the Sobolev norm to the sum of the respective seminorms.

	Input:

	norms: list of norms in the form [[(funcs1, order1, sobolev1, lebesgue1), (funcs2, order2, sobolev2, lebesgue2)], ...]
		corresponding to \sum_{j=1}^N \|( u_j^{(iu_j)} v_j^{(iv_j)} )^{(m_j)}\|_{W^{k_j,p_j}}\|( w_j^{(iw_j)} z_j^{(iz_j)} )^{(n_j)}\|_{W^{l_j,q_j}}
	r: index of the norm in the sum to be expanded (which j from the sum above do we choose)
	s: index of the term in the product to be expanded (which norm in the product above do we choose, 0 for the first and 1 for the second)

	e.g., r = 1, s = 0 corrsponds to \|( u_1^{(iu_1)} v_1^{(iv_1)} )^{(m_1)}\|_{W^{k_1,p_1}}

	Output: new list of norms with the expanded norm in seminorms

	'''
	
	if len(norms) <= r:
		print("Index exceeds number of sum terms")
		return
		
	if s > 1: 
		print("Index exceeds number of product terms")
		return

	# Determine the other function in the product
	oth = 0
	if s == 0: oth = 1
	
	#Get the individual data of the norm to be expanded
	subnorms = norms[r]
	funcs = subnorms[s][0]; deriv = subnorms[s][1]; sobolev = subnorms[s][2]; lebesgue = subnorms[s][3]
	funcs1 = subnorms[oth][0]; deriv1 = subnorms[oth][1]; sobolev1 = subnorms[oth][2]; lebesgue1 = subnorms[oth][3]
	
	if funcs == "('1', (0, 0))*('1', (0, 0))": return norms
	
	expansion = []
	
	if s == 0:
		for i in range(sobolev + 1):
			for j in range(sobolev - i + 1):
				#expand the first norm
				expansion.append([(funcs, (i + deriv[0], j + deriv[1]), 0, lebesgue), (funcs1, deriv1, sobolev1, lebesgue1)]) 
	else:
		for i in range(sobolev + 1):
			for j in range(sobolev - i + 1):
				#expand the second norm
				expansion.append([(funcs1, deriv1, sobolev1, lebesgue1), (funcs, (i + deriv[0], j + deriv[1]), 0, lebesgue)]) 
		
	newnorms = norms[0:r] + expansion + norms[r+1:len(norms)]
		
		
	return newnorms





def prod(norms, r, s):

	'''
	Applies the Leibiniz product rule to the derivative of a product of two functions.

	Input: same as expand()

	Output: new list of norms with the expanded norm in products of derivatives
	'''
	
	if len(norms) <= r:
		print("Index exceeds number of sum terms")
		return
		
	if s > 1: 
		print("Index exceeds number of product terms")
		return
		
	oth = 0
	if s == 0: oth = 1
	
	subnorms = norms[r]
	funcs = subnorms[s][0]; deriv = subnorms[s][1]; sobolev = subnorms[s][2]; lebesgue = subnorms[s][3]
	funcs1 = subnorms[oth][0]; deriv1 = subnorms[oth][1]; sobolev1 = subnorms[oth][2]; lebesgue1 = subnorms[oth][3]
	
	if funcs == "('1', (0, 0))*('1', (0, 0))": return norms
	
	splits = funcs.split("*")
	leibiniz = []
	
	#Straightforward: just change the data according to the Leibiniz rule
	if s == 0:
		for i in range(deriv[0] + 1):
			for j in range(deriv[1] + 1):
				FuncData1 = literal_eval(splits[0]); FuncData2 = literal_eval(splits[1])
				neword1 = (FuncData1[1][0] + deriv[0] - i, FuncData1[1][1] + deriv[1] - j)
				neword2 = (FuncData2[1][0] + i, FuncData2[1][1] + j)

				funcs_new = "('{data1}', {n1})*('{data2}', {n2})".format(data1 = FuncData1[0], 
																 		data2 = FuncData2[0],
																 		n1 = neword1,
																 		n2 = neword2)
															
				leibiniz.append([(funcs_new, (0, 0), sobolev, lebesgue), (funcs1, deriv1, sobolev1, lebesgue1)])
			
	else:
		for i in range(deriv[0] + 1):
			for j in range(deriv[1] + 1):
				FuncData1 = literal_eval(splits[0]); FuncData2 = literal_eval(splits[1])
				neword1 = (FuncData1[1][0] + deriv[0] - i, FuncData1[1][1] + deriv[1] - j)
				neword2 = (FuncData2[1][0] + i, FuncData2[1][1] + j)

				funcs_new = "('{data1}', {n1})*('{data2}', {n2})".format(data1 = FuncData1[0], 
																 		data2 = FuncData2[0],
																 		n1 = neword1,
																 		n2 = neword2)
															
				leibiniz.append([(funcs1, deriv1, sobolev1, lebesgue1), (funcs_new, (0, 0), sobolev, lebesgue)])
			
	newnorms = norms[0:r] + leibiniz + norms[r+1:len(norms)]

	return newnorms
	



	
def embed(norms, r, s):

	'''
	Applies the Rellich-Kondrachov embedding theorem.

	Input: same as expand()

	Output: new list of norms with the embedded norm replacing the (r,s) component
	'''
	
	if len(norms) <= r:
		print("Index exceeds number of sum terms")
		return
		
	if s > 1: 
		print("Index exceeds number of product terms")
		return
		
	oth = 0
	if s == 0: oth = 1
	
	subnorms = norms[r]
	funcs = subnorms[s][0]; order = subnorms[s][1]; sobolev = subnorms[s][2]; lebesgue = subnorms[s][3]
	funcs1 = subnorms[oth][0]; order1 = subnorms[oth][1]; sobolev1 = subnorms[oth][2]; lebesgue1 = subnorms[oth][3]
	
	if funcs == "('1', (0, 0))*('1', (0, 0))": return norms
	
	#New exponents after embedding
	pstar = 1
	if lebesgue >= 2: pstar = 2*lebesgue/(lebesgue + 2)
	if lebesgue == math.inf: pstar = 2.01
	kstar = sobolev + 1
	
	embedded = [(funcs, order, kstar, pstar), (funcs1, order1, sobolev1, lebesgue1)]
	if s == 1: embedded = [(funcs1, order1, sobolev1, lebesgue1), (funcs, order, kstar, pstar)]
	
	return norms[0:r] + [embedded] + norms[r+1:len(norms)]
	




def BoundByNorm(norms):

	
	#Bounds the Sobolev seminorm by the Sobolev norm. 
	
	normnew = []
	for subnorms in norms:
			
		funcs = subnorms[0][0]; order = subnorms[0][1]; sobolev = subnorms[0][2]; lebesgue = subnorms[0][3]
		funcs1 = subnorms[1][0]; order1 = subnorms[1][1]; sobolev1 = subnorms[1][2]; lebesgue1 = subnorms[1][3]
		
		bounded = [(funcs, (0, 0), sobolev + order[0] + order[1], lebesgue),
					(funcs1, (0, 0), sobolev1 + order1[0] + order1[1], lebesgue1)]
					
		normnew.append(bounded)
	
	return normnew




def Holder(norms, r, s, q):

	'''
	Applies Hölder's inequality to a norm of a product.

	Input: 

	norms: as in expand()
	r: as in expand()
	s: 0 if applying w.r.t. first function in the product, 1 for the second
	q: desired Lebesgue exponent after applying Hölder's inequality

	Output: new list of norms with the Hölder-split norm replacing the r-component
	'''
	
	if len(norms) <= r:
		print("Index exceeds number of sum terms")
		return norms
	
	subnorm = norms[r][0]
	funcs = subnorm[0]; order = subnorm[1]; sobolev = subnorm[2]; lebesgue = subnorm[3]

	splits = funcs.split("*") #split the product
	FuncData1 = literal_eval(splits[0]); FuncData2 = literal_eval(splits[1]) #get the name of the function
	ord1 = FuncData1[1]; ord2 = FuncData2[1] #get the derivative orders of the functions in the product

	if s == 0: q, qprime = HolderExponent(lebesgue, q) #if s == 0, compute the Hölder exponents w.r.t. the first function
	else: qprime, q = HolderExponent(lebesgue, q) #else w.r.t. the second function

	funcs_new1 = "('{data}', (0, 0))*('1', (0, 0))".format(data = FuncData1[0])
	funcs_new2 = "('{data}', (0, 0))*('1', (0, 0))".format(data = FuncData2[0])
	splitted = [(funcs_new1, ord1, 0, qprime), (funcs_new2, ord2, 0, q)]

	

	return norms[0:r] + [splitted] + norms[r+1:len(norms)] 
	
	

def absorb_weaker(norms):

	'''
	Absorbs the weaker norms by the stronger ones.

	Input: list of norms in the usual form 
	Output: simplified list of norms in the same form
	'''

	#Sort and group the norms by their functions and derivative orders, 
	#so that we can compare only those with same functions and derivative orders
	sortnorm = sorted(norms, key = lambda x: (x[0][0], x[0][1], x[1][0], x[1][1])) 

	#Group the norms with the same functions and derivative orders
	groups = [list(g) for _, g in itertools.groupby(sortnorm, key=lambda x: (x[0][0], x[0][1], x[1][0], x[1][1]))]
	
	#Get the functions and derivative orders for each group
	funcs1 = [group[0][0][0] for group in groups]; funcs2 = [group[0][1][0] for group in groups]
	order1 = [group[0][0][1] for group in groups]; order2 = [group[0][1][1] for group in groups]
	
	left_stronger = []; right_stronger = [] #lists to hold the strongest norms in each group
	for group in groups:
		
		#Get the Sobolev and Lebesgue exponents for the left and right norms in the group (corresp. to u and v)
		left_exps = [(sbgrp[0][2], sbgrp[0][3]) for sbgrp in group]
		right_exps = [(sbgrp[1][2], sbgrp[1][3]) for sbgrp in group]
		
		left_flags = len(left_exps)*[False]
		right_flags = len(right_exps)*[False]
		
		leftnew = []; rightnew = []
		
		for i in range(len(left_exps)):
			for j in range(len(left_exps)):
				if is_stronger(left_exps[i], left_exps[j]): left_flags[j] = True
					
					
		for i in range(len(right_exps)):
			for j in range(len(right_exps)):
				if is_stronger(right_exps[i], right_exps[j]): right_flags[j] = True
					
		for i in range(len(left_exps)):
			if not left_flags[i]: leftnew.append(left_exps[i])
		
		for i in range(len(right_exps)):
			if not right_flags[i]: rightnew.append(right_exps[i])
			
		left_exps = leftnew; right_exps = rightnew
		
		#The last element in the sorted list is the strongest norm of each group
		left_stronger.append(left_exps)
		right_stronger.append(right_exps)
		
	leftnew = []; rightnew = []
	
	for left in left_stronger: leftnew.append(list(set(left)))
	for right in right_stronger: rightnew.append(list(set(right)))
	
	left_stronger = leftnew; right_stronger = rightnew
	del(leftnew); del(rightnew)
	
	#Construct the new list of norms with only the strongest norms in each group
	leftnorms = [[(funcs1[i], order1[i], left_stronger[i][j][0], left_stronger[i][j][1]) \
				 for j in range(len(left_stronger[i]))] for i in range(len(groups))]
				 
	rightnorms = [[(funcs2[i], order2[i], right_stronger[i][j][0], right_stronger[i][j][1]) \
				 for j in range(len(right_stronger[i]))] for i in range(len(groups))]
	
	return [[leftnorms[i][j], rightnorms[i][k]] \
			for i in range(len(groups)) \
			for j in range(len(leftnorms[i])) \
			for k in range(len(rightnorms[i]))]
	



def sortHolder(norms):

	'''
	Split the list of norms into those where Hölder's inequality has been applied and those where it has not.
	'''

	splitted = []; nonsplitted = []

	for subnorm in norms: #for all norms in the sum
		funcs0 = subnorm[0][0]; order0 = subnorm[0][1]; sobolev0 = subnorm[0][2]; lebesgue0 = subnorm[0][3]
		funcs1 = subnorm[1][0]; order1 = subnorm[1][1]; sobolev1 = subnorm[1][2]; lebesgue1 = subnorm[1][3]
		
		splits = funcs0.split("*")
		FuncData1 = literal_eval(splits[0]); FuncData2 = literal_eval(splits[1])
		
		if FuncData2[0] == '1': #if Hölder's inequality has been applied
			splitted.append(subnorm) #add to splitted list
		else: nonsplitted.append(subnorm) #else to nonsplitted list
		
	
	return splitted, nonsplitted


def GetMaxReg(norms):

	'''
	Calculating the maximum regularity of the state.

	Input:

	norms: list of norms in the form [[(funcs1, order1, sobolev1, lebesgue1), (funcs2, order2, sobolev2, lebesgue2)], ...]

	Output:	

	KHnew: list of tuples that are either stronger than or incomparable to any Holder-spliited term in the original sum, w.r.t. u
	LHnew: list of tuples that are either stronger than or incomparable to any Holder-spliited term in the original sum, w.r.t. v
	Knew: list of tuples that are either stronger than or incomparable to any nonspliited term in the original sum, w.r.t. u
	Lnew: list of tuples that are either stronger than or incomparable to any nonspliited term in the original sum, w.r.t. v
	'''

	splitted, nonsplitted = sortHolder(norms) #split the norms into those with Hölder's inequality applied and those without
	
	#Get the highest regularity and Lebesgue exponents for the splitted norms
	#KH = sorted([(norm[0][1] + norm[0][2], norm[0][3]) for norm in splitted], key = lambda x: (x[0], x[1])) 
	KH = [(norm[0][1][0] + norm[0][1][1] + norm[0][2], norm[0][3]) for norm in splitted]
	KHflags = len(KH)*[False]; KHnew = []

	#Same for the non-splitted norms
	#LH = sorted([(norm[1][1] + norm[1][2], norm[1][3]) for norm in splitted], key = lambda x: (x[0], x[1]))
	LH = [(norm[1][1][0] + norm[1][1][1] + norm[1][2], norm[1][3]) for norm in splitted]
	LHflags = len(LH)*[False]; LHnew = []
	
	#k1 = 0; l1 = 0; p1 = 0; q1 = 0
	
	#if len(splitted) != 0: #if there are splitted norms
		#KP1 = KH[-1]; k1 = KP1[0]; p1 = KP1[1] #get the highest regularity and Lebesgue exponent
		#LQ1 = LH[-1]; l1 = LQ1[0]; q1 = LQ1[1] #same for the second function
	
	K = []; L = []
	for norm in nonsplitted: #for all non-splitted norms
		funcs = norm[0][0]; order = norm[0][1]; sobolev = norm[0][2]; lebesgue = norm[0][3]
		
		splits = funcs.split("*")
		FuncData1 = literal_eval(splits[0]); FuncData2 = literal_eval(splits[1])
		orderux = FuncData1[1][0]; orderuy = FuncData1[1][1]
		ordervx = FuncData2[1][0]; ordervy = FuncData2[1][1] #as usual, get the derivative orders of u and v in the product
		
		K.append((orderux + orderuy + order[0] + order[1] + sobolev, lebesgue)) #all possible regularities and Lebesgue exponents for u
		L.append((ordervx + ordervy + order[0] + order[1] + sobolev, lebesgue)) #same for v
		
	Kflags = len(K)*[False]; Lflags = len(L)*[False]; Knew = []; Lnew = []
	
	for i in range(len(KH)):
		for j in range(len(KH)):
			if is_stronger(KH[i], KH[j]): KHflags[j] = True
			
	for i in range(len(LH)):
		for j in range(len(LH)):
			if is_stronger(LH[i], LH[j]): LHflags[j] = True
			
	for i in range(len(K)):
		for j in range(len(K)):
			if is_stronger(K[i], K[j]): Kflags[j] = True
			
	for i in range(len(L)):
		for j in range(len(L)):
			if is_stronger(L[i], L[j]): Lflags[j] = True
				
	for i in range(len(KH)):
		if not KHflags[i]: KHnew.append(KH[i])
		
	for i in range(len(LH)):
		if not LHflags[i]: LHnew.append(LH[i])
		
	for i in range(len(K)):
		if not Kflags[i]: Knew.append(K[i])
		
	for i in range(len(L)):
		if not Lflags[i]: Lnew.append(L[i])
		
	Knew = list(set(Knew)); Lnew = list(set(Lnew))
	KHnew = list(set(KHnew)); LHnew = list(set(LHnew))
	
	
	#k2 = 0; l2 = 0; p2 = 0; q2 = 0
	#K = sorted(K, key = lambda x: (x[0], x[1])); L = sorted(L, key = lambda x: (x[0], x[1])) #sort them to get the strongest

	#if len(nonsplitted) != 0: #if there are non-splitted norms, get the strongest
	#	KP2 = K[-1]; k2 = KP2[0]; p2 = KP2[1]
	#	LQ2 = L[-1]; l2 = LQ2[0]; q2 = LQ2[1]
	
	

	return KHnew, LHnew, Knew, Lnew


def CheckRegularity(norms, kmax, pmax, lmax, qmax):

	'''
	Checks whether the norms have reached maximal regularity.

	Input:

	norms: list of norms in the form [[(funcs1, order1, sobolev1, lebesgue1), (funcs2, order2, sobolev2, lebesgue2)], ...]
	kmax: maximal regularity for the first function
	lmax: maximal regularity for the second function

	Output:	

	MakeLeafReg: boolean indicating whether maximal regularity has been reached (so it will be turned to a leaf in the tree)	
	MakeLeafHolder: boolean indicating whether all terms are Holder-splitted (i.e., if it is a terminal state)	
	KHmax: list of tuples that are either stronger than or incomparable to any Holder-spliited term in the original sum, w.r.t. u
	LHmax: list of tuples that are either stronger than or incomparable to any Holder-spliited term in the original sum, w.r.t. v
	Kmax: list of tuples that are either stronger than or incomparable to any nonspliited term in the original sum, w.r.t. u
	Lmax: list of tuples that are either stronger than or incomparable to any nonspliited term in the original sum, w.r.t. v
	'''

	MakeLeafReg = False; MakeLeafHolder = False
	splitted, nonsplitted = sortHolder(norms) #split the norms into those with Hölder's inequality applied and those without
	if nonsplitted == []: MakeLeafHolder = True #if all norms are splitted, mark for leaf
	
	KHmax, LHmax, Kmax, Lmax = GetMaxReg(norms)

	#if maximal regularity has been reached in either function, 
	#or all are splitted by Hölder's inequality, then turn to leaf
	for kp in KHmax:
		if MakeLeafReg: break
		if is_stronger(kp, (kmax, pmax)): MakeLeafReg = True
		
	for kp in Kmax:
		if MakeLeafReg: break
		if is_stronger(kp, (kmax, pmax)): MakeLeafReg = True
		
	for lq in LHmax:
		if MakeLeafReg: break
		if is_stronger(lq, (lmax, qmax)): MakeLeafReg = True
		
	for lq in Lmax:
		if MakeLeafReg: break
		if is_stronger(lq, (lmax, qmax)): MakeLeafReg = True
	
	
	return MakeLeafReg, MakeLeafHolder, KHmax, LHmax, Kmax, Lmax
	
	
def compare(K1, L1, K2, L2, mode = "safe"):
	# Compare two frontier pairs (u-side and v-side) according to selected mode.
	# safe: full set-dominance, aggressive/existential: any dominating point.
	if mode in ("existential", "aggressive"):
		u_low = dominates_any(K1, K2)
		v_low = dominates_any(L1, L2)
	else:
		u_low = dominates(K1, K2)
		v_low = dominates(L1, L2)
	return u_low, v_low


def eliminate(norms):

	'''
	Eliminates identical norms from the list.
	'''

	norms.sort()
	norms = list(norms for norms,_ in itertools.groupby(norms))
	return norms

	
	

	
if __name__ == "__main__":

	
	#Testing / sanity checks for all primitive actions and comparison helpers.
	
	print("Testing the actions:")
	print(" ")
	
	
	#_______________________Expansion__________________________________________________
	
	norms = [[("('u', (0, 0))*('v', (0, 0))", (2, 0), 3, 2), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (0, 1))*('v', (0, 0))", (1, 3), 2, 1), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0), ("('w', (0, 0))*('z', (0, 0))", (1, 0), 1, 1)]]
	
	print("Original:", sum_of_norms(norms))
	print(" ")
	
	print("Expansion:", sum_of_norms(expand(norms, 0, 0)))
	print(" ")
	
	
	
	#_______________________Leibiniz rule______________________________________________
	
	norms = [[("('u', (0, 0))*('v', (0, 0))", (2, 0), 3, 2), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (0, 1))*('v', (0, 0))", (1, 3), 2, 1), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0), ("('w', (0, 0))*('z', (0, 0))", (1, 0), 1, 1)]]
	         
	print("Original:", sum_of_norms(norms))
	print(" ")
	         
	print("Leibiniz:", sum_of_norms(prod(norms, 1, 0)))
	print(" ")
	
	
	#_______________________Rellich-Kondrachov_________________________________________
	
	norms = [[("('u', (0, 0))*('v', (0, 0))", (0, 0), 0, 9), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (1, 0))*('v', (0, 0))", (3, 0), 2, 8), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0), ("('w', (0, 0))*('z', (0, 0))", (1, 0), 1, math.inf)]]
	
	print("Original:", sum_of_norms(norms))
	print(" ")
	
	print("Embedding:", sum_of_norms(embed(norms, 2, 1)))
	print(" ")
	
	
	
	#_______________________Bounded seminorms by norms__________________________________
	
	norms = [[("('u', (0, 0))*('v', (0, 0))", (0, 0), 0, math.inf), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (0, 0))*('v', (0, 0))", (0, 0), 2, 1), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (0, 0))*('1', (0, 0))", (1, 0), 0, 3), ("('v', (0, 0))*('1', (0, 0))", (0, 0), 1, 2)],
	         [("('u', (0, 0))*('1', (0, 0))", (1, 3), 0, 4), ("('v', (0, 0))*('1', (0, 0))", (1, 1), 0, 2)],
	         [("('u', (0, 0))*('1', (0, 0))", (1, 0), 1, 1.1), ("('v', (0, 0))*('1', (0, 0))", (0, 0), 2, 2)],
	         [("('u', (0, 0))*('v', (0, 0))", (0, 0), 0, 2), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (0, 0))*('1', (0, 0))", (1, 3), 1, 7/6), ("('v', (0, 0))*('1', (0, 0))", (1, 1), 0, 3)]]
	
	print("Original:", sum_of_norms(norms))
	print(" ")
	
	print("Back to norm:", sum_of_norms(BoundByNorm(norms)))
	print(" ")
	
	
	
	#_______________________Hölder's inequality________________________________________
	
	norms = [[("('u', (1, 0))*('v', (0, 0))", (0, 0), 0, 2), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (0, 1))*('v', (0, 0))", (0, 0), 0, math.inf), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0), ("('w', (4, 0))*('z', (0, 3))", (0, 0), 0, 1)]]
	
	print("Original:", sum_of_norms(norms))
	print(" ")
	
	print("Hölder:", sum_of_norms(Holder(norms, 0, 1, 6)))
	print(" ")
	
	
	
	#_______________________eliminate same terms_______________________________________
	
	norms = [[("('u', (1, 0))*('v', (0, 0))", (0, 0), 0, 2), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (1, 0))*('v', (0, 0))", (0, 0), 0, 2), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0), ("('w', (0, 0))*('z', (0, 0))", (0, 0), 0, 1)],
	         [("('u', (1, 0))*('v', (0, 0))", (0, 0), 0, 2), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)]]
	
	print("Original:", sum_of_norms(norms))
	print(" ")
	
	print("eliminated:", sum_of_norms(eliminate(norms)))
	print(" ")

	
	
	
	#_______________________eliminate weaker terms_____________________________________
	
	norms = [[("('u', (0, 0))*('v', (0, 0))", (0, 0), 0, math.inf), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (0, 0))*('v', (0, 0))", (0, 0), 2, 1), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (0, 0))*('1', (0, 0))", (1, 0), 0, 3), ("('v', (0, 0))*('1', (0, 0))", (0, 0), 1, 2)],
	         [("('u', (0, 0))*('1', (0, 0))", (1, 3), 0, 4), ("('v', (0, 0))*('1', (0, 0))", (1, 1), 0, 2)],
	         [("('u', (0, 0))*('1', (0, 0))", (1, 0), 1, 1.1), ("('v', (0, 0))*('1', (0, 0))", (0, 0), 2, 2)],
	         [("('u', (0, 0))*('v', (0, 0))", (0, 0), 0, 2), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (0, 0))*('1', (0, 0))", (1, 3), 1, 7/6), ("('v', (0, 0))*('1', (0, 0))", (1, 1), 0, 3)]]
	
	print("Original:", sum_of_norms(norms))
	print(" ")
	
	print("Simplified:", sum_of_norms(absorb_weaker(norms)))
	print(" ")
	
	
	
	#_______________________sort by Holder_____________________________________________
	
	norms = [[("('u', (0, 0))*('v', (0, 0))", (0, 0), 0, math.inf), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (0, 0))*('v', (0, 0))", (0, 0), 2, 1), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (0, 0))*('1', (0, 0))", (1, 0), 0, 3), ("('v', (0, 0))*('1', (0, 0))", (0, 0), 1, 2)],
	         [("('u', (0, 0))*('1', (0, 0))", (1, 3), 0, 4), ("('v', (0, 0))*('1', (0, 0))", (1, 1), 0, 2)],
	         [("('u', (0, 0))*('1', (0, 0))", (1, 0), 1, 1.1), ("('v', (0, 0))*('1', (0, 0))", (0, 0), 2, 2)],
	         [("('u', (0, 0))*('v', (0, 0))", (0, 0), 0, 2), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (0, 0))*('1', (0, 0))", (1, 3), 1, 7/6), ("('v', (0, 0))*('1', (0, 0))", (1, 1), 0, 3)]]
	
	print("Original:", sum_of_norms(norms))
	print(" ")
	
	splitted, nonsplitted = sortHolder(norms)
	print("Splitted by Hölder:", sum_of_norms(splitted))
	print("Non-splitted by Hölder:", sum_of_norms(nonsplitted))
	print(" ")
	
	
	
	#_______________________Get max reg._______________________________________________
	
	norms = [[("('u', (0, 0))*('v', (0, 0))", (0, 0), 0, math.inf), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (0, 0))*('v', (0, 0))", (0, 0), 2, 1), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (0, 0))*('1', (0, 0))", (1, 0), 0, 3), ("('v', (0, 0))*('1', (0, 0))", (0, 0), 1, 2)],
	         [("('u', (0, 0))*('1', (0, 0))", (1, 3), 0, 4), ("('v', (0, 0))*('1', (0, 0))", (1, 1), 0, 2)],
	         [("('u', (0, 0))*('1', (0, 0))", (1, 0), 1, 1.1), ("('v', (0, 0))*('1', (0, 0))", (0, 0), 2, 2)],
	         [("('u', (0, 0))*('v', (0, 0))", (0, 0), 0, 2), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (0, 0))*('1', (0, 0))", (1, 3), 1, 7/6), ("('v', (0, 0))*('1', (0, 0))", (1, 1), 0, 3)],
	         [("('u', (0, 0))*('v', (1, 1))", (1, 0), 0, 1), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)]]
	
	print("Original:", sum_of_norms(norms))
	print(" ")
	
	KH, LH, K, L = GetMaxReg(norms)
	
	print("Maximum reguarity -- Holdered w.r.t. u:", KH)
	print("Maximum reguarity -- Holdered w.r.t. v:", LH)
	print("Maximum reguarity -- non-Holdered w.r.t. u:", K)
	print("Maximum reguarity -- non-Holdered w.r.t. v:", L)
	print(" ")
	
	
	
	
	#_______________________check regularity___________________________________________
	
	norms = [[("('u', (0, 0))*('v', (0, 0))", (0, 0), 0, math.inf), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (0, 0))*('v', (0, 0))", (0, 0), 2, 1), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (0, 0))*('1', (0, 0))", (1, 0), 0, 3), ("('v', (0, 0))*('1', (0, 0))", (0, 0), 1, 2)],
	         [("('u', (0, 0))*('1', (0, 0))", (1, 3), 0, 4), ("('v', (0, 0))*('1', (0, 0))", (1, 1), 0, 2)],
	         [("('u', (0, 0))*('1', (0, 0))", (1, 0), 1, 1.1), ("('v', (0, 0))*('1', (0, 0))", (0, 0), 2, 2)],
	         [("('u', (0, 0))*('v', (0, 0))", (0, 0), 0, 2), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)],
	         [("('u', (0, 0))*('1', (0, 0))", (1, 3), 1, 7/6), ("('v', (0, 0))*('1', (0, 0))", (1, 1), 0, 3)],
	         [("('u', (0, 0))*('v', (1, 1))", (1, 0), 0, 1), ("('1', (0, 0))*('1', (0, 0))", (0, 0), 0, 0)]]
	         
	pmax = 12; qmax = 4; kmax = 4; lmax = 3
	
	print("Original:", sum_of_norms(norms))
	print(" ")
	
	print("Regularity checked:", CheckRegularity(norms, kmax, pmax, lmax, qmax))
	print(" ")
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	

		
