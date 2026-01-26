from ast import literal_eval
import itertools
import math 



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
	
	if funcs == "('1', 0)*('1', 0)": return norms
	
	expansion = []
	
	if s == 0:
		for j in range(sobolev + 1):
			expansion.append([(funcs, j + deriv, 0, lebesgue), (funcs1, deriv1, sobolev1, lebesgue1)])
	else:
		for j in range(sobolev + 1):
			expansion.append([(funcs1, deriv1, sobolev1, lebesgue1), (funcs, j + deriv, 0, lebesgue)])
		
	newnorms = norms[0:r] + expansion + norms[r+1:len(norms)]
		
		
	return newnorms





def prod(norms, r, s):

	'''
	Applies the Leibiniz product rule to the derivative of a product of two functions.
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
	
	if funcs == "('1', 0)*('1', 0)": return norms
	
	splits = funcs.split("*")
	leibiniz = []
	
	if s == 0:
		for i in range(deriv + 1):
			FuncData1 = literal_eval(splits[0]); FuncData2 = literal_eval(splits[1])
			neword1 = FuncData1[1] + deriv - i
			neword2 = FuncData2[1] + i
		
			funcs_new = "('{data1}', {n1})*('{data2}', {n2})".format(data1 = FuncData1[0], 
																 	data2 = FuncData2[0],
																 	n1 = neword1,
																 	n2 = neword2)
															
			leibiniz.append([(funcs_new, 0, sobolev, lebesgue), (funcs1, deriv1, sobolev1, lebesgue1)])
			
	else:
		for i in range(deriv + 1):
			FuncData1 = literal_eval(splits[0]); FuncData2 = literal_eval(splits[1])
			neword1 = FuncData1[1] + deriv - i
			neword2 = FuncData2[1] + i
		
			funcs_new = "('{data1}', {n1})*('{data2}', {n2})".format(data1 = FuncData1[0], 
																 	data2 = FuncData2[0],
																 	n1 = neword1,
																 	n2 = neword2)
															
			leibiniz.append([(funcs1, deriv1, sobolev1, lebesgue1), (funcs_new, 0, sobolev, lebesgue)])
			
	newnorms = norms[0:r] + leibiniz + norms[r+1:len(norms)]

	return newnorms
	



	
def embed(norms, r, s):

	'''
	Applies the Rellich-Kondrachov embedding theorem.
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
	
	if funcs == "('1', 0)*('1', 0)": return norms
	
	pstar = lebesgue/(lebesgue + 1)
	if lebesgue == math.inf: pstar = 1
	if pstar < 1: pstar = 1
	kstar = sobolev + 1
	
	embedded = [(funcs, order, kstar, pstar), (funcs1, order1, sobolev1, lebesgue1)]
	if s == 1: embedded = [(funcs1, order1, sobolev1, lebesgue1), (funcs, order, kstar, pstar)]
	
	return norms[0:r] + [embedded] + norms[r+1:len(norms)]
	




def BoundByNorm(norms, r, s):

	'''
	Bounds the Sobolev seminorm by the Sobolev norm.
	'''
	
	if len(norms) <= r:
		print("Index exceeds number of sum terms")
		return norms
		
	if s > 1: 
		print("Index exceeds number of product terms")
		return norms
		
	oth = 0
	if s == 0: oth = 1
	
	subnorms = norms[r]
	funcs = subnorms[s][0]; order = subnorms[s][1]; sobolev = subnorms[s][2]; lebesgue = subnorms[s][3]
	funcs1 = subnorms[oth][0]; order1 = subnorms[oth][1]; sobolev1 = subnorms[oth][2]; lebesgue1 = subnorms[oth][3]
	
	bounded = [(funcs, 0, sobolev + order, lebesgue), (funcs1, order1, sobolev1, lebesgue1)]
	if s == 1: bounded = [(funcs1, order1, sobolev1, lebesgue1), (funcs, 0, sobolev + order, lebesgue)]
	
	return norms[0:r] + [bounded] + norms[r+1:len(norms)] 
	



def Holder(norms, r, q):

	'''
	Applies Hölder's inequality to a norm of a product.
	'''
	
	if len(norms) <= r:
		print("Index exceeds number of sum terms")
		return norms
	
	subnorms = norms[r]
	
	if subnorms[1] != ("('1', 0)*('1', 0)", 0, 0, 0) \
	and subnorms[0] == ("('1', 0)*('1', 0)", 0, 0, 0): 
		temp_sn = [subnorms[0]]
		subnorms = [subnorms[1], temp_sn[0]]
		
		norms = norms[0:r] + [subnorms] + norms[r+1:len(norms)]
		
	funcs = subnorms[0][0]; order = subnorms[0][1]; sobolev = subnorms[0][2]; lebesgue = subnorms[0][3]
	funcs1 = subnorms[1][0]; order1 = subnorms[1][1]; sobolev1 = subnorms[1][2]; lebesgue1 = subnorms[1][3]
	
	if order + sobolev != 0:
		print(order, sobolev)
		print("Input is not ready for Hölder's inequality!") 
		print (subnorms); input()
		return norms
		
		
	splits = funcs.split("*")
	FuncData1 = literal_eval(splits[0]); FuncData2 = literal_eval(splits[1])
	ord1 = FuncData1[1]; ord2 = FuncData2[1]
	
	if FuncData2[0] == '1': # or subnorms[1] != ("('1', 0)*('1', 0)", 0, 0, 0):
		
		order = ord1
		funcsnew = "('{data}', 0)*('1', 0)".format(data = FuncData1[0])
		subnorms = [(funcsnew, order, sobolev, lebesgue), (funcs1, order1, sobolev1, lebesgue1)]
		
		print("Hölder's inequality has already been applied; please check for validity.")
		print(subnorms); input()
		return norms[0:r] + [subnorms] + norms[r+1:len(norms)]
	
	if q < lebesgue and lebesgue != math.inf: 
		print("There's no such Hölder's inequality!")
		input()
		return norms
		
	q, qprime = HolderExponent(lebesgue, q)
	
	funcs_new1 = "('{data}', 0)*('1', 0)".format(data = FuncData1[0])
	funcs_new2 = "('{data}', 0)*('1', 0)".format(data = FuncData2[0])
	
	splitted = [(funcs_new1, ord1, 0, q), (funcs_new2, ord2, 0, qprime)]
	
	return norms[0:r] + [splitted] + norms[r+1:len(norms)] 
	

def absorb_weaker(norms):

	sortnorm = sorted(norms, key = lambda x: (x[0][0], x[0][1], x[1][0], x[1][1]))
	groups = [list(g) for _, g in itertools.groupby(sortnorm, key=lambda x: (x[0][0], x[0][1], x[1][0], x[1][1]))]
	
	funcs1 = [group[0][0][0] for group in groups]; funcs2 = [group[0][1][0] for group in groups]
	order1 = [group[0][0][1] for group in groups]; order2 = [group[0][1][1] for group in groups]
	
	left_stronger = []; right_stronger = []
	for group in groups:
		
		left_exps = [(sbgrp[0][2], sbgrp[0][3]) for sbgrp in group]
		right_exps = [(sbgrp[1][2], sbgrp[1][3]) for sbgrp in group]
		
		sortleft = sorted(left_exps, key = lambda x: (x[0], x[1]))
		sortright = sorted(right_exps, key = lambda x: (x[0], x[1]))
		
		left_stronger.append(sortleft[-1])
		right_stronger.append(sortright[-1])
		
	leftnorms = [(funcs1[i], order1[i], left_stronger[i][0], left_stronger[i][1]) for i in range(len(groups))]
	rightnorms = [(funcs2[i], order2[i], right_stronger[i][0], right_stronger[i][1]) for i in range(len(groups))]
	
	return [[leftnorms[i], rightnorms[i]] for i in range(len(groups))]
	



def sortHolder(norms):

	splitted = []; nonsplitted = []

	for subnorm in norms:
		funcs0 = subnorm[0][0]; order0 = subnorm[0][1]; sobolev0 = subnorm[0][2]; lebesgue0 = subnorm[0][3]
		funcs1 = subnorm[1][0]; order1 = subnorm[1][1]; sobolev1 = subnorm[1][2]; lebesgue1 = subnorm[1][3]
		
		splits = funcs0.split("*")
		FuncData1 = literal_eval(splits[0]); FuncData2 = literal_eval(splits[1])
		
		if FuncData2[0] == '1':
			splitted.append(subnorm)
		else: nonsplitted.append(subnorm)
		
	
	return splitted, nonsplitted


def CheckRegularity(norms, kmax, lmax):

	MakeLeaf = False
	splitted, nonsplitted = sortHolder(norms)
	KH = sorted([(norm[0][1] + norm[0][2], norm[0][3]) for norm in splitted], key = lambda x: (x[0], x[1]))
	LH = sorted([(norm[1][1] + norm[1][2], norm[1][3]) for norm in splitted], key = lambda x: (x[0], x[1]))
	
	k1 = 0; l1 = 0; p1 = 0; q1 = 0
	
	if len(splitted) != 0:
		KP1 = KH[-1]; k1 = KP1[0]; p1 = KP1[1]
		LQ1 = LH[-1]; l1 = LQ1[0]; q1 = LQ1[1]
	
	K = []; L = []
	for norm in nonsplitted:
		funcs = norm[0][0]; order = norm[0][1]; sobolev = norm[0][2]; lebesgue = norm[0][3]
		
		splits = funcs.split("*")
		FuncData1 = literal_eval(splits[0]); FuncData2 = literal_eval(splits[1])
		orderu = FuncData1[1]; orderv = FuncData2[1]
		
		K.append((orderu + order + sobolev, lebesgue))
		L.append((orderv + order + sobolev, lebesgue))
	
	k2 = 0; l2 = 0; p2 = 0; q2 = 0
	K = sorted(K, key = lambda x: (x[0], x[1])); L = sorted(L, key = lambda x: (x[0], x[1]))
	if len(nonsplitted) != 0: 
		KP2 = K[-1]; k2 = KP2[0]; p2 = KP2[1]
		LQ2 = L[-1]; l2 = LQ2[0]; q2 = LQ2[1]
	
	
	
	if max(k1, k2) >= kmax or max(l1, l2) >= lmax or nonsplitted == []: MakeLeaf = True
	
	
	return MakeLeaf, (k1, p1), (l1, q1), (k2, p2), (l2, q2)
		

		
	
	
	


def eliminate(norms):
	norms.sort()
	norms = list(norms for norms,_ in itertools.groupby(norms))
	return norms

	
	

	
if __name__ == "__main__":
	
	print("Testing the actions:")
	print(" ")
	
	
	#_______________________Expansion__________________________________________________
	
	norms = [[("('u', 0)*('v', 0)", 0, 3, 2), ("('1', 0)*('1', 0)", 0, 0, 0)],
	         [("('u', 1)*('v', 0)", 0, 2, 1), ("('1', 0)*('1', 0)", 0, 0, 0)],
	         [("('1', 0)*('1', 0)", 0, 0, 0), ("('w', 0)*('z', 0)", 1, 1, 1)]]
	
	print("Original:", norms)
	print(" ")
	
	print("Expansion:", expand(norms, 2, 1))
	print(" ")
	
	
	#_______________________Leibiniz rule______________________________________________
	
	norms = [[("('u', 0)*('v', 0)", 2, 3, 2), ("('1', 0)*('1', 0)", 0, 0, 0)],
	         [("('u', 1)*('v', 0)", 4, 2, 1), ("('1', 0)*('1', 0)", 0, 0, 0)],
	         [("('1', 0)*('1', 0)", 0, 0, 0), ("('w', 0)*('z', 0)", 1, 1, 1)]]
	         
	print("Original:", norms)
	print(" ")
	         
	print("Leibiniz:", prod(norms, 1, 0))
	print(" ")
	
	
	#_______________________Rellich-Kondrachov_________________________________________
	
	norms = [[("('u', 0)*('v', 0)", 0, 0, 9), ("('1', 0)*('1', 0)", 0, 0, 0)],
	         [("('u', 1)*('v', 0)", 3, 2, 8), ("('1', 0)*('1', 0)", 0, 0, 0)],
	         [("('1', 0)*('1', 0)", 0, 0, 0), ("('w', 0)*('z', 0)", 1, 1, 1)]]
	
	print("Original:", norms)
	print(" ")
	
	print("Embedding:", embed(norms, 1, 0))
	print(" ")
	
	
	#_______________________Bounded seminorms by norms__________________________________
	
	norms = [[("('u', 0)*('v', 0)", 3, 1, 2), ("('1', 0)*('1', 0)", 0, 0, 0)],
	         [("('u', 1)*('v', 0)", 3, 9, 7), ("('1', 0)*('1', 0)", 0, 0, 0)],
	         [("('1', 0)*('1', 0)", 0, 0, 0), ("('w', 0)*('z', 0)", 1, 1, 1)]]
	
	print("Original:", norms)
	print(" ")
	
	print("Back to norm:", BoundByNorm(norms, 2, 2))
	print(" ")
	
	
	#_______________________Hölder's inequality________________________________________
	
	norms = [[("('u', 1)*('v', 0)", 0, 0, 2), ("('1', 0)*('1', 0)", 0, 0, 0)],
	         [("('u', 1)*('v', 0)", 0, 0, math.inf), ("('1', 0)*('1', 0)", 0, 0, 0)],
	         [("('1', 0)*('1', 0)", 0, 0, 0), ("('w', 0)*('z', 0)", 0, 0, 1)]]
	
	print("Original:", norms)
	print(" ")
	
	print("Hölder:", Holder(norms, 1, 2))
	print(" ")
	
	
	
	#_______________________eliminate same terms_______________________________________
	
	norms = [[("('u', 1)*('v', 0)", 0, 0, 2), ("('1', 0)*('1', 0)", 0, 0, 0)],
	         [("('u', 1)*('v', 0)", 0, 0, 2), ("('1', 0)*('1', 0)", 0, 0, 0)],
	         [("('1', 0)*('1', 0)", 0, 0, 0), ("('w', 0)*('z', 0)", 0, 0, 1)],
	         [("('u', 1)*('v', 0)", 0, 0, 2), ("('1', 0)*('1', 0)", 0, 0, 0)]]
	
	print("Original:", norms)
	print(" ")
	
	print("eliminated:", eliminate(norms))
	print(" ")
	
	
	
	#_______________________eliminate weaker terms_____________________________________
	
	norms = [[("('u', 0)*('1', 0)", 0, 0, 2), ("('v', 0)*('1', 0)", 0, 2, 2)],
	         [("('u', 0)*('1', 0)", 0, 0, 2), ("('v', 0)*('1', 0)", 1, 1, 2)],
	         [("('u', 0)*('1', 0)", 0, 1, 2), ("('v', 0)*('1', 0)", 0, 0, 2)],
	         [("('u', 0)*('v', 0)", 0, 2, 3), ("('1', 0)*('1', 0)", 0, 0, 0)],
	         [("('1', 0)*('1', 0)", 0, 0, 0), ("('w', 0)*('z', 0)", 0, 0, 1)],
	         [("('u', 4)*('v', 1)", 2, 5, 2), ("('1', 0)*('1', 0)", 0, 0, 0)],
	         [("('u', 4)*('v', 1)", 2, 6, 1), ("('1', 0)*('1', 0)", 0, 0, 0)],
	         [("('u', 0)*('1', 0)", 0, 1, 2), ("('v', 0)*('1', 0)", 0, 0, 2)]]
	
	print("Original:", norms)
	print(" ")
	
	print("Simplified:", absorb_weaker(norms))
	print(" ")
	
	
	
	#_______________________sort by Holder_____________________________________________
	
	norms = [[("('u', 0)*('1', 0)", 0, 0, 2), ("('v', 0)*('1', 0)", 0, 2, 2)],
	         [("('u', 0)*('1', 0)", 0, 0, 2), ("('v', 0)*('1', 0)", 1, 1, 2)],
	         [("('u', 0)*('1', 0)", 0, 1, 2), ("('v', 0)*('1', 0)", 0, 0, 2)],
	         [("('u', 0)*('v', 0)", 0, 2, 3), ("('1', 0)*('1', 0)", 0, 0, 0)],
	         [("('1', 0)*('1', 0)", 0, 0, 0), ("('w', 0)*('z', 0)", 0, 0, 1)],
	         [("('u', 4)*('v', 1)", 2, 5, 2), ("('1', 0)*('1', 0)", 0, 0, 0)],
	         [("('u', 4)*('v', 1)", 2, 6, 1), ("('1', 0)*('1', 0)", 0, 0, 0)],
	         [("('u', 0)*('1', 0)", 0, 1, 2), ("('v', 0)*('1', 0)", 0, 0, 2)]]
	
	print("Original:", norms)
	print(" ")
	
	print("Sorted by Hölder:", sortHolder(norms))
	print(" ")
	
	
	
	
	#_______________________check regularity___________________________________________
	
	norms = [[("('u', 1)*('v', 0)", 0, 1, 2), ("('1', 0)*('1', 0)", 0, 0, 0)],
	         [("('u', 0)*('v', 1)", 1, 1, 3), ("('1', 0)*('1', 0)", 0, 0, 2)],
	         [("('u', 1)*('1', 0)", 0, 0, 4), ("('v', 2)*('1', 0)", 0, 0, 4)],
	         [("('u', 3)*('1', 0)", 0, 0, 4), ("('v', 2)*('1', 0)", 0, 0, 4)]]
	         
	r = 3; t = 4; kmax = 3; lmax = 3
	
	print("Original:", norms)
	print(" ")
	
	print("Regularity checked:", CheckRegularity(norms, r, t, kmax, lmax))
	print(" ")
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	

		

