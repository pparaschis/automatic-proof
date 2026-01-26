import math
import actions
import numpy as np
from SumOfNorms import sum_of_norms
from ast import literal_eval


class TreeNode:

	#Initialize the node with data and an empty list of children
    def __init__(self, data):
        self.data = data
        self.children = []
        self.ancestors = [self.data]
        self.isleaf = False

	#Add a child node and update its ancestors
    def add_child(self, child):
        self.children.append(child)
        child.ancestors = [anc for anc in self.ancestors] + child.ancestors
        
class Norm:
	def __init__(self, tup):

		#Data of the norm-tuple - stored in a class for convenience
		self.tup = tup
		
		self.fncs = tup[0]
		self.ordr = tup[1]
		self.sblv = tup[2]
		self.lbsg = tup[3]
    
	
		
		
def build_tree(root, pmax, step, kmax, lmax, depth):

	'''
	Inputs:

	root: Root node of the tree - initial norms to be bounded
	pmax: Maximum p-value for the Holder exponents
	step: Step size for the p-values
	kmax: Maximal regularity in u
	lmax: Maximal regularity in v
	depth: Maximum depth of the tree

	Builds a tree of norm bounds using depth-first traversal and prunes branches that reach maximal regularity.
	'''

	prange = np.arange(pinit, pmax + step, step) #Range of p-values for Holder exponents
	stack = [root] #Stack for depth-first traversal
	visited = [] #List of visited norm-sets to avoid duplicates
	
	while stack:
		parent = stack.pop() #Get the next node to process
		ParentHitMaxReg = False #Flag to check if parent hit max regularity
		
		
		current_depth = len(parent.ancestors) - 1 #Calculate current depth
		if current_depth == depth: continue #Stop if max depth reached
			
		MakeLeaf, (k1, p1), (l1, q1), (k2, p2), (l2, q2) = actions.CheckRegularity(parent.data, kmax, lmax) #Check regularity

		#Holder exponent ranges for the non-Holdered norms
		srange = np.arange(max(p2, pinit), max(p2, pmax) + step, step) #Range for second Holder exponent
		rrange = np.arange(max(q2, pinit), max(q2, pmax) + step, step) #Range for second Holder exponent - the actual exponent will be its dual
		
		if MakeLeaf:
			ParentHitMaxReg = True
			for s in srange:
				for r in rrange:
					
					r, t = actions.HolderExponent(q2, r) #Compute the dual exponent of r

					#sort the parameters for u to get the max regularity
					Knew = sorted([(k1, p1), (k2, s)], key = lambda x: (x[0], x[1]))
					KPnew = Knew[-1]; k = KPnew[0]; p = KPnew[1]
				
					#sort the parameters for v to get the max regularity
					Lnew = sorted([(l1, q1), (l2, t)], key = lambda x: (x[0], x[1]))
					LQnew = Lnew[-1]; l = LQnew[0]; q = LQnew[1]
				
					#define the new upper bound based on the max regularities
					normnew = [[("('u', 0)*('1', 0)", 0, k, p), ("('v', 0)*('1', 0)", 0, l, q)]]
					if parent.isleaf == False and normnew not in visited:
						visited.append(normnew) #mark as visited
						normleaf = TreeNode(normnew)
						parent.add_child(normleaf)
						stack.append(normleaf) #add to stack for further processing
						normleaf.isleaf = True #mark as leaf
						
		
		
		if parent.isleaf:

			#Print the proof for the leaf node kind of in latex format
		
			
			print(" ")
			print("Proof complete!")
			print("{anc}".format(anc = sum_of_norms(parent.ancestors[0])))
			for i in range(1, len(parent.ancestors)):
				print("    \\leq {ancestor}".format(ancestor = sum_of_norms(parent.ancestors[i])))
			
			print(" ")
			
			
			continue 
	
		
	
	
		for i in range(len(parent.data)): #iterate over all terms in the sum of norms
	
			tup0 = Norm(parent.data[i][0])
	
			splits0 = tup0.fncs.split("*") #split the function string to get individual functions
			FuncData01 = literal_eval(splits0[0]); FuncData02 = literal_eval(splits0[1])
			ord01 = FuncData01[1]; ord02 = FuncData02[1] #orders of the individual functions
			
			#If Holder's inequality has not yet been applied to this norm
			#and if the norm is not yet at maximal regularity
			if FuncData02[0] != '1' and abs(tup0.ordr + tup0.sblv) == 0 and parent.isleaf == False and ParentHitMaxReg == False: 
				prange = np.arange(max(pinit, tup0.lbsg), max(pmax, tup0.lbsg) + step, step)
				
				#Apply Holder's inequality with all possible p-values
				for p in prange:
					normnew = actions.Holder(parent.data, i, p)
					normnew = actions.eliminate(normnew) #eliminate duplicates
					normnew = actions.absorb_weaker(normnew) #absorb the weaker norms by stronger ones
					normnew = sorted(normnew) #sort for consistency
					if normnew not in visited: #if not yet visited
						visited.append(normnew) #mark as visited
						normnode = TreeNode(normnew) 
						parent.add_child(normnode) #add as child
						stack.append(normnode)


					
					#The following does the same w.r.t. v - commented out for now (possibly needs correction too)
					'''
					p, pstar = actions.HolderExponent(tup0.lbsg, p)
					if abs(tup0.lbsg - pstar) > 0.5*step:
						normnew = actions.Holder(norms, i, pstar)
						normnew = actions.eliminate(normnew)
						normnew = actions.absorb_weaker(normnew)
						normnew = sorted(normnew)
						normnode = TreeNode(normnew)
						parent.add_child(normnode)
						stack.append(normnode)
						#if parent.data != normnode.data: parent.add_child(normnode)
					'''
					
			for j in range(2): #iterate over the two functions in the norm

				tup = Norm(parent.data[i][j])
			
				splits = tup.fncs.split("*") #split as above
				FuncData1 = literal_eval(splits[0]); FuncData2 = literal_eval(splits[1])
				ord1 = FuncData1[1]; ord2 = FuncData2[1]
				
				#If the total derivative order is positive
				#and the term is not yet Holdered
				#and the norm is not yet at maximal regularity
				if tup.ordr != 0 and tup.fncs != "('1', 0)*('1', 0)" and FuncData02[0] != '1' \
				 	and parent.isleaf == False and ParentHitMaxReg == False: 
					normnew = actions.prod(parent.data, i, j) #product rule
					normnew = actions.eliminate(normnew)
					normnew = actions.absorb_weaker(normnew)
					normnew = sorted(normnew)
					if normnew not in visited: #same as above
						visited.append(normnew) 
						normnode = TreeNode(normnew)
						parent.add_child(normnode) 
						stack.append(normnode)
				
				#Under the exact same conditions as above
				if tup.sblv != 0 and tup.fncs != "('1', 0)*('1', 0)" and FuncData02[0] != '1' \
				 	and parent.isleaf == False and ParentHitMaxReg == False:
					normnew = actions.expand(parent.data, i, j) #expand Sobolev norm to sum of seminorms
					normnew = actions.eliminate(normnew)
					normnew = actions.absorb_weaker(normnew)
					normnew = sorted(normnew)
					if normnew not in visited:
						visited.append(normnew)
						normnode = TreeNode(normnew)
						parent.add_child(normnode)
						stack.append(normnode)
				
				#Under the same conditions as above, but now allowing zero derivative order
				if tup.fncs != "('1', 0)*('1', 0)" and FuncData02[0] != '1' \
				 	and parent.isleaf == False and ParentHitMaxReg == False: 
					normnew = actions.embed(parent.data, i, j) #apply Sobolev embedding
					normnew = actions.eliminate(normnew)
					normnew = actions.absorb_weaker(normnew)
					normnew = sorted(normnew)
					if normnew not in visited:
						visited.append(normnew)
						normnode = TreeNode(normnew)
						parent.add_child(normnode)
						stack.append(normnode)
		
			
			
	
		
#Example: Find upper bounds for \|uv\|_{H^1}
funcs = "('u', 0)*('v', 0)"
norms = [[(funcs, 0, 1, 2), ("('1', 0)*('1', 0)", 0, 0, 0)]]

tup_init = Norm(norms[0][0]); pinit = tup_init.lbsg; pmax = 5

print(" ")
print(norms)
print(" ")

norms = sorted(norms)

kmax = 2; lmax = 2; step = 1

root = TreeNode(norms); depth = math.inf
build_tree(root, pmax, step, kmax, lmax, depth)
	
					
	
		
		
				
