import math
import actions
import numpy as np
from SumOfNorms import sum_of_norms
from ast import literal_eval
from collections import deque
import time
import psutil


#Memory-based stopping criterion - can be skipped if RAM is large enough
#for skipping, comment out "import psutil" and the two following lines
proc = psutil.Process()
THRESHOLD = 3 * 1024**3  # 3 GB



class TreeNode:

    #Initialize the node with data and an empty list of children
    def __init__(self, data):
        self.data = data
        self.children = []
        self.parents = None
        self.nchildren = 0
        self.ancestors = [self]
        self.isleaf = False

    #Add a child node and update its ancestors
    def add_child(self, child):
        self.children.append(child)
        self.nchildren += 1
        child.ancestors = [anc for anc in self.ancestors] + child.ancestors
        child.parents = self

        
class Norm:
    def __init__(self, tup):

        #Data of the norm-tuple - stored as a class for convenience
        self.tup = tup
        
        self.fncs = tup[0]
        self.ordr = tup[1]
        self.sblv = tup[2]
        self.lbsg = tup[3]
    
		
		
def build_tree(root, pinit_u, pmax_u, pinit_v, pmax_v, step, kmax, lmax, depth):

    '''
	Inputs:

	root: Root node of the tree - initial norms to be bounded
	pmax_u: Maximum p-value for the Holder exponents w.r.t. u
    pinit_u: Initial p-value for the Holder exponents w.r.t. u
	pmax_v: Maximum p-value for the Holder exponents w.r.t. v
    pinit_v: Initial p-value for the Holder exponents w.r.t. v
	step: Step size for the p-values
	kmax: Maximal regularity in u
	lmax: Maximal regularity in v
	depth: Maximum depth of the tree

	Builds a tree of norm bounds using breadth-first search and prunes branches that reach maximal regularity.
    '''

	
    prange_u = np.arange(pinit_u, pmax_u + step, step) #Range of p-values for Holder exponents
    
    queue = deque([root]) #Queue for breadth-first search
    levels = [[root]]
    visited = set() #Set of visited norm-sets to avoid duplicates
    leafnodes = set() #Set of leaf nodes

    totalnnodes = 1
	
    while queue:
        parent = queue.popleft()
		
		
        current_depth = len(parent.ancestors) - 1 #Calculate current depth
        lvl = current_depth + 1
        if current_depth == depth: continue #Stop if max depth reached
			
        MakeLeafReg, MakeLeafHolder, (k1, p1), (l1, q1), (k2, p2), (l2, q2) = actions.CheckRegularity(parent.data, kmax, lmax) #Check regularity

		#Holder exponent ranges for the non-Holdered norms
        #Range for first Holder exponent
        srange = np.arange(max(p2, pinit_u), max(p2, pmax_u) + step, step) 

        #Range for second Holder exponent - the actual exponent will be its dual
        rrange = np.arange(max(q2, pinit_u), max(q2, pmax_u) + step, step) 

        #Range for second Holder exponent - now the inequality is not applied with the dual;
        #this yields inequalities that would be skipped otherwise
        trange = np.arange(max(q2, pinit_v), max(q2, pmax_v) + step, step)
		
        
        if MakeLeafReg: #If the node hit maximum regularity
			
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
                    normnew_tuple = tuple(tuple(item) for item in normnew) #convert to tuple of tuples for set operations
					
                    if parent.isleaf == False and normnew_tuple not in visited:

                        LowScore = False

                        #Check if there is any leaf node already proving a better result
                        for leaf in leafnodes: 
                            
                            #If you already found a better one, then stop searching
                            if LowScore: break
                            ku = leaf.data[0][0][2]; pu = leaf.data[0][0][3]
                            lv = leaf.data[0][1][2]; qv = leaf.data[0][1][3]

                            ustronger = False; vstronger = False
                            if k > ku or (k == ku and p >= pu): ustronger = True
                            if l > lv or (l == lv and q >= qv): vstronger = True

                            if ustronger and vstronger: LowScore = True


                        visited.add(normnew_tuple) #mark as visited
                        if not LowScore: #if there are not any better leaf nodes, then proceed with this one
                            normleaf = TreeNode(normnew)
                            parent.add_child(normleaf)
                            queue.append(normleaf) #add to queue for further processing
                            normleaf.isleaf = True #mark as leaf
                            leafnodes.add(normleaf) #add to leaf nodes set
                            totalnnodes += 1

                            if len(levels) <= lvl: levels += [[]]
                            levels[lvl].append(normleaf)

                for t in trange: #same process for the other Holder inequality

                    #sort the parameters for u to get the max regularity
                    Knew = sorted([(k1, p1), (k2, s)], key = lambda x: (x[0], x[1]))
                    KPnew = Knew[-1]; k = KPnew[0]; p = KPnew[1]
				
					#sort the parameters for v to get the max regularity
                    Lnew = sorted([(l1, q1), (l2, t)], key = lambda x: (x[0], x[1]))
                    LQnew = Lnew[-1]; l = LQnew[0]; q = LQnew[1]
				
					#define the new upper bound based on the max regularities
                    normnew = [[("('u', 0)*('1', 0)", 0, k, p), ("('v', 0)*('1', 0)", 0, l, q)]]
                    normnew_tuple = tuple(tuple(item) for item in normnew) #convert to tuple of tuples for set operations
					
                    if parent.isleaf == False and normnew_tuple not in visited:

                        LowScore = False
                        for leaf in leafnodes: 
                            ku = leaf.data[0][0][2]; pu = leaf.data[0][0][3]
                            lv = leaf.data[0][1][2]; qv = leaf.data[0][1][3]

                            ustronger = False; vstronger = False
                            othercase_u = (k == ku and p >= pu)
                            othercase_v = (l == lv and q >= qv)
                            if k > ku or othercase_u: ustronger = True
                            if l > lv or othercase_v: vstronger = True

                            
                            if ustronger and vstronger: LowScore = True

                            if LowScore: break
                        

                        visited.add(normnew_tuple) #mark as visited
                        if not LowScore:    
                            normleaf = TreeNode(normnew)
                            parent.add_child(normleaf)
                            queue.append(normleaf) #add to queue for further processing
                            normleaf.isleaf = True #mark as leaf
                            leafnodes.add(normleaf) #add to leaf nodes set
                            totalnnodes += 1

                            if len(levels) <= lvl: levels += [[]]
                            levels[lvl].append(normleaf)

        if MakeLeafHolder: #if all terms are Holder-splitted

            #do the same process as above to create a new leaf node
            k = k1; p = p1; l = l1; q = q1
            normnew = [[("('u', 0)*('1', 0)", 0, k, p), ("('v', 0)*('1', 0)", 0, l, q)]]
            normnew_tuple = tuple(tuple(item) for item in normnew) #convert to tuple of tuples for set operations 
            if parent.isleaf == False: # and normnew_tuple not in visited:
                
            
                LowScore = False
                for leaf in leafnodes: 
                    ku = leaf.data[0][0][2]; pu = leaf.data[0][0][3]
                    lv = leaf.data[0][1][2]; qv = leaf.data[0][1][3]

                    ustronger = False; vstronger = False
                    if k > ku or (k == ku and p >= pu): ustronger = True
                    if l > lv or (l == lv and q >= qv): vstronger = True

                    if ustronger and vstronger: LowScore = True
                    if LowScore: break

                if LowScore: visited.add(normnew_tuple)

                #visited.add(normnew_tuple) #mark as visited
                if not LowScore:
                    if normnew_tuple not in visited:
                        visited.add(normnew_tuple)
                        normleaf = TreeNode(normnew)
                        parent.add_child(normleaf)
                        queue.append(normleaf) #add to queue for further processing
                        normleaf.isleaf = True #mark as leaf
                        leafnodes.add(normleaf) #add to leaf nodes set
                        totalnnodes += 1

                        if len(levels) <= lvl: levels += [[]]
                        levels[lvl].append(normleaf)
                    else: #this one covers the case where the sum of norms contains just one term
                        parent_tuple = tuple(tuple(item) for item in parent.data)
                        visited.add(parent_tuple)
                        parent.isleaf = True #mark as leaf
                        leafnodes.add(parent) #add to leaf nodes set  

                       
						
		
		
        if parent.isleaf:

	    	#Print the proof for the leaf node kind of in latex format
		
			
            print(" ")
            print("Proof complete!")
            print("{anc}".format(anc = sum_of_norms(parent.ancestors[0].data)))
            for i in range(1, len(parent.ancestors)):
                print("    \\leq {ancestor}".format(ancestor = sum_of_norms(parent.ancestors[i].data)))
			
            print(" ")
			
			
            continue 

        else:

            #If the node is not in a terminal state, then compare it once more with the leafs,
            #in case new weaker ones where created on the same level after this one
            #if so, then don't expand it further
            LowScore = False
            u_low = False; v_low = False

            #compare with the nodes of the same depth
            if len(levels) <= lvl: levels += [[]]
            
            Kparent = sorted([(k1, p1), (k2, p2)], key = lambda x: (x[0], x[1]))
            Lparent = sorted([(l1, q1), (l2, q2)], key = lambda x: (x[0], x[1]))
            
            kparent = Kparent[-1][0]; pparent = Kparent[-1][1]
            lparent = Lparent[-1][0]; qparent = Lparent[-1][1]
            
            for node in levels[lvl]: 
                if node in parent.ancestors: continue
                
                #Get maximum regularities of both
                (kh, ph), (lh, qh), (kn, pn), (ln, qn) = actions.GetMaxReg(node.data)
                
                Klevel = sorted([(kh, ph), (kn, pn)], key = lambda x: (x[0], x[1]))
                Llevel = sorted([(lh, qh), (ln, qn)], key = lambda x: (x[0], x[1]))
                
                klevel = Klevel[-1][0]; plevel = Klevel[-1][1]
                llevel = Llevel[-1][0]; qlevel = Llevel[-1][1]

                if kparent > klevel or (kparent == klevel and pparent >= plevel): u_low = True
                if lparent > llevel or (lparent == llevel and qparent >= qlevel): v_low = True

                #if the current node has stronger regularity than the other one,
                #then it has a lower score
                if u_low and v_low: 
                    LowScore = True
                    break

            for leaf in leafnodes: 
                if LowScore: break
                ku = leaf.data[0][0][2]; pu = leaf.data[0][0][3]
                lv = leaf.data[0][1][2]; qv = leaf.data[0][1][3]

                ustronger = False; vstronger = False
                if kparent > ku or (k1 == ku and p1 >= pu): ustronger = True 
                if lparent > lv or (l1 == lv and q1 >= qv): vstronger = True

                if ustronger and vstronger: LowScore = True

            if LowScore: 

                #if the node has a low score, delete it
                #also, delete the ancestors leading only to this node
                ancestors_rev = parent.ancestors
                ancestors_rev.reverse()
                for anc in ancestors_rev:
                    if anc.nchildren > 0: break
                    anc.parents.children.remove(anc)
                    anc.parents.nchildren -= 1
                    totalnnodes -= 1
                continue

	
        for i in range(len(parent.data)): #iterate over all terms in the sum of norms
	
            tup0 = Norm(parent.data[i][0])
	
            splits0 = tup0.fncs.split("*") #split the function string to get individual functions
            FuncData01 = literal_eval(splits0[0]); FuncData02 = literal_eval(splits0[1])
            ord01 = FuncData01[1]; ord02 = FuncData02[1] #orders of the individual functions
			
            #If Holder's inequality has not yet been applied to this norm
            #and if the norm is not yet at maximal regularity
            if FuncData02[0] != '1' and abs(tup0.ordr + tup0.sblv) == 0 and parent.isleaf == False and MakeLeafReg == False: 
                prange_u = np.arange(max(pinit_u, tup0.lbsg), max(pmax_u, tup0.lbsg) + step, step)
                prange_v = np.arange(max(pinit_v, tup0.lbsg), max(pmax_v, tup0.lbsg) + step, step)
						
				#Apply Holder's inequality with all possible p-values
                for p in prange_u:
                    normnew = actions.Holder(parent.data, i, 0, p)
                    normnew = actions.eliminate(normnew) #eliminate duplicates
                    normnew = actions.absorb_weaker(normnew) #absorb the weaker norms by stronger ones
                    normnew = sorted(normnew) #sort for consistency
                    normnew_tuple = tuple(tuple(tuple(x) for x in row) for row in normnew)


                    LowScore = False
                    u_low = False; v_low = False

                    #compare with the nodes of the same depth
                    if len(levels) <= lvl: levels += [[]]
                    
                    (kh, ph), (lh, qh), (kn, pn), (ln, qn) = actions.GetMaxReg(normnew)
                    
                    Knode = sorted([(kh, ph), (kn, pn)], key = lambda x: (x[0], x[1]))
                    Lnode = sorted([(lh, qh), (ln, qn)], key = lambda x: (x[0], x[1]))
                    knode = Knode[-1][0]; pnode = Knode[-1][1]
                    lnode = Lnode[-1][0]; qnode = Lnode[-1][1]
                    
                    for node in levels[lvl]: 
                        if node in parent.ancestors: continue
                        
                        #Get maximum regularities of both
                        (k1, p1), (l1, q1), (k2, p2), (l2, q2) = actions.GetMaxReg(node.data)
                        
                        Klevel = sorted([(k1, p1), (k2, p2)], key = lambda x: (x[0], x[1]))
                        Llevel = sorted([(l1, q1), (l2, q2)], key = lambda x: (x[0], x[1]))
                        
                        klevel = Klevel[-1][0]; plevel = Klevel[-1][1]
                        llevel = Llevel[-1][0]; qlevel = Llevel[-1][1]
                        

                        if knode > klevel or (knode == klevel and pnode >= plevel): u_low = True
                        if lnode > llevel or (lnode == llevel and qnode >= qlevel): v_low = True

                        #if the current node has stronger regularity than the other one,
                        #then it has a lower score
                        if u_low and v_low: 
                            LowScore = True
                            break

                    #compare with the leaf nodes
                    u_low = False; v_low = False
                    for leaf in leafnodes:
                        if LowScore: break

                        ku = leaf.data[0][0][2]; pu = leaf.data[0][0][3]
                        lv = leaf.data[0][1][2]; qv = leaf.data[0][1][3]

                        if knode > ku or (knode == ku and pnode >= pu): u_low = True
                        if lnode > lv or (lnode == lv and qnode >= qv): v_low = True

                        #same principle
                        if u_low and v_low: LowScore = True

                            


                    if normnew_tuple not in visited: #if not yet visited
                        visited.add(normnew_tuple) #mark as visited

                        #if it isn't stronger than either the leaf or the same-depth nodes , 
                        #then create child;
                        #it will be compared further when it is dequed, in case 
                        #weaker (more promising) nodes are created afterwards
                        if not LowScore:
                            normnode = TreeNode(normnew) 
                            parent.add_child(normnode) #add as child
                            queue.append(normnode)
                            levels[lvl].append(normnode)
                            totalnnodes += 1

                #DO THE SAME WITH THE REST OF THE ACTIONS
					
                #The following does the same w.r.t. v
                for p in prange_v:
                    normnew = actions.Holder(parent.data, i, 1, p)
                    normnew = actions.eliminate(normnew) #eliminate duplicates
                    normnew = actions.absorb_weaker(normnew) #absorb the weaker norms by stronger ones
                    normnew = sorted(normnew) #sort for consistency
                    normnew_tuple = tuple(tuple(tuple(x) for x in row) for row in normnew)

                    LowScore = False
                    u_low = False; v_low = False

                    if len(levels) <= lvl: levels += [[]]
                    
                    (kh, ph), (lh, qh), (kn, pn), (ln, qn) = actions.GetMaxReg(normnew)
                    
                    Knode = sorted([(kh, ph), (kn, pn)], key = lambda x: (x[0], x[1]))
                    Lnode = sorted([(lh, qh), (ln, qn)], key = lambda x: (x[0], x[1]))
                    knode = Knode[-1][0]; pnode = Knode[-1][1]
                    lnode = Lnode[-1][0]; qnode = Lnode[-1][1]
                    
                    for node in levels[lvl]:
                        if node in parent.ancestors: continue
                        (k1, p1), (l1, q1), (k2, p2), (l2, q2) = actions.GetMaxReg(node.data)
                        
                        Klevel = sorted([(k1, p1), (k2, p2)], key = lambda x: (x[0], x[1]))
                        Llevel = sorted([(l1, q1), (l2, q2)], key = lambda x: (x[0], x[1]))
                        
                        klevel = Klevel[-1][0]; plevel = Klevel[-1][1]
                        llevel = Llevel[-1][0]; qlevel = Llevel[-1][1]
                        

                        if knode > klevel or (knode == klevel and pnode >= plevel): u_low = True
                        if lnode > llevel or (lnode == llevel and qnode >= qlevel): v_low = True

                        #if the current node has stronger regularity than the other one,
                        #then it has a lower score
                        if u_low and v_low: 
                            LowScore = True
                            break

                    u_low = False; v_low = False
                    for leaf in leafnodes:
                        if LowScore: break

                        ku = leaf.data[0][0][2]; pu = leaf.data[0][0][3]
                        lv = leaf.data[0][1][2]; qv = leaf.data[0][1][3]
                        if knode > ku or (knode == ku and pnode >= pu): u_low = True
                        if lnode > lv or (lnode == lv and qnode >= qv): v_low = True

                        if u_low and v_low: LowScore = True


                            

                    if normnew_tuple not in visited: #if not yet visited
                        visited.add(normnew_tuple) #mark as visited
                        if not LowScore:
                            normnode = TreeNode(normnew) 
                            parent.add_child(normnode) #add as child
                            queue.append(normnode)
                            levels[lvl].append(normnode)
                            totalnnodes += 1
					
            for j in range(2): #iterate over the two functions in the norm

                tup = Norm(parent.data[i][j])
			
                splits = tup.fncs.split("*") #split as above
                FuncData1 = literal_eval(splits[0]); FuncData2 = literal_eval(splits[1])
                ord1 = FuncData1[1]; ord2 = FuncData2[1]
				
                #If the total derivative order is positive
                #and the term is not yet Holdered
                #and the norm is not yet at maximal regularity
                if tup.ordr != 0 and tup.fncs != "('1', 0)*('1', 0)" and FuncData02[0] != '1' \
				    and parent.isleaf == False and MakeLeafReg == False:
                    normnew = actions.prod(parent.data, i, j) #product rule
                    normnew = actions.eliminate(normnew)
                    normnew = actions.absorb_weaker(normnew)
                    normnew = sorted(normnew)
                    normnew_tuple = tuple(tuple(tuple(x) for x in row) for row in normnew)
                    LowScore = False
                    u_low = False; v_low = False

                    if len(levels) <= lvl: levels += [[]]
                    
                    (kh, ph), (lh, qh), (kn, pn), (ln, qn) = actions.GetMaxReg(normnew)
                    
                    Knode = sorted([(kh, ph), (kn, pn)], key = lambda x: (x[0], x[1]))
                    Lnode = sorted([(lh, qh), (ln, qn)], key = lambda x: (x[0], x[1]))
                    
                    knode = Knode[-1][0]; pnode = Knode[-1][1]
                    lnode = Lnode[-1][0]; qnode = Lnode[-1][1]
                    
                    for node in levels[lvl]:
                        if node in parent.ancestors: continue
                        (k1, p1), (l1, q1), (k2, p2), (l2, q2) = actions.GetMaxReg(node.data)
                        
                        Klevel = sorted([(k1, p1), (k2, p2)], key = lambda x: (x[0], x[1]))
                        Llevel = sorted([(l1, q1), (l2, q2)], key = lambda x: (x[0], x[1]))
                        
                        klevel = Klevel[-1][0]; plevel = Klevel[-1][1]
                        llevel = Llevel[-1][0]; qlevel = Llevel[-1][1]
                        

                        if knode > klevel or (knode == klevel and pnode >= plevel): u_low = True
                        if lnode > llevel or (lnode == llevel and qnode >= qlevel): v_low = True

                        #if the current node has stronger regularity than the other one,
                        #then it has a lower score
                        if u_low and v_low: 
                            LowScore = True
                            break

                    u_low = False; v_low = False
                    for leaf in leafnodes:
                        if LowScore: break

                        ku = leaf.data[0][0][2]; pu = leaf.data[0][0][3]
                        lv = leaf.data[0][1][2]; qv = leaf.data[0][1][3]
                        if knode > ku or (knode == ku and pnode >= pu): u_low = True
                        if lnode > lv or (lnode == lv and qnode >= qv): v_low = True

                        if u_low and v_low: LowScore = True

                            

                    if normnew_tuple not in visited: 
                        visited.add(normnew_tuple) #mark as visited
                        if not LowScore:
                            normnode = TreeNode(normnew) 
                            parent.add_child(normnode) #add as child
                            queue.append(normnode)
                            levels[lvl].append(normnode)
                            totalnnodes += 1
				
				#Under the exact same conditions as above
                if tup.sblv != 0 and tup.fncs != "('1', 0)*('1', 0)" and FuncData02[0] != '1' \
				 	and parent.isleaf == False and MakeLeafReg == False:
                    normnew = actions.expand(parent.data, i, j) #expand Sobolev norm to sum of seminorms
                    normnew = actions.eliminate(normnew)
                    normnew = actions.absorb_weaker(normnew)
                    normnew = sorted(normnew)
                    normnew_tuple = tuple(tuple(tuple(x) for x in row) for row in normnew)

                    LowScore = False
                    u_low = False; v_low = False

                    if len(levels) <= lvl: levels += [[]]
                    
                    (kh, ph), (lh, qh), (kn, pn), (ln, qn) = actions.GetMaxReg(normnew)
                    
                    Knode = sorted([(kh, ph), (kn, pn)], key = lambda x: (x[0], x[1]))
                    Lnode = sorted([(lh, qh), (ln, qn)], key = lambda x: (x[0], x[1]))
                    
                    knode = Knode[-1][0]; pnode = Knode[-1][1]
                    lnode = Lnode[-1][0]; qnode = Lnode[-1][1]
                    
                    for node in levels[lvl]:
                        if node in parent.ancestors: continue
                        (k1, p1), (l1, q1), (k2, p2), (l2, q2) = actions.GetMaxReg(node.data)
                        
                        Klevel = sorted([(k1, p1), (k2, p2)], key = lambda x: (x[0], x[1]))
                        Llevel = sorted([(l1, q1), (l2, q2)], key = lambda x: (x[0], x[1]))
                        
                        klevel = Klevel[-1][0]; plevel = Klevel[-1][1]
                        llevel = Llevel[-1][0]; qlevel = Llevel[-1][1]
                        

                        if knode > klevel or (knode == klevel and pnode >= plevel): u_low = True
                        if lnode > llevel or (lnode == llevel and qnode >= qlevel): v_low = True

                        #if the current node has stronger regularity than the other one,
                        #then it has a lower score
                        if u_low and v_low: 
                            LowScore = True
                            break

                    u_low = False; v_low = False
                    for leaf in leafnodes:
                        if LowScore: break

                        ku = leaf.data[0][0][2]; pu = leaf.data[0][0][3]
                        lv = leaf.data[0][1][2]; qv = leaf.data[0][1][3]
                        if knode > ku or (knode == ku and pnode >= pu): u_low = True
                        if lnode > lv or (lnode == lv and qnode >= qv): v_low = True

                        if u_low and v_low: LowScore = True

                            

                    if normnew_tuple not in visited: 
                        visited.add(normnew_tuple) #mark as visited
                        if not LowScore:
                            normnode = TreeNode(normnew) 
                            parent.add_child(normnode) #add as child
                            queue.append(normnode)
                            levels[lvl].append(normnode)
                            totalnnodes += 1

                if tup.fncs != "('1', 0)*('1', 0)" and FuncData02[0] != '1' \
				    and parent.isleaf == False and MakeLeafReg == False:
                    normnew = actions.embed(parent.data, i, j) #apply Sobolev embedding
                    normnew = actions.eliminate(normnew)
                    normnew = actions.absorb_weaker(normnew)
                    normnew = sorted(normnew)
                    normnew_tuple = tuple(tuple(tuple(x) for x in row) for row in normnew)

                    LowScore = False
                    Holder_u_low = False; Holder_v_low = False
                    nonHolder_u_low = False; nonHolder_v_low = False

                    LowScore = False
                    u_low = False; v_low = False

                    if len(levels) <= lvl: levels += [[]]
                    
                    (kh, ph), (lh, qh), (kn, pn), (ln, qn) = actions.GetMaxReg(normnew)
                    
                    Knode = sorted([(kh, ph), (kn, pn)], key = lambda x: (x[0], x[1]))
                    Lnode = sorted([(lh, qh), (ln, qn)], key = lambda x: (x[0], x[1]))
                    
                    knode = Knode[-1][0]; pnode = Knode[-1][1]
                    lnode = Lnode[-1][0]; qnode = Lnode[-1][1]
                    
                    for node in levels[lvl]:
                        if node in parent.ancestors: continue
                        (k1, p1), (l1, q1), (k2, p2), (l2, q2) = actions.GetMaxReg(node.data)
                        
                        Klevel = sorted([(k1, p1), (k2, p2)], key = lambda x: (x[0], x[1]))
                        Llevel = sorted([(l1, q1), (l2, q2)], key = lambda x: (x[0], x[1]))
                        
                        klevel = Klevel[-1][0]; plevel = Klevel[-1][1]
                        llevel = Llevel[-1][0]; qlevel = Llevel[-1][1]
                        

                        if knode > klevel or (knode == klevel and pnode >= plevel): u_low = True
                        if lnode > llevel or (lnode == llevel and qnode >= qlevel): v_low = True

                        #if the current node has stronger regularity than the other one,
                        #then it has a lower score
                        if u_low and v_low: 
                            LowScore = True
                            break

                    u_low = False; v_low = False
                    for leaf in leafnodes:
                        if LowScore: break

                        ku = leaf.data[0][0][2]; pu = leaf.data[0][0][3]
                        lv = leaf.data[0][1][2]; qv = leaf.data[0][1][3]
                        if knode > ku or (knode == ku and pnode >= pu): u_low = True
                        if lnode > lv or (lnode == lv and qnode >= qv): v_low = True

                        if u_low and v_low: LowScore = True

                            

                    if normnew_tuple not in visited: 
                        visited.add(normnew_tuple) #mark as visited
                        if not LowScore:
                            normnode = TreeNode(normnew) 
                            parent.add_child(normnode) #add as child
                            queue.append(normnode)
                            levels[lvl].append(normnode)
                            totalnnodes += 1
                            

        #If no children were added and there are nonsplitted terms, 
        #prune the branch and remove ancestors  only leading to this node,
        #so that you won't have any useless leaf nodes
        ancestors_rev = parent.ancestors
        ancestors_rev.reverse()
        for anc in ancestors_rev:
            if anc.nchildren > 0: break
            anc.parents.children.remove(anc)
            anc.parents.nchildren -= 1
            totalnnodes -= 1

        #for skipping the memory-based stopping criterion,
        #comment out the three following lines as well
        if proc.memory_info().rss >= THRESHOLD:
            print("Memory threshold reached; stopping loop.")
            break

    print("Total number of nodes:", totalnnodes)
    
		
#Example: Find upper bounds for \|uv\|_{H^1}
funcs = "('u', 0)*('v', 0)"
norms = [[(funcs, 0, 1, 2), ("('1', 0)*('1', 0)", 0, 0, 0)]]

tup_init = Norm(norms[0][0])
pinit_u = tup_init.lbsg; pmax_u = 5
pinit_v = tup_init.lbsg; pmax_v = 5


norms = sorted(norms)

kmax = math.inf; lmax = math.inf; step = 1
#kmax = 3; lmax = 3; step = 1



start_time = time.time()
root = TreeNode(norms); depth = math.inf
build_tree(root, pinit_u, pmax_u, pinit_v, pmax_v, step, kmax, lmax, depth)
end_time = time.time()


print(" ")
print("Total computation time: {time} seconds".format(time = end_time - start_time))
print(" ")
		
		
				
