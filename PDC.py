# PDC.py
# Author: Jesse Rivera

# A program for working with permutations and parabolic double cosets in symmetric groups
# For use with the Washington Experimental Mathematics Lab (WXML)


# Recall: multiplying on the LEFT  permutes VALUES
#         multiplying on the RIGHT permutes POSITIONS
#         permutations are multiplied from RIGHT to LEFT
#         TOP row of the w-ocean corresponds to RIGHT multiplication
#         BOTTOM row of the w-ocean corresponds to LEFT  multiplication


import turtle # for drawing w-oceans
from tkinter import * # for saving w-oceans to postscript
from itertools import chain, combinations # for powerset function
import time # for test functions


####################
# GLOBAL VARIABLES #
####################


# S_N, determines which symmetric group we will be working in
# (i.e. the size of the permutations)
N = 5

print('Currently N = ' + str(N) + '.')
##print('Remember to call init_turtle() before calling drawOcean(w,save) or draw_S(n).')

# NOTE: Permutations are written in one-line notation and are represented as tuples

# examples for testing
w0 = (5,4,3,2,1)
w1 = (3, 1, 4, 5, 2)
w2 = (1,3,4,5,7,8,2,6,14,15,16,9,10,11,12,13)
w3 = (7,1,2,3,5,4,6)

# Subsets of adjacent transpositions, represented as sets
# examples for testing
##I1 = set([1, 3, 4])
##J1 = set([2])

# Initial terms for the a-sequences
# M[k][m] returns the mth term of the sequence a^k, for 0 <= m <= 4
# 5 and 6 represent 2' and 2'' respectively
A_initial = [[1,2,6,20,66], [1,3,9,28,89], [1,4,12,36,112], [1,4,14,46,148], [1,4,16,56,184], [1,3,11,37,119], [1,4,12,37,118]]

# Cache for the a-sequences
# A[k][m] returns the mth term of the sequence a^k
# 5 and 6 represent 2' and 2'' respectively
A = [[0 for x in range(10000)] for y in range(7)]

# Initializing the initial terms for the a-sequences
for i in range(7):
    for j in range(5):
        A[i][j] = A_initial[i][j]

# Maps the boundary apparatus (tuple) (I,J,K,L) to the corresponding b-sequence (0 - 26)
bd_dict = {(0,0,0,0) : 0,
           (1,0,0,0) : 1, (0,1,0,0) : 1, (0,0,1,0) : 1, (0,0,0,1) : 1,
           (1,0,1,0) : 2, (0,1,0,1) : 2,
           (1,1,0,0) : 3, (0,0,1,1) : 3,
           (0,1,1,0) : 4, (1,0,0,1) : 4,
           (1,1,1,0) : 5, (1,1,0,1) : 5, (1,0,1,1) : 5, (0,1,1,1) : 5,
           (1,1,1,1) : 6,
           (10,0,0,0) : 7, (0,10,0,0) : 7, (0,0,10,0) : 7, (0,0,0,10) : 7,
           (10,0,1,0) : 8, (1,0,10,0) : 8, (0,10,0,1) : 8, (0,1,0,10) : 8,
           (10,1,0,0) : 9, (1,10,0,0) : 9, (0,0,10,1) : 9, (0,0,1,10) : 9,
           (0,10,1,0) : 10, (0,1,10,0) : 10, (10,0,0,1) : 10, (1,0,0,10) : 10,
           (1,10,1,0) : 11, (10,1,0,1) : 11, (0,1,10,1) : 11, (1,0,1,10) : 11,
           (1,1,10,0) : 12, (10,0,1,1) : 12, (0,10,1,1) : 12, (1,1,0,10) : 12,
           (10,1,1,0) : 13, (1,10,0,1) : 13, (1,0,10,1) : 13, (0,1,1,10) : 13,
           (10,1,1,1) : 14, (1,10,1,1) : 14, (1,1,10,1) : 14, (1,1,1,10) : 14,
           (10,0,10,0) : 15, (0,10,0,10) : 15,
           (10,10,0,0) : 16, (0,0,10,10) : 16,
           (0,10,10,0) : 17, (10,0,0,10) : 17,
           (1,10,10,0) : 18, (0,10,10,1) : 18, (10,1,0,10) : 18, (10,0,1,10) : 18,
           (10,10,1,0) : 19, (10,10,0,1) : 19, (1,0,10,10) : 19, (0,1,10,10) : 19,
           (10,1,10,0) : 20, (10,0,10,1) : 20, (1,10,0,10) : 20, (0,10,1,10) : 20,
           (10,1,10,1) : 21, (1,10,1,10) : 21,
           (10,10,1,1) : 22, (1,1,10,10) : 22,
           (1,10,10,1) : 23, (10,1,1,10) : 23,
           (10,10,10,0) : 24, (10,10,0,10) : 24, (10,0,10,10) : 24, (0,10,10,10) : 24,
           (10,10,10,1) : 25, (10,10,1,10) : 25, (10,1,10,10) : 25, (1,10,10,10) : 25,
           (10,10,10,10) : 26}

# Cache for the b-equences, B[k][m] returns the mth term of the sequence b^k
B = [[0 for x in range(10000)] for y in range(27)]

# Initial terms for the b-sequences
B_initial = [[1,2,6,20,66,214], [1,3,9,28,89,285,914], [1,3,11,37,119,380,1216], [1,4,12,36,112,356,1140], [1,4,12,37,118,379,1216],
             [1,4,14,46,148,474,1518], [1,4,16,56,184,592,1896], [2,5,15,48,155,499,1602], [2,6,20,65,208,665,2130], [2,7,21,64,201,641,2054],
             [2,7,21,65,207,664,2130], [2,7,25,83,267,854,2734], [2,8,26,82,260,830,2658], [2,8,26,83,266,853,2734], [2,8,30,102,332,1066,3414],
             [4,11,35,113,363,1164,3732], [4,12,36,112,356,1140,3656], [4,12,36,113,362,1163,3732], [4,14,46,147,468,1495,4788], [4,14,46,148,474,1518,4864],
             [4,15,47,147,467,1494,4788], [4,15,55,185,599,1920,6148], [4,16,56,184,592,1896,6072], [4,16,56,185,598,1919,6148], [8,26,82,260,830,2658,8520],
             [8,30,102,332,1066,3414,10936], [16,56,184,592,1896,6072,19456]]

# Initializing the initial terms for the b-sequences
for i in range(27):
    for j in range(6):
        B[i][j] = B_initial[i][j]


###################
# BASIC FUNCTIONS #
###################


# Initializing the turtle module
def init_turtle():
    turtle.setup(width=1200, height=600)
    turtle.delay(0)
    turtle.speed(0)

init_turtle()

def set_N(n):
    global N
    N = n
    global w0
    x = [0]*n
    for i in range(n):
        x[i] = n - i
    w0 = tuple(x)
    print('Currently N = ' + str(n) + '.')

# Returns the powerset of the given iterable structure, as a set of tuples
def powerset(X):
    return set(chain.from_iterable(combinations(list(X), r) for r in range(len(X)+1)))

# Returns the inverse of the given permutation
def inverse(w):
    z = [0]*N
    for i in range(N):
        z[i] = w.index(i + 1) + 1
    return tuple(z)

# Multiplies the given permutations in the order in which they are given
# Returns the product as a tuple
def mult(w,s):
    z = [0]*N
    for i in range(N):
        z[i] = w[s[i] - 1]
    return tuple(z)

# Returns the length (number of inversions) of the given permutation
def length(w):
    result = 0
    for i in range(N):
        for j in range(i,N):
            if w[j] < w[i]:
                result += 1
    return result

# Returns the adjacent transposition s_k as a tuple
def s(k):
    z = list(range(1,N + 1))
    z[k - 1] = k + 1
    z[k] = k
    return tuple(z)


########################
# ASCENTS AND DESCENTS #
########################


# Given a permutation w and an integer k, returns whether the
# adjacent transposition s_k is a left ascent of w
# (i.e. whether length(s_k*w) > length(w))
def isLeftAscent(w,k):
    return w.index(k) < w.index(k + 1)

# Given a permutation w and an integer k, returns whether the
# adjacent transposition s_k is a right ascent of w
# (i.e. whether length(w*s_k) > length(w))
def isRightAscent(w,k):
    return w[k - 1] < w[k]

# Given a permutation w and an integer k, returns whether the
# adjacent transposition s_k is a left descent of w
# (i.e. whether length(s_k*w) < length(w))
def isLeftDescent(w,k):
    return w.index(k) > w.index(k + 1)

# Given a permutation w and an integer k, returns whether the
# adjacent transposition s_k is a right descent of w
# (i.e. whether length(w*s_k) < length(w))
def isRightDescent(w,k):
    return w[k - 1] > w[k]

# Returns the left ascent set of the given permutation
def leftAscentSet(w):
    result = set()
    for i in range(N - 1):
        if isLeftAscent(w,i + 1):
            result.add(i + 1)
    return result

# Returns the right ascent set of the given permutation
def rightAscentSet(w):
    result = set()
    for i in range(N - 1):
        if isRightAscent(w,i + 1):
            result.add(i + 1)
    return result

# Returns the left descent set of the given permutation
def leftDescentSet(w):
    result = set()
    for i in range(N - 1):
        if isLeftDescent(w,i + 1):
            result.add(i + 1)
    return result

# Returns the right descent set of the given permutation
def rightDescentSet(w):
    result = set()
    for i in range(N - 1):
        if isRightDescent(w,i + 1):
            result.add(i + 1)
    return result

# Returns whether the adjacent transposition s_k is a small left ascent of w
def isSmallLeftAscent(w,k):
    return w.index(k) + 1 == w.index(k + 1)

# Returns whether the adjacent transposition s_k is a small right ascent of w    
def isSmallRightAscent(w,k):
    return w[k - 1] + 1 == w[k]

# Returns whether the adjacent transposition s_k is a large left ascent of w
def isLargeLeftAscent(w,k):
    return isLeftAscent(w,k) and (not isSmallLeftAscent(w,k))

# Returns whether the adjacent transposition s_k is a large right ascent of w
def isLargeRightAscent(w,k):
    return isRightAscent(w,k) and (not isSmallRightAscent(w,k))

# Returns the small left ascent set of w
def smallLeftAscentSet(w):
    result = set()
    for i in range(N - 1):
        if isSmallLeftAscent(w,i + 1):
            result.add(i + 1)
    return result

# Returns the small right ascent set of w
def smallRightAscentSet(w):
    result = set()
    for i in range(N - 1):
        if isSmallRightAscent(w,i + 1):
            result.add(i + 1)
    return result

# Returns the large left ascent set of w
def largeLeftAscentSet(w):
    result = set()
    for i in range(N - 1):
        if isLargeLeftAscent(w,i + 1):
            result.add(i + 1)
    return result

# Returns the large right ascent set of w
def largeRightAscentSet(w):
    result = set()
    for i in range(N - 1):
        if isLargeRightAscent(w,i + 1):
            result.add(i + 1)
    return result


################################
# MINIMAL AND MAXIMAL ELEMENTS #
################################

# Returns the minimal element in the right coset w*W_J
def minimalRight(w,J):
    aux = list.copy(list(w)) # auxiliary storage, as to not modify w
    z = list.copy(list(w))
    for i in range(len(J)):
        for j in J:
            if z[j - 1] > z[j]:
                z[j - 1] = aux[j]
                z[j] = aux[j - 1]
                aux[j - 1] = z[j - 1]
                aux[j] = z[j]
    return tuple(z)

# Returns the minimal element in the left coset W_I*w
def minimalLeft(w,I):
    aux = list.copy(list(w)) # auxiliary storage, as to not modify w
    z = list.copy(list(w))
    for j in range(len(I)):
        for i in I:
            if aux.index(i) > aux.index(i + 1):
                z[aux.index(i)] = i + 1
                z[aux.index(i + 1)] = i
                aux[aux.index(i)] = z[aux.index(i)]
                aux[aux.index(i + 1)] = z[aux.index(i + 1)]
    return tuple(z)

# Returns the minimal element in the parabolic double coset W_I*w*W_J
def minimal(I,w,J):
    z = minimalLeft(w,I)
    z = minimalRight(z,J)
    return z

# Returns the maximal element in the right coset w*W_J
def maximalRight(w,J):
    aux = list.copy(list(w)) # auxiliary storage, as to not modify w
    z = list.copy(list(w))
    for i in range(len(J)):
        for j in J:
            if z[j - 1] < z[j]:
                z[j - 1] = aux[j]
                z[j] = aux[j - 1]
                aux[j - 1] = z[j - 1]
                aux[j] = z[j]
    return tuple(z)

# Returns the maximal element in the left coset W_I*w
def maximalLeft(w,I):
    aux = list.copy(list(w)) # auxiliary storage, as to not modify w
    z = list.copy(list(w))
    for j in range(len(I)):
        for i in I:
            if aux.index(i + 1) > aux.index(i):
                z[aux.index(i + 1)] = i
                z[aux.index(i)] = i + 1
                aux[aux.index(i + 1)] = z[aux.index(i + 1)]
                aux[aux.index(i)] = z[aux.index(i)]
    return tuple(z)

# Returns the maximal element in the double coset W_I*w*W_J
def maximal(I,w,J):
    z = maximalLeft(w,I)
    z = maximalRight(z,J)
    return z

# Returns whether W_I*w*W_J = Z_K*z*Z_L
def equals(I,w,J,K,z,L):
    return (minimal(I,w,J) == minimal(K,z,L)) and (maximal(I,w,J) == maximal(K,z,L))

# Returns the rank of W_IwW_J
def rank(I,w,J):
    return len(maximal(I,w,J)) - len(minimal(I,w,J)) + 1


###############################
# A-SEQUENCES AND B-SEQUENCES #
###############################


# Returns which of the seven symmetry types correspond to the given boundary apparatus
# 5 and 6 represent 2' and 2'' respectively
# The input i,j,k,l are in {0,1} and represent the whether or not the lower left,
# upper left, lower right, upper right boundaries are filled in
def bd_a(i,j,k,l):
    if i + j + k + l != 2:
        return i + j + k + l
    else:
        if i == j:
            return 2
        elif i == k:
            return 5
        else: # (i == l)
            return 6

# Returns the mth term of the sequence a^k using the recurence relation
def a(k,m):
    if A[k][m] != 0:
        return A[k][m]
    else:
        result = 6*a(k,m-1) - 13*a(k,m-2) + 16*a(k,m-3) - 11*a(k,m-4) + 4*a(k,m-5)
        A[k][m] = result
        return result

# Returns the mth term of the a-sequence for the boundary apparatus (i,j,k,l)
def a2(i,j,k,l,m):
    x = bd_a(i,j,k,l)
    return a(x,m)

# Prints the first n terms of the sequence a^k
def print_a(k,n):
    for i in range(n):
        print(a(k,i))

# Returns b^k_m, the mth term of the k^th b-sequence
def b(k,m):
    if B[k][m] != 0:
        return B[k][m]
    else:
        result = 6*b(k,m-1) - 13*b(k,m-2) + 16*b(k,m-3) - 11*b(k,m-4) + 4*b(k,m-5)
        B[k][m] = result
        return result

# Prints the first n terms of the sequence b^k
def print_b(k,n):
    for i in range(n):
        print(b(k,i))


##################################
# PARABOLIC SUBGROUPS AND COSETS #
##################################


# Returns the parabolic subgroup W_I as a set
def parabolic_subgroup(I):
    result = set()
    aux = set()
    for i in I:
        result.add(s(i))
        aux.add(s(i))
    # counters
    x = -1
    y = 0
    # terminates when no new permutations are obtained from (pairwise) multiplying all elements
    while x < y:
        x = len(result)
        for w in result:
            for z in result:
                aux.add(mult(w,z))
        result = set.copy(aux)
        y = len(result)
    return result

# Returns the double coset XwY as a set
def double_coset(X,w,Y):
    result = set([w])
    for x in X:
        for y in Y:
            result.add(mult(mult(x,w),y))
    return set(result)

# Returns the parabolic double coset W_IwW_J as a set
def PDC(I,w,J):
    return double_coset(parabolic_subgroup(I),w,parabolic_subgroup(J))

# Returns the symmetric group S_n as a set, using Heap's algorithm (recursive)
def S(k):
    result = set()
    generate(k,list(range(1,N + 1)),result)
    return result

def generate(m,E,result):
    aux = 0
    if m == 1:
          result.add(tuple(E))
    else:
        for i in range(m - 1):
            generate(m - 1,E,result)
            if m % 2 == 0:
                # swapping E[i] and E[m-1]
                aux = E[i]
                E[i] = E[m - 1]
                E[m - 1] = aux
            else:
                # swapping E[0] and E[m-1]
                aux = E[0]
                E[0] = E[m - 1]
                E[m - 1] = aux
        generate(m - 1,E,result)


############
# W-OCEANS #
############


# Prints w-ocean in text format to a file named "(w(1), w(2), ..., w(n))-ocean.txt"
##def oceanText(w):
##    f = open(str(w) + '-ocean.txt','w')
##    smallRight = smallRightAscentSet(w)
##    largeRight = largeRightAscentSet(w)
##    smallLeft = smallLeftAscentSet(w)
##    largeLeft = largeLeftAscentSet(w)
##    f.write('top (right)\n')
##    for i in range(1,n):
##        if i in smallRight:
##            x = 'S ' + str(w[i-1])
##        elif i in largeRight:
##            x = 'L'
##        else:
##            x = 'D'
##        f.write('s_' + str(i) + '\t' + x + '\n')
##    f.write('\nbottom (left)\n')
##    for i in range(1,n):
##        if i in smallLeft:
##            x = 'S'
##        elif i in largeLeft:
##            x = 'L'
##        else:
##            x = 'D'
##        f.write('s_' + str(i) + '\t' + x + '\n')
##    f.close()

# Draws the w-ocean
# Saves it to a postscript file named "(w(1), w(2), ..., w(n))-ocean.eps" if save == True
def drawOcean(w,save):
    turtle.clear()
    x = -500 # inital x-position
    y = 100 # initial y-position of top row
    r = 10 # inner vertex radius
    R = 15 # outer vertex radius (for large ascents)
    dx = int((1000 - (2*r*(N - 1)))/(N - 2)) # horizontal spacing between vertices
    # top row
    drawRow(x,y,dx,r,R,rightAscentSet(w),smallRightAscentSet(w),largeRightAscentSet(w))
    # bottom row
    drawRow(x,-y,dx,r,R,leftAscentSet(w),smallLeftAscentSet(w),largeLeftAscentSet(w))
    # drawing planks
    for i in smallRightAscentSet(w):
        turtle.setposition(-500 + dx*(i - 1) + r*(i - 1), y - r)
        turtle.down()
        turtle.setposition(-500 + dx*(w[i - 1] - 1) + r*(w[i - 1] - 1), r - y)
        turtle.up()
    turtle.hideturtle()
    # saving to postscript
    if save:
        ts = turtle.getscreen()
        ts.getcanvas().postscript(file=str(w)+'-ocean.eps')

# Draws a row of the w-ocean
# x = x-position of the left end of the row
# y = y-position of the row
# dx = horizontal spacing between vertices
# r = inner vertex radius
# R = outer vertex radius (for large ascents)
# rightAscent = right ascent set of w
# smallRight = small right ascent set of w
# largeRight = large right ascent set of w
def drawRow(x,y,dx,r,R,rightAscent,smallRight,largeRight):
    turtle.up()
    turtle.setposition(x,y)
    for i in range(1,N):
        # drawing inner circle
        turtle.setposition(x, y - r)
        turtle.down()
        turtle.circle(r)
        turtle.up()
        if i in largeRight:
            # drawing outer circle
            turtle.setposition(x, y - R)
            turtle.down()
            turtle.circle(R)
            turtle.up()
        elif i not in smallRight: # descent
            # drawing cross
            turtle.setposition(x - r, y + r)
            turtle.down()
            turtle.setposition(x + r, y - r)
            turtle.up()
            turtle.setposition(x - r, y - r)
            turtle.down()
            turtle.setposition(x + r, y + r)
            turtle.up()
        # updating position
        x = x + r
        turtle.setposition(x, y)
        # drawing horizontal line
        if ((i in smallRight) and (i + 1 in rightAscent)) or ((i in rightAscent) and (i + 1 in smallRight)):
            turtle.down()
        if i + 1 < N:
            x = x + dx
            turtle.setposition(x - r, y)
            turtle.up()
            turtle.setposition(x,y)
        turtle.up()

# Draws the w-ocean of every permutation in S_n and saves them to current directory
# (i.e. the same directory as PDC.py)
def draw_S(n):
    if n != N:
        set_N(n)
    for w in S(n):
        drawOcean(w,True)

# Returns the number of floats in the w-ocean
def num_floats(w):
    result = 0
    for i in range(1,N):
        if isLargeRightAscent(w,i):
            if i == 1 or not isSmallRightAscent(w, i - 1):
                if i + 1 == N or (not isSmallRightAscent(w, i + 1)):
                    result += 1
        if isLargeLeftAscent(w,i):
            if i == 1 or not isSmallLeftAscent(w, i - 1):
                if i + 1 == N or not isSmallLeftAscent(w, i + 1):
                    result += 1
    return result

# NOTE: negative indices will indicate indices in the BOTTOM row

# Returns the set of indices of floats of w
def floats(w):
    result = set()
    for i in range(1,N):
        if isLargeRightAscent(w,i):
            if i == 1 or not isSmallRightAscent(w, i - 1):
                if i + 1 == N or (not isSmallRightAscent(w, i + 1)):
                    result.add(i)
        if isLargeLeftAscent(w,i):
            if i == 1 or not isSmallLeftAscent(w, i - 1):
                if i + 1 == N or not isSmallLeftAscent(w, i + 1):
                    result.add(-1*i)
    return result

# Returns the set of rafts of w as a set of 4-tuples
# (a,b,w(a),w(b)) indicates there is a raft from s_a to s_b (in the top row)
# connecting to the raft from s_w(a) to s_w(b) (in the bottom row)
def rafts(w):
    result = set()
    l = list(smallRightAscentSet(w))
    l.sort()
    if len(l) == 0:
        return result
    a = l[0]
    for i in range(len(l) - 1):
        if i == len(l) - 1:
            result.add((a, l[i], w[a - 1], w[l[i] - 1]))
        elif l[i + 1] != l[i] + 1:
            result.add((a, l[i], w[a - 1], w[l[i] - 1]))
            a = l[i + 1]
    result.add((a, l[-1], w[a - 1], w[l[-1] - 1]))
    return result

# Returns the set of indices of right ropes of w
def rightRopes(w):
    result = set()
    for i in range(1,N):
        if isLargeRightAscent(w,i):
            if i == 1:
                if isSmallRightAscent(w, i + 1):
                    result.add(i)
            elif i == N - 1:
                if isSmallRightAscent(w, i - 1):
                    result.add(i)
            elif (isSmallRightAscent(w, i - 1) and (not isSmallRightAscent(w,i+1))) or ((not isSmallRightAscent(w,i-1)) and isSmallRightAscent(w,i+1)):
                result.add(i)
    return result

# Returns the set of indices of left ropes of w
def leftRopes(w):
    result = set()
    for i in range(1,N):
        if isLargeLeftAscent(w,i):
            if i == 1:
                if isSmallLeftAscent(w, i + 1):
                    result.add(-1*i)
            elif i == N - 1:
                if isSmallLeftAscent(w, i - 1):
                    result.add(-1*i)
            elif (isSmallLeftAscent(w,i-1) and not isSmallLeftAscent(w,i+1)) or (not isSmallLeftAscent(w,i-1) and isSmallLeftAscent(w,i+1)):
                result.add(-1*i)
    return result

# Returns the set of indices of ropes of w
def ropes(w):
    return rightRopes(w).union(leftRopes(w))
    
# Returns the set of indices of right tethers of w
def rightTethers(w):
    result = set()
    for i in range(2, N - 1):
        if isLargeRightAscent(w,i):
            if i + 1 < N and isSmallRightAscent(w, i + 1) and isSmallRightAscent(w, i - 1):
                result.add(i)
    return result

# Returns the set of indices of left tethers of w
def leftTethers(w):
    result = set()
    for i in range(2, N - 1):
        if isLargeLeftAscent(w,i):
            if i + 1 < N and isSmallLeftAscent(w, i + 1) and isSmallLeftAscent(w, i - 1):
                result.add(-1*i)
    return result

# Returns the set of indices of tethers of w
def tethers(w):
    return rightTethers(w).union(leftTethers(w))

# Returns the w-ocean as a 4-tuple of tuples
# First tuple contains rafts
# Second tuple contains floats
# Third tuple contains ropes
# Fourth tuple contains tethers
# Each tuple is sorted so that oceans will be comparable
def ocean(w):
    raft_list = list(rafts(w))
    raft_list.sort()
    float_list = list(floats(w))
    float_list.sort()
    rope_list = list(ropes(w))
    rope_list.sort()
    tether_list = list(tethers(w))
    tether_list.sort()
    return (tuple(raft_list), tuple(float_list), tuple(rope_list), tuple(tether_list))

# Returns the set of w-oceans in S_n
def oceans_S(n):
    if n != N:
        set_N(n)
    result = set()
    for w in S(n):
        result.add(ocean(w))
    return result

# Returns the set of duplicate w-oceans in S_n
# (w-oceans that belong to more than one permutation)
def duplicates(n):
    if n != N:
        set_N(n)
    result = set()
    duplicates = set()
    for w in S(n):
        o = ocean(w)
        if o in result:
            duplicates.add(o)
        result.add(o)
    return duplicates

# Returns a list ocean-permutation pairs (2-tuples)
# containing all duplicate w-oceans in S_n
# Prints the returned list if printing == true
# Saves the list to text file if save_text == true
# Saves w-ocean .eps files to current directory if save_pic == true
def duplicate_pairs(n,printing,save_text,save_pic):
    if n != N:
        set_N(n)
    result = list()
    d = duplicates(n)
    for w in S(n):
        o = ocean(w)
        if o in d:
            result.append((o,w))
            if save_pic:
                drawOcean(w,save)
    result.sort()
    if printing:
        for x in result:
            print(x)
    if save_text:
        f = open('S_' + str(n) + '_duplicate_pairs.txt','w')
        for x in result:
            f.write(str(x) + '\n')
    return result


        

###############
# c_w and p_n #
###############


# Boundary apparatus of the given raft R in the permutation w
# Returns a tuple (I,J,K,L) where I,J,K,L are in the set {0,1,10}
# 1 corresponds to an index in T (a particular subset of tethers(w))
# 10 corresponds to a rope
# 0 corresponds to anything else (a descent, an edge, or a tether not in T)
# I,J,K,L correspond to bottom left, top left, bottom right, and top right
# corners of the raft, respectively
def bd(w,ropeSet,T,R):
    I = J = K = L = 0
    if R[0] - 1 > 0:
        if -1*(w[R[0]-1] - 1) in ropeSet:
            I = 10
        elif -1*(w[R[0]-1] - 1) in T:
            I = 1
        if (R[0] - 1) in ropeSet:
            J = 10
        elif R[0] - 1 in T:
            J = 1
    if R[1] < N - 1:
        if -1*(w[R[1]-1] + 1) in ropeSet:
            K = 10
        elif -1*(w[R[1]-1] + 1) in T:
            K = 1
        if R[1] + 1 in ropeSet:
            L = 10
        elif R[1] + 1 in T:
            L = 1
    return (I,J,K,L)


# Returns c_w, the number of parabolic double cosets in S_n with
# minimal length element w
def c(w):
    result = 0
    for T in powerset(tethers(w)):
        product = 1
        for R in rafts(w):
            product *= b(bd_dict[bd(w,ropes(w),T,R)], R[1] - R[0] + 1)
        result += product
    return pow(2,num_floats(w))*result

# Prints c_w for each permutation w in S_n
def print_cw(n):
    if n != N:
        set_N(n)
    for w in S(n):
        print('c_' + str(w) + ' = ' + str(c(w)))
    
# Returns p_n, the number of parabolic double cosets in S_n
def p(n):
    if n != N:
        set_N(n)
    result = 0
    for w in S(n):
        result += c(w)
    return result

# Returns the set {w in S_n | c_w = k}
def cw_class(n,k):
    if n != N:
        set_N(n)
    result = set()
    for w in S(n):
        if c(w) == k:
            result.add(w)
    return result

# Returns p_n (uses WXML equivalence classes)
def p2(n):
    if n != N:
        set_N(n)
    WXML = dict()
    result = 0
    for w in S(n):
        if w not in WXML:
            WXML[w] = WXML[inverse(w)] = WXML[mult(w0,mult(w,w0))] = WXML[mult(w0,mult(inverse(w),w0))] = c(w)
        result += WXML[w]
    return result

# Returns p_n (uses duplicate oceans)
def p3(n):
    if n != N:
        set_N(n)
    OCEANS = dict()
    result = 0
    for w in S(n):
        o = ocean(w)
        if o not in OCEANS:
            OCEANS[o] = c(w)
        result += OCEANS[o]
    return result

# Returns p_n (uses duplicate oceans and WXML equivalence classes)
def p4(n):
    if n != N:
        set_N(n)
    OCEANS = dict()
    result = 0
    for w in S(n):
        o = ocean(w)
        if o not in OCEANS:
            OCEANS[o] = OCEANS[ocean(inverse(w))] = OCEANS[mult(w0,mult(w,w0))] = OCEANS[mult(w0,mult(inverse(w),w0))] = c(w)
        result += OCEANS[o]
    return result

# Test functions that time how long it takes to compute p_n
def test_p(n):
    for i in range(1,n + 1):
        start = time.time()
        result = p(i)
        end = time.time()
        print('p_' + str(i) + ' = '  + str(result) + '\t time elapsed: ' + str(end - start) + ' seconds')

def test_p2(n):
    for i in range(1,n + 1):
        start = time.time()
        result = p2(i)
        end = time.time()
        print('p_' + str(i) + ' = '  + str(result) + '\t time elapsed: ' + str(end - start) + ' seconds')

def test_p3(n):
    for i in range(1,n + 1):
        start = time.time()
        result = p3(i)
        end = time.time()
        print('p_' + str(i) + ' = '  + str(result) + '\t time elapsed: ' + str(end - start) + ' seconds')

def test_p4(n):
    for i in range(1,n + 1):
        start = time.time()
        result = p4(i)
        end = time.time()
        print('p_' + str(i) + ' = '  + str(result) + '\t time elapsed: ' + str(end - start) + ' seconds')
        
