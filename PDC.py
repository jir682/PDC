# PDC.py
# Author: Jesse Rivera
# Last modified: 4/9/18
# A program for working with permutations in the symmetric group
# For use with the Washington Experimental Mathematics Lab (WXML)

# Recall: multiplying on the LEFT  permutes VALUES
#         multiplying on the RIGHT permutes POSITIONS
#         permutations are multiplied from RIGHT to LEFT

# TODO:
# w-ocean vertices need to be smaller for n > 20
# modify Heap's algorithm to generate parabolic subgroups or cosets?
# move turtle initialization to a function

import turtle # for drawing w-oceans
from tkinter import * # for saving w-oceans to postscript

turtle.setup(width=1200, height=600)
turtle.delay(0)
turtle.speed(0)

####################
# GLOBAL VARIABLES #
####################


# S_n, determines which symmetric group we will be working in
# (i.e. the size of the permutations)
n = 16

# Permutations in one-line notation represented as tuples (static but hashable)
# e = tuple(range(1,n + 1)) # the identity permutation

# examples for testing
# w = (3, 1, 4, 5, 2)
w = (1,3,4,5,7,8,2,6,14,15,16,9,10,11,12,13)
# w = (7,1,2,3,5,4,6)

# Set of adjacent transpositions (simple reflections)
# S = {1, 2, ..., n - 1} = {s_1, s_2, ..., s_n-1}
# adjacent_transpositions = set(range(1,n))

# Subsets of the simple reflection set S, represented as sets
I = set([1, 3, 4]) # examples for testing
J = set([2])

# Initial terms for the a-sequences
# A[k][m] returns the mth term of the sequence a^k, for 0 <= m <= 4
# Recall that 5 and 6 represent 2' and 2'' respectively
M = [[1,2,6,20,66], [1,3,9,28,89], [1,4,12,36,112], [1,4,14,46,148], [1,4,16,56,184], [1,3,11,37,119], [1,4,12,37,118]]

# Cache for the a-sequences, A[k][m] returns the mth term of the sequence a^k
A = [[0 for x in range(10000)] for y in range(7)]

# Initializing the initial terms for the a-sequences
for i in range(7):
    for j in range(5):
        A[i][j] = M[i][j]

# Maps the tuple (I,J,K,L) to the corresponding b-sequence (0 - 26)
dictionary = {(0,0,0,0) : 0,
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
N = [[1,2,6,20,66,214], [1,3,9,28,89,285,914], [1,3,11,37,119,380,1216], [1,4,12,36,112,356,1140], [1,4,12,37,118,379,1216],
     [1,4,14,46,148,474,1518], [1,4,16,56,184,592,1896], [2,5,15,48,155,499,1602], [2,6,20,65,208,665,2130], [2,7,21,64,201,641,2054],
     [2,7,21,65,207,664,2130], [2,7,25,83,267,854,2734], [2,8,26,82,260,830,2658], [2,8,26,83,266,853,2734], [2,8,30,102,332,1066,3414],
     [4,11,35,113,363,1164,3732], [4,12,36,112,356,1140,3656], [4,12,36,113,362,1163,3732], [4,14,46,147,468,1495,4788], [4,14,46,148,474,1518,4864],
     [4,15,47,147,467,1494,4788], [4,15,55,185,599,1920,6148], [4,16,56,184,592,1896,6072], [4,16,56,185,598,1919,6148], [8,26,82,260,830,2658,8520],
     [8,30,102,332,1066,3414,10936], [16,56,184,592,1896,6072,19456]]

# Initializing the initial terms for the b-sequences
for i in range(27):
    for j in range(6):
        B[i][j] = N[i][j]


###################
# BASIC FUNCTIONS #
###################


# Changes to the symmetric group S_n
# currently not working, and I don't know why
# def change_n(k):
#    global n
#    n = k
    
# Returns the reduced expression of w (w written as a product of adjacent transpositions)
#def reduced(w):

# Returns the inverse of the given permutation
def inverse(w):
    z = [0]*n
    for i in range(len(w)):
        z[i] = w.index(i + 1) + 1
    return tuple(z)

# Multiplies the given permutations in the order in which they are given
# Returns the product as a tuple
def mult(w,s):
    z = [0]*n
    for i in range(len(w)):
        z[i] = w[s[i] - 1]
    return tuple(z)

# Returns the length (number of inversions) of the given permutation
def length(w):
    count = 0
    for i in range(n):
        for j in range(i,n):
            if w[j] < w[i]:
                count += 1
    return count

# Returns the adjacent transposition s_k as a tuple
def s(k):
    z = list(range(1,n + 1))
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
    for i in range(n - 1):
        if isLeftAscent(w,i + 1):
            result.add(i + 1)
    return result

# Returns the right ascent set of the given permutation
def rightAscentSet(w):
    result = set()
    for i in range(n - 1):
        if isRightAscent(w,i + 1):
            result.add(i + 1)
    return result

# Returns the left descent set of the given permutation
def leftDescentSet(w):
    result = set()
    for i in range(n - 1):
        if isLeftDescent(w,i + 1):
            result.add(i + 1)
    return result

# Returns the right descent set of the given permutation
def rightDescentSet(w):
    result = set()
    for i in range(n - 1):
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
    return isLeftAscent(w,k) & (not isSmallLeftAscent(w,k))

# Returns whether the adjacent transposition s_k is a large right ascent of w
def isLargeRightAscent(w,k):
    return isRightAscent(w,k) & (not isSmallRightAscent(w,k))

# Returns the small left ascent set of w
def smallLeftAscentSet(w):
    result = set()
    for i in range(n - 1):
        if isSmallLeftAscent(w,i + 1):
            result.add(i + 1)
    return result

# Returns the small right ascent set of w
def smallRightAscentSet(w):
    result = set()
    for i in range(n - 1):
        if isSmallRightAscent(w,i + 1):
            result.add(i + 1)
    return result

# Returns the large left ascent set of w
def largeLeftAscentSet(w):
    result = set()
    for i in range(n - 1):
        if isLargeLeftAscent(w,i + 1):
            result.add(i + 1)
    return result

# Returns the large right ascent set of w
def largeRightAscentSet(w):
    result = set()
    for i in range(n - 1):
        if isLargeRightAscent(w,i + 1):
            result.add(i + 1)
    return result


################################
# MINIMAL AND MAXIMAL ELEMENTS #
################################

# Returns the minimal element in the right coset w*W_J
# Essentially a bubble sort, O(|J|^2) time complexity
def minimalRight(w,J):
    aux = list.copy(list(w)) # auxiliary storage, as to not modify w
    z = list.copy(list(w))
    for i in range(len(J)):
        for j in J:
            if z[j - 1] > z[j]:
                z[j - 1] = aux[j]
                z[j] = aux[j - 1]
                # updating aux
                aux[j - 1] = z[j - 1]
                aux[j] = z[j]
    return tuple(z)

# Returns the minimal element in the left coset W_I*w
# O(|I|^2) time complexity
def minimalLeft(w,I):
    aux = list.copy(list(w)) # auxiliary storage, as to not modify w
    z = list.copy(list(w))
    for j in range(len(I)):
        for i in I:
            if aux.index(i) > aux.index(i + 1):
                z[aux.index(i)] = i + 1
                z[aux.index(i + 1)] = i
                # updating aux
                aux[aux.index(i)] = z[aux.index(i)]
                aux[aux.index(i + 1)] = z[aux.index(i + 1)]
    return tuple(z)

# Returns the minimal element in the parabolic double coset W_I*w*W_J
def minimal(I,w,J):
    z = minimalLeft(w,I)
    z = minimalRight(z,J)
    return z

# Returns the maximal element in the right coset w*W_J
# Essentially a bubble sort, O(|J|^2) time complexity
def maximalRight(w,J):
    aux = list.copy(list(w)) # auxiliary storage, as to not modify w
    z = list.copy(list(w))
    for i in range(len(J)):
        for j in J:
            if z[j - 1] < z[j]:
                z[j - 1] = aux[j]
                z[j] = aux[j - 1]
                # updating aux
                aux[j - 1] = z[j - 1]
                aux[j] = z[j]
    return tuple(z)

# Returns the maximal element in the left coset W_I*w
# O(|I|^2) time complexity
def maximalLeft(w,I):
    aux = list.copy(list(w)) # auxiliary storage, as to not modify w
    z = list.copy(list(w))
    for j in range(len(I)):
        for i in I:
            if aux.index(i + 1) > aux.index(i):
                z[aux.index(i + 1)] = i
                z[aux.index(i)] = i + 1
                # updating aux
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
    return (minimal(I,w,J) == minimal(K,z,L)) & (maximal(I,w,J) == maximal(K,z,L))


###############################
# A-SEQUENCES AND B-SEQUENCES #
###############################


# Returns which of the seven symmetry types correspond to the given boundary apparatus
# 5 and 6 represent 2' and 2'' respectively
# The input i,j,k,l are in {0,1} and represent the whether or not the lower left,
# upper left, lower right, upper right boundaries are filled in
def K(i,j,k,l):
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
    
# Implement the recurrence for k = 0,1,2,3,4 (excluding 2',2'') for efficiency?
# It would be barely faster, probably not worth the trouble

# Returns the mth term of the a-sequence for the boundary apparatus (i,j,k,l)
def a2(i,j,k,l,m):
    x = K(i,j,k,l)
    return a(x,m)

# Prints the first n terms of the sequence a^k
def print_a(k,n):
    for i in range(n):
        print(a(k,i))

# Returns the mth term of the b-sequence for k = (I,J,K,L)
# I,J,K,L are in {0,1,10}, where 0 represents {0}, 1 represents {1}, and 10 represents {0,1}
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
# Could use some optimizing
def subgroup(I):
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

# Returns the parabolic double coset W_IwW_J as a set
def PDC(W_I,w,W_J):
    result = set([w])
    for x in W_I:
        for y in W_J:
            result.add(mult(mult(x,w),y))
    for y in W_J:
        result.add(mult(w,y))
    return set(result)

# Returns the symmetric group S_n as a set, using Heap's algorithm (recursive)
def S(k):
    result = set()
    generate(k,list(range(1,n + 1)),result)
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
def oceanText(w):
    f = open(str(w) + '-ocean.txt','w')
    smallRight = smallRightAscentSet(w)
    largeRight = largeRightAscentSet(w)
    smallLeft = smallLeftAscentSet(w)
    largeLeft = largeLeftAscentSet(w)
    f.write('top (right)\n')
    for i in range(1,n):
        if i in smallRight:
            x = 'S ' + str(w[i-1])
        elif i in largeRight:
            x = 'L'
        else:
            x = 'D'
        f.write('s_' + str(i) + '\t' + x + '\n')
    f.write('\nbottom (left)\n')
    for i in range(1,n):
        if i in smallLeft:
            x = 'S'
        elif i in largeLeft:
            x = 'L'
        else:
            x = 'D'
        f.write('s_' + str(i) + '\t' + x + '\n')
    f.close()

# Draws w-ocean and saves it to a postscript file named "(w(1), w(2), ..., w(n))-ocean.eps"
def drawOcean(w):
    turtle.clear()
    # turtle.screensize(1200,300)
    x = -500 # inital x-position
    y = 100 # initial y-position of top row
    r = 10 # inner radius 5,10
    R = 15 # outer radius 10,15
    dx = int((1000 - (2*r*(n - 1)))/(n - 2)) # horizontal spacing between vertices
    # top row
    drawRow(x,y,dx,r,R,rightAscentSet(w),smallRightAscentSet(w),largeRightAscentSet(w))
    # bottom row
    drawRow(x,-y,dx,r,R,leftAscentSet(w),smallLeftAscentSet(w),largeLeftAscentSet(w))
    # drawing planks
    for i in smallRightAscentSet(w):
        turtle.setposition(-500 + dx*(i - 1) + r*(i - 1), y - r)
        turtle.down()
        turtle.setposition(-500 + dx*(w[i-1] - 1) + r*(w[i-1] - 1), r - y)
        turtle.up()
    turtle.hideturtle()
    # saving to postscript
    ts = turtle.getscreen()
    ts.getcanvas().postscript(file=str(w)+'-ocean.eps')

# Draws a row of the w-ocean
# x = x-position of the left end of the row
# y = y-position of the row
# dx = horizontal spacing between vertices
# r = inner radius
# R = outer radius (for large ascents)
# rightAscent = right ascent set of w
# smallRight = small right ascent set of w
# largeRight = large right ascent set of w
def drawRow(x,y,dx,r,R,rightAscent,smallRight,largeRight):
    turtle.up()
    turtle.setposition(x,y)
    for i in range(1,n):
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
        x = x + r
        turtle.setposition(x, y)
        if ((i in smallRight) and (i + 1 in rightAscent)) or ((i in rightAscent) and i + 1 in smallRight):
            turtle.down()
        if i + 1 < n:
            x = x + dx
            turtle.setposition(x - r, y)
            turtle.up()
            turtle.setposition(x,y)
        turtle.up()

# Draws the w-ocean of every permutation in S_n
def drawS(k):
    global n
    n = k
    for w in S(k):
        drawOcean(w)
