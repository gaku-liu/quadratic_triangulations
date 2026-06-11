import numpy as np
import itertools

def preprocess(arrangement, affine=True):
    if affine:
        vectors = []
        for p in arrangement:
            v = list(p)
            v.append(1)
            vectors.append(v)
    else:
        vectors = arrangement
    
    M = np.transpose(np.array(vectors))
    d,n = M.shape
    r = np.linalg.matrix_rank(M)

    independent = {():True}
    circuits = []

    for k in range(1,r+2):
        for S in itertools.combinations(range(n),k):
            if not all(independent[T] for T in itertools.combinations(S,k-1)):
                independent[S] = False
            else:
                N = M[:,S]
                if np.linalg.matrix_rank(N) == k:
                    independent[S] = True
                else:
                    independent[S] = False
                    row = [0]*k
                    row[0] = 1
                    b = [0]*d
                    b.append(1)
                    A = np.append(N, [row], axis=0)
                    x = np.linalg.lstsq(A,b,rcond=None)[0]
                    c = []
                    c.append(tuple([S[i] for i in range(k) if x[i] > 0]))
                    c.append(tuple([S[i] for i in range(k) if x[i] < 0]))
                    assert len(c[0]) + len(c[1]) == k
                    circuits.append(c)

    return circuits

def fano():
    # In order, matroid elements are
    # 001, 010, 011, 100, 101, 110, 111
    fano = [(0,0,1),(0,1,0),(0,1,1),(1,0,0),(1,0,1),(1,1,0),(1,1,1)]

    # Creates the list of vertices. Vertices are stored as tuples.
    vertices = []
    for i,j,k in itertools.combinations(range(7),3):
        if not all((fano[i][t] + fano[j][t] + fano[k][t]) % 2 == 0 for t in range(3)):
            vertex = [0] * 7
            vertex[i] = 1
            vertex[j] = 1
            vertex[k] = 1
            vertices.append(tuple(vertex))
    
    return vertices

def uniform(n, r):
    bases = itertools.combinations(range(n),r)
    vertices = []
    for b in bases:
        v = [0] * n
        for i in b:
            v[i] = 1
        vertices.append(tuple(v))
    return vertices


def main():
    points = fano()
    circuits = preprocess(points)
    print(len(circuits))

if __name__ == "__main__":
    main()