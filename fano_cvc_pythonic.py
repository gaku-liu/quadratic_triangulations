import ast
import itertools
from cvc5.pythonic import *
import circuit

def quadratic_triangulation(vertices, indices, all_circuits, all_nonunimodular):
    d = len(vertices[0])
    pairs = list(itertools.combinations(indices,2))
    circuits = []
    for c in all_circuits:
        if all(i in indices for i in c[0]) and all(i in indices for i in c[1]): 
            circuits.append(c)
    nonunimodular = []
    for simplex in all_nonunimodular:
        if all(i in indices for i in simplex):
            nonunimodular.append(simplex)
    edge_classes = {}
    for (i,j) in pairs:
        sum = tuple([vertices[i][k] + vertices[j][k] for k in range(d)])
        if sum in edge_classes.keys():
            edge_classes[sum].append((i,j))
        else:
            edge_classes[sum] = [(i,j)]
    
    s = Solver()

    h = {}
    for i in indices:
        h[i] = Real(f"h_{i}")
    x = {}
    for e in pairs:
        x[e] = Bool(f"x_{e}")

    for edges in edge_classes.values():
        # Exactly one edge in the class
        s.add(Or(*[x[e] for e in edges]))
        for e1, e2 in itertools.combinations(edges, 2):
            s.add(Not(And(x[e1],x[e2])))

        # Chosen edge is minimum in edge class
        for (i,j) in edges:
            for (k,l) in edges:
                if (i,j) != (k,l):
                    s.add(Implies(x[i,j], h[i]+h[j]<h[k]+h[l]))

    # At least one missing edge in a part of each circuit.
    for c in circuits:
        edges1 = itertools.combinations(c[0],2)
        edges2 = itertools.combinations(c[1],2)
        edges = list(itertools.chain(edges1, edges2))
        s.add(Or(*[Not(x[e]) for e in edges]))
    
    # At least one missing edge in each nonunimodular simplex
    for simplex in nonunimodular:
        edges = list(itertools.combinations(simplex,2))
        s.add(Or(*[Not(x[e]) for e in edges]))

    status = s.check()
    if status == sat:
        print("Quadratic triangulation found")
        m = s.model()
        with open('heights_test.txt', 'w') as f:
            for i in indices:
                f.write(f"{vertices[i]}: " + str(m[h[i]]) + "\n")
    elif status == unsat:
        print("Proven no quadratic triangulation")
    else:
        print("Could not resolve")
    
    return status

def main0():
    vertices = [(0,0,0),(1,0,0),(0,1,0),(0,0,1),(1,1,0),(1,0,1),(0,1,1),(1,1,1)]
    indices = range(8)
    circuits = circuit.get_affine_circuits(vertices)
    nonunimodular = [(0,4,5,6),(1,2,3,7)]
    quadratic_triangulation(vertices, indices, circuits, nonunimodular)

def main():
    # In order, matroid elements are
    # 001, 010, 011, 100, 101, 110, 111
    fano = [(0,0,1),(0,1,0),(0,1,1),(1,0,0),(1,0,1),(1,1,0),(1,1,1)]

    # Creates the list of vertices. Vertices are stored as tuples.
    vertices = []
    for i in range(5):
        for j in range(i+1,6):
            for k in range(j+1,7):
                if not all((fano[i][t] + fano[j][t] + fano[k][t]) % 2 == 0 for t in range(3)):
                    vertex = [0] * 7
                    vertex[i] = 1
                    vertex[j] = 1
                    vertex[k] = 1
                    vertices.append(tuple(vertex))
    n = len(vertices)

    # minor is some subset of the vertices
    minor = [i for i in range(n) if vertices[i][0] == 0]
    # minor = range(n)

    # Reads all circuits and puts them in a list. Circuits are stored as (c[0], c[1]), where c[i] is
    # a tuple with all vertices in that part.
    circuits = []
    with open('circuitsFano.txt', 'r') as file:
        for line in file.readlines():
            circuit = ast.literal_eval(line)
            circuit = (tuple(sorted(circuit[0])), tuple(sorted(circuit[1])))
            circuits.append(circuit)

    # Stores all minimal nonunimodular simplices as tuples.
    nonunimodular = []
    with open('minimal_nonunimodular_simplices.txt', 'r') as file:
        for line in file.readlines():
            simplex = ast.literal_eval(line)
            nonunimodular.append(simplex)

    quadratic_triangulation(vertices, minor, circuits, nonunimodular)

if __name__ == "__main__":
    main()


    




