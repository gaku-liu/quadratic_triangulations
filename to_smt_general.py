import itertools
from triangulation_tools import preprocess, fano

def x_name(e):
    i, j = e
    return f"x_{i}_{j}"

def h_name(i):
    return f"h_{i}"

def write_not_all_true(f, edge_list, comment=None):
    """
    Encode: not all variables in edge_list are true.
    This is equivalent to:
        sum x[e] <= len(edge_list)-1
    when x[e] are Booleans.
    """
    if comment:
        f.write(f"; {comment}\n")
    if not edge_list:
        return
    lits = " ".join(f"(not {x_name(e)})" for e in edge_list)
    f.write(f"(assert (or {lits}))\n")


def make_smt_script(points, write_to="test.smt2", dump_model=False, dump_proof=False):
    n = len(points)
    d = len(points[0])

    # Creates the list of pairs of vertices. Pairs are stored as (i,j) where i < j.
    pairs = list(itertools.combinations(range(n), 2))

    # Partitions pairs into equivalence classes depending on the sum of the vertices.
    edge_classes = {}
    for (i, j) in pairs:
        s = tuple(points[i][k] + points[j][k] for k in range(d))
        if s in edge_classes:
            edge_classes[s].append((i, j))
        else:
            edge_classes[s] = [(i, j)]

    circuits = preprocess(points)


    with open(write_to, "w") as f:
        # Header
        f.write("(set-logic QF_LRA)\n")
        f.write("(set-option :produce-models true)\n")
        f.write("(set-option :produce-proofs true)\n")
        if dump_model:
            f.write("(set-option :dump-models true)\n")
        if dump_proof:
            f.write("(set-option :dump-proofs true)\n")
        f.write("\n")

        # Variable declarations
        f.write("; Real variables h_i\n")
        for i in range(n):
            f.write(f"(declare-const {h_name(i)} Real)\n")
        f.write("\n")

        f.write("; Boolean variables x_(i,j)\n")
        for e in pairs:
            f.write(f"(declare-const {x_name(e)} Bool)\n")
        f.write("\n")

        # Edge class constraints
        f.write("; At least one edge from each edge class is chosen\n")
        for cl, edges in edge_classes.items():
            edge_vars = " ".join(x_name(e) for e in edges)
            f.write(f"; edge class {cl}\n")
            f.write(f"(assert (or {edge_vars}))\n")
        f.write("\n")

        # Indicator constraints
        f.write("; If x_(i,j) is chosen, then h_i + h_j is smallest in its edge class\n")
        for edges in edge_classes.values():
            for (i, j) in edges:
                for (k, l) in edges:
                    if (i, j) != (k, l):
                        f.write(
                            f"(assert (=> {x_name((i, j))} "
                            f"(< (+ {h_name(i)} {h_name(j)}) (+ {h_name(k)} {h_name(l)}) )))\n"
                        )
        f.write("\n")

        # Flag constraints
        f.write("; Flag constraints: every circuit has a missing edge within a part\n")
        for c in circuits:
            edges1 = itertools.combinations(c[0], 2)
            edges2 = itertools.combinations(c[1], 2)
            edges = itertools.chain(edges1, edges2)
            write_not_all_true(f, edges, comment=f"circuit {c}")
        f.write("\n")

        # Final commands
        f.write("(check-sat)\n")
    
    print(f"Wrote {write_to}")
    print(f"Vertices: {n}")
    print(f"Pairs: {len(pairs)}")
    print(f"Edge classes: {len(edge_classes)}")
    print(f"Circuits: {len(circuits)}")

def small_test():
    vertices = [(0,0,0),(1,0,0),(0,1,0),(0,0,1),(1,1,0),(1,0,1),(0,1,1),(1,1,1)]
    indices = (0,4,5,6,7)
    points = [vertices[i] for i in indices]
    make_smt_script(points)

def main():
    vertices = fano()
    make_smt_script(vertices, write_to="fano.smt2", dump_proof=True)

    #minor = [v for v in vertices if v[0]==0]
    #make_smt_script(minor)

    #small_test()

if __name__ == "__main__":
    main()
