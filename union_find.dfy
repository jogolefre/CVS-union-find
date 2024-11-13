class UF {
    var size: nat
    var link: array<nat>
    var rank: array<nat>
    ghost var rep: seq<nat>

    var dst: array<nat>
    ghost var maxd: nat

    ghost predicate LinkValid()
        reads this, link
    {
        link.Length == size &&
        (forall i :: 0 <= i < size ==> link[i] < size)
    }

    ghost predicate RepValid()
        reads this
    {
        |rep| == size &&
        (forall i :: 0 <= i < size ==> rep[i] < size && rep[rep[i]] == rep[i])
    }

    ghost predicate Valid()
        reads this, link, rank, dst
    {
        LinkValid() &&
        RepValid() &&
        rank.Length == size &&
        dst.Length == size
    }

    constructor(n: nat)
        ensures Valid()
    {
        link := new nat[n](i => i);
        size := n;
        rank := new nat[n](i => 0);

        rep := seq(n, i => i);

        dst := new nat[n](i => 0);
        maxd := 0;
    }

    method{:isolate_assertions} findIt(x: nat) returns (r: nat)
        requires Valid() && 0 <= x < size
        ensures Valid()
        ensures 0 <= r < size && r == link[r] && rep[x] == rep[r]
        decreases size - x
        modifies link
    {
        var y := link[x];

        while (y != link[y])
            invariant 0 <= y < size
            invariant Valid()
            decreases size - y
        {
            y := link[y];
        }

        return y;
    }

    function findRep(x: nat): nat
        requires 0 <= x < size
        ensures link[findRep(x)] == findRep(x)
    {
        if link[x] == x then x else findRep(link[x])
    }

    method{:isolate_assertions} find(x: nat) returns (r: nat)
        requires Valid() && 0 <= x < size
        ensures Valid()
        ensures 0 <= r < size && r == link[r] && rep[x] == rep[r]
        decreases if link[x] == x then 0 else size - x
        modifies link
    {
        if link[x] != x {
            var parent := this.find(link[x]);
            link[x] := parent; // Path compression
            return parent;
        }
        return link[x];
    }

    method{:isolate_assertions} same(x: nat, y: nat) returns (r: bool)
        requires Valid() && 0 <= x < size && 0 <= y < size
        ensures Valid()
        ensures r == (findRep(x) == findRep(y))
        modifies link
    {
        var a := find(x);
        var b := find(y);

        r := a == b;
    }

    function max(x: nat, y: nat): nat {
        if x <= y then y else x
    }

    method Max(x: nat, y: nat) returns (r: nat)
        ensures r == max(x, y)
    {
        if x <= y {
            return y;
        } else {
            return x;
        }
    }

    function updateRep(rep: seq<nat>, r: nat, v: nat): seq<nat>
        requires 0 <= r < |rep|
        ensures |rep| == |updateRep(rep, r, v)|
        ensures forall z: nat :: (z < |rep| && rep[z] == r) ==> updateRep(rep, r, v)[z] == v
        ensures forall z: nat :: (z < |rep| && rep[z] != r) ==> updateRep(rep, r, v)[z] == rep[z]
    {
        rep[0..r] + [v] + rep[r+1..]
    }

    ghost method updateRepGhost(x: nat, y: nat)
        requires Valid() && 0 <= x < size && 0 <= y < size
    {
        if 0 <= x < size && 0 <= rep[x] < size {
            rep := updateRep(rep, x, y);
        }
    }

    method{:isolate_assertions} union(x: nat, y: nat) returns (ghost oldRep: nat)
        requires Valid() && 0 <= x < size && 0 <= y < size
        ensures Valid()
        ensures oldRep == findRep(x) || oldRep == findRep(y)
        modifies this, link, rank, dst
    {
        var rx := find(x);
        var ry := find(y);

        if rx == ry {
            return rx;
        } else {
            var rkx := if 0 <= rx < size then rank[rx] else 0;
            var rky := if 0 <= ry < size then rank[ry] else 0;
            var maxDst := Max(dst[rx], dst[ry]);

            if rkx < rky {
                link[rx] := ry;
                dst[ry] := 1 + maxDst;
                if 0 <= x < size {
                    updateRepGhost(x, ry); // Update rep indirectly using ghost method
                }
                maxd := maxd + 1;
                return ry;
            } else {
                link[ry] := rx;
                dst[rx] := 1 + maxDst;
                if 0 <= y < size {
                    updateRepGhost(y, rx); // Update rep indirectly using ghost method
                }
                maxd := maxd + 1;

                if rkx == rky {
                    rank[rx] := rkx + 1;
                }

                return rx;
            }
        }
    }
}
