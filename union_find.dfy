class UF {
    var size: nat
    var link: array<nat>
    var rank: array<nat>
    ghost var rep: seq<nat>

    var dst: array<nat>
    ghost var maxd: nat

    ghost predicate LinkValid() reads this, link {
        link.Length == size &&
        (forall i :: 0 <= i < size ==> link[i] < size)
    }

    ghost predicate RepValid() reads this {
        |rep| == size &&
        (forall i :: 0 <= i < size ==> rep[i] < size && (0 <= rep[rep[i]] < size ==> rep[rep[i]] == rep[i]))
    }

    ghost predicate Valid() reads this, link, rank, dst {
        LinkValid() &&
        RepValid() &&
        rank.Length == size &&
        dst.Length == size &&
        (forall i :: 0 <= i < size && i != link[i] ==> dst[i] < dst[link[i]]) &&
        (forall i :: 0 <= i < size ==> dst[i] <= maxd)
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
        ensures LinkValid()
        decreases dst[x]
        ensures 0 <= r < size && r == link[r]
        decreases dst[x], link[x]
        modifies link
        requires forall i :: 0 <= i < size && link[i] == i ==> rep[i] == i

    {
        var y := link[x];
        synchronizeRep();
        while (y != link[y])
            invariant 0 <= y < size
            invariant Valid()
            invariant dst[y] >= 0
            invariant dst[y] >= dst[x]
            invariant forall i :: 0 <= i < size && link[i] == i ==> rep[i] == i
            invariant forall i :: 0 <= i < size && i != link[i] ==> dst[i] < dst[link[i]]


            invariant dst[y] <= maxd

            invariant size - (if dst[y] < size then dst[y] else size - 1) >= 0
            decreases size - (if dst[y] < size then dst[y] else size - 1)
        {
            y := link[y];
        }
        r := y;
    }

    ghost method synchronizeRep()
        requires Valid()
        modifies this`rep
    {
        rep := seq(size, i => link[i]); // Update rep to match link
    }


    method{:isolate_assertions} find(x: nat) returns (r: nat)
        requires Valid() && 0 <= x < size
        ensures Valid()
        ensures LinkValid()
        decreases dst[x], size, x
        ensures 0 <= r < size && r == link[r]
        decreases size - (if dst[x] < size then dst[x] else size - 1)
        modifies link
    {
        if link[x] != x {
            var parent := this.find(link[x]);
            link[x] := parent;
            updateRepGhost(x, parent);
            r := parent;
        } else {
            r := link[x];
        }
        assert forall i :: 0 <= i < size && i != link[i] ==> dst[i] < dst[link[i]];
        assert forall i :: 0 <= i < size ==> dst[i] <= maxd;
        assert LinkValid();
        assert Valid();
    }

    method{:isolate_assertions} union(x: nat, y: nat) returns (ghost oldRep: nat)
        requires Valid() && 0 <= x < size && 0 <= y < size
        ensures Valid()
        ensures LinkValid()
        modifies this, link, rank, dst, this`rep
    {
        var rx := find(x);
        var ry := find(y);

        if rx == ry {
            oldRep := rx;
            return;
        } else {
            var rkx := rank[rx];
            var rky := rank[ry];
            var maxDst := if dst[rx] > dst[ry] then dst[rx] else dst[ry];

            if rkx < rky {
                link[rx] := ry;
                dst[rx] := maxDst + 1;
                dst[ry] := maxDst + 1;
                maxd := if maxd > dst[rx] then maxd else dst[rx];
                oldRep := ry;
            } else {
                link[ry] := rx;
                dst[ry] := maxDst + 1;
                dst[rx] := maxDst + 1;
                maxd := if maxd > dst[ry] then maxd else dst[ry];
                if rkx == rky {
                    rank[rx] := rkx + 1;
                }
                oldRep := rx;
            }
        }
    }

    ghost method updateRepGhost(x: nat, y: nat)
        requires Valid() && 0 <= x < size && 0 <= y < size
        modifies this`rep
    {
        rep := updateRep(rep, x, y);
    }

    function updateRep(rep: seq<nat>, r: nat, v: nat): seq<nat>
        requires 0 <= r < |rep|
        requires |rep| > 0
        ensures |rep| == |updateRep(rep, r, v)|
        ensures forall z :: 0 <= z < |rep| && rep[z] == r ==> updateRep(rep, r, v)[z] == v
        ensures forall z :: 0 <= z < |rep| && rep[z] != r ==> updateRep(rep, r, v)[z] == rep[z]
    {
        if r == 0 then
            assert forall z :: 1 <= z < |rep| ==> rep[z] == ([v] + rep[1..])[z];
            [v] + rep[1..]
        else if r == |rep| - 1 then
            assert forall z :: 0 <= z < r ==> rep[z] == (rep[0..r] + [v])[z];
            rep[0..r] + [v]
        else
            assert forall z :: 0 <= z < r ==> rep[z] == (rep[0..r] + [v] + rep[r+1..])[z];
            assert forall z :: r + 1 <= z < |rep| ==> rep[z] == (rep[0..r] + [v] + rep[r+1..])[z];
            rep[0..r] + [v] + rep[r+1..]

    }


}