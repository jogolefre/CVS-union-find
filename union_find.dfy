class UF {
    var size: nat
    var link: array<nat>
    var rank: array<nat>
    ghost var rep : seq<nat>

    var dst : array<nat>
    ghost var maxd : nat

    ghost predicate DFInv ()
      reads this
    {
        true
    }

    ghost predicate Valid ()
      reads this
    {
        link.Length == size &&
        rank.Length == size &&
        dst.Length == size &&
        (forall i :: 0 <= i < size ==> link[i] < size) &&
        (forall i :: 0 <= i < size ==> rep[i] < size && rep[rep[i]] == rep[i])
    }

    constructor (n: nat)
      ensures Valid()
    {
        link := new nat[n](i => i);
        size := n;
        rank := new nat[n](i => 0);

        var tmp := new nat[n](i => i);
        rep := tmp[..];

        dst := new nat[n](i => 0);
        maxd := 0;

        // Now that all fields are initialized, we can assert DFInv
        assert DFInv();
    }

    method{:isolate_assertions} findIt (x: nat) returns (r: nat)
      requires Valid()
      ensures Valid()
      ensures r == link[r] && rep[x] == rep[r]
    {
      var y := link[x];

      while (y != link[y])
      {
        y := link[y];
      }

      return y;
    }

    function findRep(x: nat): nat
      requires 0 <= x < size
      ensures link[findRep(x)] == findRep(x)
    {
      if (link[x] == x) then x else findRep(link[x])
    }

    method{:isolate_assertions} find (x: nat) returns (r: nat)
      requires Valid()
      ensures Valid()
      ensures r == link[r] && rep[x] == rep[r]
    {
      if (link[x] != x) {
        var parent := this.find(link[x]); // Store the result of the recursive call
        link[x] := parent; // Path compression
        return parent;
      }
      return link[x];
    }

    method{:isolate_assertions} same (x: nat, y: nat) returns (r: bool)
      requires Valid()
      ensures Valid()
      ensures r == (findRep(x) == findRep(y))
    {
      var a := find(x);
      var b := find(y);

      r := a == b;
    }

    function max(x: nat, y: nat) : nat
    {
      if (x <= y) then y
      else x
    }

    method Max(x: nat, y: nat) returns (r: nat)
      ensures r == max(x, y)
    {
      if (x <= y) { return y; }
      else { return x; }
    }

    function{:axiom} updateRep (rep: seq<nat>, r: nat, v: nat) : seq<nat>
      requires 0 <= r < |rep|
      ensures |rep| == |updateRep(rep, r, v)|
      ensures forall z : nat :: (z < |rep| && rep[z] == r) ==> updateRep(rep, r, v)[z] == v
      ensures forall z : nat :: (z < |rep| && rep[z] != r) ==> updateRep(rep, r, v)[z] == rep[z]

    method{:isolate_assertions} union (x: nat, y: nat) returns (ghost oldRep: nat)
      requires Valid()
      ensures Valid()
      ensures oldRep == findRep(x) || oldRep == findRep(y)
    {
      var rx := find(x);
      var ry := find(y);

      if (rx == ry) {
        return rx;
      }
      else {
        var rkx := rank[rx];
        var rky := rank[ry];
        var maxDst := Max(dst[rx], dst[ry]);

        if (rkx < rky) {
          link[rx] := ry;

          dst[ry] := 1 + maxDst;

          rep := updateRep(rep, rep[x], ry);
         
          maxd := maxd + 1;

          return ry;
        }
        else {
          link[ry] := rx;

          rep := updateRep(rep, rep[y], rx);

          dst[rx] := 1 + maxDst;

          maxd := maxd + 1;

          if (rkx == rky) { rank[rx] := rkx + 1; }
          else { }

          return rx;
        }
      }
    }
}
