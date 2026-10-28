module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.Setup

/-!
# Literal Schreier words for the ATLAS M2 subgroup

The 36-vertex table guides the choice of words only. Each edge is the literal
word rho(i) * a_or_b * rho(j)^-1 in the original two generators. Its rewritten
source loops are valid by telescoping once the endpoint and inverse checks in
`SchreierLifting` are proved. No coset-table faithfulness is assumed here.

Source: ATLAS `S62G1-P1.M`, M2; see `source/README.md` for extraction provenance.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound
open Subgroup.CosetWordCertificate

abbrev Vertex := Fin 36
abbrev Edge := Vertex × Bool

def sourceWord (i : Fin 7) : Word Bool :=
  match i.val with
  | 0 => [(false, true), (false, true)]
  | 1 => [(true, true), (true, true), (true, true), (true, true), (true, true), (true, true), (true, true)]
  | 2 => [(false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)]
  | 3 => [(false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true)]
  | 4 => [(false, false), (true, false), (false, false), (true, false), (false, false), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, false), (true, false), (false, false), (true, false), (false, false), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)]
  | 5 => [(false, false), (true, false), (false, true), (true, true), (false, false), (true, false), (false, true), (true, true), (false, false), (true, false), (false, true), (true, true)]
  | _ => [(false, false), (true, false), (true, false), (false, true), (true, true), (true, true), (false, false), (true, false), (true, false), (false, true), (true, true), (true, true)]

def representativeWord (i : Fin 36) : Word Bool :=
  match i.val with
  | 0 => []
  | 1 => [(true, true)]
  | 2 => [(true, false)]
  | 3 => [(true, true), (false, true)]
  | 4 => [(true, true), (true, true)]
  | 5 => [(true, false), (false, true)]
  | 6 => [(true, false), (true, false)]
  | 7 => [(true, true), (false, true), (true, false)]
  | 8 => [(true, true), (true, true), (false, true)]
  | 9 => [(true, false), (false, true), (true, true)]
  | 10 => [(true, false), (false, true), (true, false)]
  | 11 => [(true, true), (false, true), (true, false), (false, true)]
  | 12 => [(true, true), (true, true), (false, true), (true, true)]
  | 13 => [(true, true), (true, true), (false, true), (true, false)]
  | 14 => [(true, false), (false, true), (true, true), (false, true)]
  | 15 => [(true, false), (false, true), (true, true), (true, true)]
  | 16 => [(true, false), (false, true), (true, false), (false, true)]
  | 17 => [(true, false), (false, true), (true, false), (true, false)]
  | 18 => [(true, true), (false, true), (true, false), (false, true), (true, true)]
  | 19 => [(true, true), (false, true), (true, false), (false, true), (true, false)]
  | 20 => [(true, true), (true, true), (false, true), (true, true), (true, true)]
  | 21 => [(true, true), (true, true), (false, true), (true, false), (true, false)]
  | 22 => [(true, false), (false, true), (true, true), (false, true), (true, true)]
  | 23 => [(true, false), (false, true), (true, true), (false, true), (true, false)]
  | 24 => [(true, false), (false, true), (true, true), (true, true), (true, true)]
  | 25 => [(true, false), (false, true), (true, false), (false, true), (true, true)]
  | 26 => [(true, false), (false, true), (true, false), (false, true), (true, false)]
  | 27 => [(true, false), (false, true), (true, false), (true, false), (false, true)]
  | 28 => [(true, false), (false, true), (true, false), (true, false), (true, false)]
  | 29 => [(true, true), (false, true), (true, false), (false, true), (true, true), (true, true)]
  | 30 => [(true, true), (true, true), (false, true), (true, true), (true, true), (true, true)]
  | 31 => [(true, true), (true, true), (false, true), (true, false), (true, false), (true, false)]
  | 32 => [(true, false), (false, true), (true, true), (false, true), (true, false), (true, false)]
  | 33 => [(true, false), (false, true), (true, false), (true, false), (false, true), (true, false)]
  | 34 => [(true, true), (false, true), (true, false), (false, true), (true, true), (true, true), (true, true)]
  | _ => [(true, false), (false, true), (true, true), (false, true), (true, false), (true, false), (false, true)]

def stepA (i : Fin 36) : Vertex :=
  match i.val with
  | 0 => 0
  | 1 => 3
  | 2 => 5
  | 3 => 1
  | 4 => 8
  | 5 => 2
  | 6 => 6
  | 7 => 11
  | 8 => 4
  | 9 => 14
  | 10 => 16
  | 11 => 7
  | 12 => 12
  | 13 => 13
  | 14 => 9
  | 15 => 20
  | 16 => 10
  | 17 => 27
  | 18 => 18
  | 19 => 19
  | 20 => 15
  | 21 => 21
  | 22 => 22
  | 23 => 23
  | 24 => 24
  | 25 => 25
  | 26 => 26
  | 27 => 17
  | 28 => 28
  | 29 => 29
  | 30 => 33
  | 31 => 31
  | 32 => 35
  | 33 => 30
  | 34 => 34
  | _ => 32

def stepAInv (i : Fin 36) : Vertex :=
  match i.val with
  | 0 => 0
  | 1 => 3
  | 2 => 5
  | 3 => 1
  | 4 => 8
  | 5 => 2
  | 6 => 6
  | 7 => 11
  | 8 => 4
  | 9 => 14
  | 10 => 16
  | 11 => 7
  | 12 => 12
  | 13 => 13
  | 14 => 9
  | 15 => 20
  | 16 => 10
  | 17 => 27
  | 18 => 18
  | 19 => 19
  | 20 => 15
  | 21 => 21
  | 22 => 22
  | 23 => 23
  | 24 => 24
  | 25 => 25
  | 26 => 26
  | 27 => 17
  | 28 => 28
  | 29 => 29
  | 30 => 33
  | 31 => 31
  | 32 => 35
  | 33 => 30
  | 34 => 34
  | _ => 32

def stepB (i : Fin 36) : Vertex :=
  match i.val with
  | 0 => 1
  | 1 => 4
  | 2 => 0
  | 3 => 6
  | 4 => 7
  | 5 => 9
  | 6 => 2
  | 7 => 3
  | 8 => 12
  | 9 => 15
  | 10 => 5
  | 11 => 18
  | 12 => 20
  | 13 => 8
  | 14 => 22
  | 15 => 24
  | 16 => 25
  | 17 => 10
  | 18 => 29
  | 19 => 11
  | 20 => 30
  | 21 => 13
  | 22 => 26
  | 23 => 14
  | 24 => 28
  | 25 => 32
  | 26 => 16
  | 27 => 19
  | 28 => 17
  | 29 => 34
  | 30 => 31
  | 31 => 21
  | 32 => 23
  | 33 => 27
  | 34 => 33
  | _ => 35

def stepBInv (i : Fin 36) : Vertex :=
  match i.val with
  | 0 => 2
  | 1 => 0
  | 2 => 6
  | 3 => 7
  | 4 => 1
  | 5 => 10
  | 6 => 3
  | 7 => 4
  | 8 => 13
  | 9 => 5
  | 10 => 17
  | 11 => 19
  | 12 => 8
  | 13 => 21
  | 14 => 23
  | 15 => 9
  | 16 => 26
  | 17 => 28
  | 18 => 11
  | 19 => 27
  | 20 => 12
  | 21 => 31
  | 22 => 14
  | 23 => 32
  | 24 => 15
  | 25 => 16
  | 26 => 22
  | 27 => 33
  | 28 => 24
  | 29 => 18
  | 30 => 20
  | 31 => 30
  | 32 => 25
  | 33 => 34
  | 34 => 29
  | _ => 35

def step (i : Vertex) (a : Letter Bool) : Vertex :=
  match a with
  | (false, true) => stepA i
  | (false, false) => stepAInv i
  | (true, true) => stepB i
  | (true, false) => stepBInv i

def endpoint : Vertex → Word Bool → Vertex
  | i, [] => i
  | i, a :: w => endpoint (step i a) w

/-- Each inverse edge uses the inverse of the positive edge at its destination. -/
def rewrite : Vertex → Word Bool → Word Edge
  | _, [] => []
  | i, a :: w =>
      ((if a.2 then i else step i a, a.1), a.2) :: rewrite (step i a) w

def edgeWord (e : Edge) : Word Bool :=
  representativeWord e.1 ++ [(e.2, true)] ++
    FreeGroup.invRev (representativeWord (step e.1 (e.2, true)))

def treeEdge (i : Fin 35) : Edge :=
  match i.val with
  | 0 => (0, true)
  | 1 => (2, true)
  | 2 => (1, false)
  | 3 => (1, true)
  | 4 => (2, false)
  | 5 => (6, true)
  | 6 => (7, true)
  | 7 => (4, false)
  | 8 => (5, true)
  | 9 => (10, true)
  | 10 => (7, false)
  | 11 => (8, true)
  | 12 => (13, true)
  | 13 => (9, false)
  | 14 => (9, true)
  | 15 => (10, false)
  | 16 => (17, true)
  | 17 => (11, true)
  | 18 => (19, true)
  | 19 => (12, true)
  | 20 => (21, true)
  | 21 => (14, true)
  | 22 => (23, true)
  | 23 => (15, true)
  | 24 => (16, true)
  | 25 => (26, true)
  | 26 => (17, false)
  | 27 => (28, true)
  | 28 => (18, true)
  | 29 => (20, true)
  | 30 => (31, true)
  | 31 => (32, true)
  | 32 => (33, true)
  | 33 => (29, true)
  | _ => (32, false)

abbrev RelatorIndex := (Vertex × Fin 7) ⊕ Fin 35

/-- The only relations are rewritten source loops and the spanning-tree edges. -/
def rawRelator : RelatorIndex → Word Edge
  | .inl (i, r) => rewrite i (sourceWord r)
  | .inr k => [(treeEdge k, true)]

def RawPresentation := PresentedGroup (Set.range (fun i => FreeGroup.mk (rawRelator i)))

instance : Group RawPresentation := inferInstanceAs (Group (PresentedGroup _))

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound
