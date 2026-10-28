module

public import Theory.SpecificGroups.ReeTwo.TailQuotientOrder16Nodes

/-!
# Word certificates identifying the noncore order-sixteen nodes

The eighteen rows are the quotient generators of the fifteen residual and
three exceptional root-based representatives, in that order. The twenty-six
remaining nodes are obtained by conjugating these rows. Membership of every
conjugated generator and word expressions for every node generator prove both
containments. All finite equations are checked by kernel reduction.

Source: direct calculation in the Shinoda tail quotient defined in
`SylowTailQuotient`; externally computed words are only proof witnesses.
-/

namespace ReeTwo.TailQuotient.Order1024NodeCertificates
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration
open Order16Nodes
set_option maxRecDepth 100000

@[expose] public def generatorCode (j : Fin 18) (k : Fin 4) : ℕ :=
  (![![8, 4, 1, 32],
    ![8, 4, 2, 45],
    ![8, 4, 3, 34],
    ![12, 10, 1, 32],
    ![12, 2, 1, 32],
    ![12, 10, 9, 40],
    ![12, 2, 9, 40],
    ![12, 10, 9, 32],
    ![12, 10, 1, 40],
    ![8, 4, 2, 32],
    ![12, 10, 59, 59],
    ![12, 10, 51, 51],
    ![8, 4, 48, 48],
    ![8, 4, 53, 53],
    ![12, 2, 51, 51],
    ![12, 10, 48, 48],
    ![12, 10, 56, 56],
    ![12, 2, 48, 48]] j) k

@[expose] public def representative (i : Fin 26) : Fin 18 :=
  ![4, 6, 0, 2, 3, 8, 9, 1, 4, 6, 17, 14, 17, 14, 0, 2, 7, 5, 12, 13, 12, 13, 15, 10, 16, 11] i

@[expose] public def conjugatorCode (i : Fin 26) : ℕ :=
  ![0, 16, 0, 16, 0, 0, 0, 0, 16, 0, 0, 1, 1, 0, 16, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0] i

@[expose] public def quotientGenerator (j : Fin 18) (k : Fin 4) : Group :=
  coordinateElement (generatorCode j k)

@[expose] public def conjugatedGenerator (i : Fin 26) (k : Fin 4) : Group :=
  MulAut.conj (coordinateElement (conjugatorCode i))
    (quotientGenerator (representative i) k)

private def backwardWord (i : Fin 26) (k : Fin 4) : List (Fin 4) :=
  (![![[2], [1], [3], []],
    ![[2, 1], [1, 0], [3, 0], []],
    ![[2], [1], [3], []],
    ![[2, 0], [1], [3, 1, 0], []],
    ![[2], [1, 0], [3], []],
    ![[2], [1, 0], [3, 1], []],
    ![[2], [1], [0], [3]],
    ![[2], [1], [3, 1, 0], []],
    ![[1, 0], [2, 1, 0], [3], []],
    ![[1], [2, 0], [2, 3], []],
    ![[1], [2, 2, 2], [], []],
    ![[1], [2, 2, 2, 1], [], []],
    ![[1], [2, 2, 1, 2], [], []],
    ![[1], [2, 2, 2, 0], [], []],
    ![[2, 1], [1], [3], []],
    ![[2], [1], [2, 3], []],
    ![[2, 1], [2, 0], [3], []],
    ![[2, 1], [2, 0], [2, 3], []],
    ![[1], [0], [2, 2, 2], []],
    ![[1], [0], [2, 2, 2, 1], []],
    ![[1], [0], [2, 2, 2, 1], []],
    ![[1], [0], [2, 2, 2], []],
    ![[1, 0], [2, 2, 2], [], []],
    ![[1, 0], [2, 2, 2], [], []],
    ![[1, 0], [2, 2, 1, 2], [], []],
    ![[1, 0], [2, 2, 1, 2], [], []]] i) k

set_option maxHeartbeats 2000000 in
private theorem conjugatedGenerator_mem : ∀ i k,
    conjugatedGenerator i k ∈ node i.succ := by decide +kernel

set_option maxHeartbeats 2000000 in
private theorem backwardWord_valid : ∀ i k,
    evalWord (conjugatedGenerator i) (backwardWord i k) = generator i.succ k := by
  intro i k
  apply coordinateCode_injective
  exact (by decide +kernel : ∀ i k,
    coordinateCode (evalWord (conjugatedGenerator i) (backwardWord i k)) =
      coordinateCode (generator i.succ k)) i k

/-- The checked generator words identify all twenty-six noncore nodes. -/
public theorem node_eq_closure (i : Fin 26) :
    node i.succ = Subgroup.closure (Set.range (conjugatedGenerator i)) := by
  rw [Order16Nodes.node_eq_closure]
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    rw [← backwardWord_valid i k]
    exact evalWord_mem _ _ (fun j => Subgroup.subset_closure (Set.mem_range_self j)) _
  · rw [← Order16Nodes.node_eq_closure]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    exact conjugatedGenerator_mem i k

end ReeTwo.TailQuotient.Order1024NodeCertificates
