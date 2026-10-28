module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutProfilesB
public import Theory.GroupTheory.SubgroupEnumeration

/-!
# Coordinates for the seven rank-four small even Ree two candidates

Explicit binary polynomial coordinates use the internal core coordinates of
`SylowModel`. A word in the original generators realizes every binary value,
so the restrictions to the exact generated subgroups are surjective. The
multiplication, Frattini-kernel and intrinsic-count assertions remain separate
certificates on these fixed coordinates.

Source: Shinoda (1975), (2.3), pp. 81–82, with the root convention verified in
`SmallEvenCandidates`. The coordinate basis and section words are extracted
from the finite root-word enumeration; all section equations are kernel checked.
-/

namespace ReeTwo.SylowModel.SmallEvenAutB

open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration

set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

/-- The original generators, padding the last two rows by a repeated generator. -/
@[expose] public def rankFourGenerators : Fin 7 → Fin 8 → SylowModel :=
  ![![root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9], ![root 0, root 0 * root 3 * root 5 * root 6 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9], ![root 0, root 0 * root 3 * root 5 * root 6 * root 9, root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9], ![root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9], ![root 0, root 0 * root 2 * root 5 * root 6 * root 9, root 1 * root 3 * root 4 * root 5 * root 6 * root 8, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9], ![root 0 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9, root 9], ![root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 5 * root 8 * root 9, root 6 * root 8, root 7, root 8 * root 9, root 9, root 9]]

set_option maxHeartbeats 800000 in
/-- The generator vectors retain the exact candidate subgroups. -/
public theorem rankFourCandidate_eq (i : Fin 7) :
    smallEvenCandidate (rankFourIndex i) =
      Subgroup.closure (Set.range (rankFourGenerators i)) := by
  fin_cases i
  · change Subgroup.closure {root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} =
      Subgroup.closure (Set.range ![root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9])
    congr 1
    ext x
    simp only [Matrix.range_cons, Matrix.range_empty, Set.singleton_union,
      Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false]
  · change Subgroup.closure {root 0, root 0 * root 3 * root 5 * root 6 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} =
      Subgroup.closure (Set.range ![root 0, root 0 * root 3 * root 5 * root 6 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9])
    congr 1
    ext x
    simp only [Matrix.range_cons, Matrix.range_empty, Set.singleton_union,
      Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false]
  · change Subgroup.closure {root 0, root 0 * root 3 * root 5 * root 6 * root 9, root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} =
      Subgroup.closure (Set.range ![root 0, root 0 * root 3 * root 5 * root 6 * root 9, root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9])
    congr 1
    ext x
    simp only [Matrix.range_cons, Matrix.range_empty, Set.singleton_union,
      Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false]
  · change Subgroup.closure {root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} =
      Subgroup.closure (Set.range ![root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9])
    congr 1
    ext x
    simp only [Matrix.range_cons, Matrix.range_empty, Set.singleton_union,
      Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false]
  · change Subgroup.closure {root 0, root 0 * root 2 * root 5 * root 6 * root 9, root 1 * root 3 * root 4 * root 5 * root 6 * root 8, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} =
      Subgroup.closure (Set.range ![root 0, root 0 * root 2 * root 5 * root 6 * root 9, root 1 * root 3 * root 4 * root 5 * root 6 * root 8, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9])
    congr 1
    ext x
    simp only [Matrix.range_cons, Matrix.range_empty, Set.singleton_union,
      Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false]
  · change Subgroup.closure {root 0 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} =
      Subgroup.closure (Set.range ![root 0 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9, root 9])
    congr 1
    ext x
    simp only [Matrix.range_cons, Matrix.range_empty, Set.singleton_union,
      Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false, or_self]
  · change Subgroup.closure {root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 5 * root 8 * root 9, root 6 * root 8, root 7, root 8 * root 9, root 9} =
      Subgroup.closure (Set.range ![root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 5 * root 8 * root 9, root 6 * root 8, root 7, root 8 * root 9, root 9, root 9])
    congr 1
    ext x
    simp only [Matrix.range_cons, Matrix.range_empty, Set.singleton_union,
      Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false, or_self]


/-- Binary quotient coordinates, in the ordered basis of `rankFourProfile`. -/
@[expose] public def rankFourCoordinates (i : Fin 7) (x : SylowModel) : Binary 4 :=
  let c := x.left
  Multiplicative.ofAdd ((![
    ![c.b7 + c.b6 + c.b2 + c.b1 + c.b0, c.b7 + c.b6, c.b1, c.b2],
    ![c.b7 + c.b3 + c.b1 + c.b0, c.b7 + c.b1, c.b1, c.b3],
    ![c.b6 + c.b5 + c.b1, c.b6 + c.b5, c.b3, c.b3 + c.b1 + c.b0],
    ![c.b7 + c.b6 + c.b3 + c.b1, c.b3, c.b1, c.b3 + c.b1 + c.b0],
    ![c.b1 + c.b0, c.b1 * c.b2 + c.b8 + c.b6 + c.b2, c.b2, c.b1],
    ![c.b2 * c.b3 + c.b8 + c.b3 + c.b2, c.b2 * c.b3 + c.b8 + c.b5,
      c.b2 * c.b3 + c.b8 + c.b5 + c.b3 + c.b2 + c.b0, c.b3 + c.b2],
    ![c.b1 * c.b4 + c.b7 + c.b6 + c.b3 + c.b1, c.b3 + c.b1,
      c.b1 * c.b4 + c.b7 + c.b1, c.b1]]) i)

/-- Proposed internal carrier equations. Equality with each generated candidate
is a separate algebraic certificate. -/
@[expose] public def rankFourCarrier (i : Fin 7) (x : SylowModel) : Prop :=
  let c := x.left
  (![x.right = 1 ∧ c.b3 = 0 ∧ c.b4 = c.b2,
    x.right = 1 ∧ c.b2 = 0 ∧ c.b4 = 0,
    x.right = 1 ∧ c.b2 = c.b1 ∧ c.b4 = c.b1,
    x.right = 1 ∧ c.b2 = c.b0 ∧ c.b4 = c.b0,
    x.right = 1 ∧ c.b3 = c.b1 ∧ c.b4 = c.b1,
    x.right.toAdd = 2 * ((c.b2 + c.b3).val : ZMod 4) ∧
      c.b1 = 0 ∧ c.b4 = c.b2 ∧ c.b6 = c.b0 + c.b2 + c.b3 + c.b5,
    x.right.toAdd = 2 * (c.b1.val : ZMod 4) ∧
      c.b0 = 0 ∧ c.b2 = 0 ∧ c.b5 = c.b4]) i

public instance (i : Fin 7) (x : SylowModel) : Decidable (rankFourCarrier i x) := by
  revert i
  refine Fin.cases (by dsimp [rankFourCarrier]; infer_instance) ?_
  refine Fin.cases (by dsimp [rankFourCarrier]; infer_instance) ?_
  refine Fin.cases (by dsimp [rankFourCarrier]; infer_instance) ?_
  refine Fin.cases (by dsimp [rankFourCarrier]; infer_instance) ?_
  refine Fin.cases (by dsimp [rankFourCarrier]; infer_instance) ?_
  refine Fin.cases (by dsimp [rankFourCarrier]; infer_instance) ?_
  refine Fin.cases (by dsimp [rankFourCarrier]; infer_instance) ?_
  intro i
  exact Fin.elim0 i

set_option maxHeartbeats 16000000 in
/-- All original generators satisfy the proposed carrier equations. -/
public theorem rankFourGenerators_carrier : ∀ i j,
    rankFourCarrier i (rankFourGenerators i j) := by decide +kernel

/-- Restriction of the coordinates to the exact candidate. -/
@[expose] public def rankFourMap (i : Fin 7)
    (x : smallEvenCandidate (rankFourIndex i)) : Binary 4 :=
  rankFourCoordinates i x.val

private def decode (n : Fin 16) : Binary 4 :=
  Multiplicative.ofAdd ![(n.val : ZMod 2), (n.val / 2 : ℕ),
    (n.val / 4 : ℕ), (n.val / 8 : ℕ)]

private def encode (v : Binary 4) : Fin 16 :=
  Fin.ofNat 16 ((v.toAdd 0).val + 2 * (v.toAdd 1).val +
    4 * (v.toAdd 2).val + 8 * (v.toAdd 3).val)

private theorem decode_encode : ∀ v, decode (encode v) = v := by decide +kernel

private def sectionWord : Fin 7 → Fin 16 → List (Fin 8) :=
  ![![[], [0], [0, 5], [5], [1, 2], [0, 1, 2], [0, 1, 2, 5], [1, 2, 5], [1], [0, 1], [0, 1, 5], [1, 5], [2], [0, 2], [0, 2, 5], [2, 5]], ![[], [0], [0, 3], [3], [0, 1, 2], [1, 2], [1, 2, 3], [0, 1, 2, 3], [1], [0, 1], [0, 1, 3], [1, 3], [0, 2], [2], [2, 3], [0, 2, 3]], ![[], [0, 2], [0, 2, 4], [4], [1], [0, 1, 2], [0, 1, 2, 4], [1, 4], [0], [2], [2, 4], [0, 4], [0, 1], [1, 2], [1, 2, 4], [0, 1, 4]], ![[], [5], [0], [0, 5], [0, 2], [0, 2, 5], [2], [2, 5], [1], [1, 5], [0, 1], [0, 1, 5], [0, 1, 2], [0, 1, 2, 5], [1, 2], [1, 2, 5]], ![[], [0], [3], [0, 3], [0, 1], [1], [0, 1, 3], [1, 3], [0, 2], [2], [0, 2, 3], [2, 3], [1, 2], [0, 1, 2], [1, 2, 3], [0, 1, 2, 3]], ![[], [2], [0, 2], [0], [0, 3], [0, 2, 3], [2, 3], [3], [1], [1, 2], [0, 1, 2], [0, 1], [0, 1, 3], [0, 1, 2, 3], [1, 2, 3], [1, 3]], ![[], [3], [0, 3], [0], [3, 4], [4], [0, 4], [0, 3, 4], [1], [1, 3], [0, 1, 3], [0, 1], [1, 3, 4], [1, 4], [0, 1, 4], [0, 1, 3, 4]]]

private def sectionElement (i : Fin 7) (n : Fin 16) : SylowModel :=
  evalWord (rankFourGenerators i) (sectionWord i n)

private theorem sectionElement_mem (i : Fin 7) (n : Fin 16) :
    sectionElement i n ∈ smallEvenCandidate (rankFourIndex i) := by
  rw [rankFourCandidate_eq]
  exact evalWord_mem (rankFourGenerators i) _
    (fun j => Subgroup.subset_closure (Set.mem_range_self j)) _

set_option maxHeartbeats 16000000 in
private theorem section_check : ∀ i n,
    rankFourCoordinates i (sectionElement i n) = decode n := by decide +kernel

/-- A section inside the exact root-generated candidate. -/
private def rankFourSection (i : Fin 7) (v : Binary 4) :
    smallEvenCandidate (rankFourIndex i) :=
  ⟨sectionElement i (encode v), sectionElement_mem i (encode v)⟩

/-- The proposed quotient has all sixteen values on each candidate. -/
private theorem rankFourMap_section (i : Fin 7) (v : Binary 4) :
    rankFourMap i (rankFourSection i v) = v :=
  (section_check i (encode v)).trans (decode_encode v)

/-- Surjectivity is independent of the remaining homomorphism certificate. -/
public theorem rankFourMap_surjective (i : Fin 7) : Function.Surjective (rankFourMap i) :=
  fun v => ⟨rankFourSection i v, rankFourMap_section i v⟩

/-- The three intrinsic predicate counts on a fiber of the fixed coordinates. -/
@[expose] public noncomputable def rankFourCoordinateProfile (i : Fin 7) (v : Binary 4) :
    ℕ × ℕ × ℕ :=
  (Nat.card {x : smallEvenCandidate (rankFourIndex i) //
      rankFourMap i x = v ∧ MulAut.orderCentralizerTest (rankFourTests i 0) x},
    Nat.card {x : smallEvenCandidate (rankFourIndex i) //
      rankFourMap i x = v ∧ MulAut.orderCentralizerTest (rankFourTests i 1) x},
    Nat.card {x : smallEvenCandidate (rankFourIndex i) //
      rankFourMap i x = v ∧ MulAut.orderCentralizerTest (rankFourTests i 2) x})

end ReeTwo.SylowModel.SmallEvenAutB
