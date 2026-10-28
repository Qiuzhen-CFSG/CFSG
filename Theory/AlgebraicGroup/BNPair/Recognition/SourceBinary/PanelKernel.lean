module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootLocalCover
public import Mathlib.GroupTheory.IndexNormal

/-!
# The local-section kernel criterion and the cubic branch

The simple remainder V = U intersect U^s is preserved by the marked
reflection and by H = B intersect N. Consequently V lies in the full
panel kernel exactly when U normalizes V: in that case B and the simple
reflection normalize V, hence so does the entire marked parabolic.
For a simple root of order two, V has index two in U, proving this
normality and the required kernel containment without perfectness.

This proves the cubic instance of Fong--Seitz I (2B), printed p.9,
using the canonical intersections of (3A)--(3C), pp.12--13. The general
(2B) statement has an exception: its type VI has a degree-nine affine
local action and [V : U intersect K] = 2. No universal containment is
asserted here. Source (2A)'s regularity and the later exclusion of type VI
remain necessary outside the proved branch.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelKernel
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The SAME simple lift preserves the complementary intersection. -/
theorem remainder_simple_conjugate (i : Fin 2) :
    rightConjugate (simpleRemainder Q split i)
      (representative (Q.simple i) : X ⧸ Q.D) = simpleRemainder Q split i := by
  change (split.U ⊓ unipotentConjugate split (Q.simple i)).comap
    (MulAut.conj (representative (Q.simple i) : X ⧸ Q.D)).toMonoidHom = _
  rw [comap_inf]
  change unipotentConjugate split (Q.simple i) ⊓
    rightConjugate (unipotentConjugate split (Q.simple i)) _ = _
  rw [unipotentConjugate_right split _ _ _ (representative_spec _)]
  have hs : Q.simple i * Q.simple i = 1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2
  rw [hs, unipotentConjugate_one, inf_comm]
  rfl

/-- Relative U-normality promotes to full parabolic normality and kernel containment. -/
theorem remainder_le_kernel_of_normalized (i : Fin 2)
    (hU : split.U ≤ normalizer (simpleRemainder Q split i : Set (X ⧸ Q.D))) :
    simpleRemainder Q split i ≤ localKernel Q i := by
  let V := simpleRemainder Q split i
  let M := Q.tits.standardParabolic {Q.simple i}
  have hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (V : Set (X ⧸ Q.D)) :=
    (le_inf (inf_le_left.trans split.normalizes)
      (torus_normalizes_unipotentConjugate split (Q.simple i))).trans
        inf_normalizer_le_normalizer_inf
  have hB : Q.tits.B ≤ normalizer (V : Set (X ⧸ Q.D)) := by
    rw [← split.factorization]
    exact sup_le hU hH
  have hn : (representative (Q.simple i) : X ⧸ Q.D) ∈
      normalizer (V : Set (X ⧸ Q.D)) := by
    apply mem_normalizer_iff.mpr
    intro x
    exact (SetLike.ext_iff.mp (remainder_simple_conjugate Q split i) x).symm
  have hM : M ≤ normalizer (V : Set (X ⧸ Q.D)) := by
    apply Q.tits.standardParabolic_le _ hB
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst s
    exact Q.tits.bruhatCell_subset_of_mem _ hB
      (Q.tits.representative_mem_bruhatCell _ _ (representative_spec _)) hn
  let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hM
  have hcore : V.subgroupOf M ≤ (Q.tits.B.subgroupOf M).normalCore :=
    normal_le_normalCore.mpr (subgroupOf_mono _ (inf_le_left.trans split.U_le))
  intro x hx
  exact ⟨⟨x,Q.tits.B_le_standardParabolic _ (split.U_le hx.1)⟩,hcore hx,rfl⟩

/-- The exact missing (2B) premise, expressed as intrinsic relative normality. -/
theorem remainder_le_kernel_iff_normalized (i : Fin 2) :
    simpleRemainder Q split i ≤ localKernel Q i ↔
      split.U ≤ normalizer (simpleRemainder Q split i : Set (X ⧸ Q.D)) := by
  constructor
  · intro hV
    exact (split.U_le.trans (Q.tits.B_le_standardParabolic _)).trans
      (remainder_parabolic_normalizes Q split i hV)
  · exact remainder_le_kernel_of_normalized Q split i

/-- The nonperfect cubic branch discharges (2B) by index-two normality. -/
theorem remainder_le_kernel_of_root_card_two (i : Fin 2)
    (hc : Nat.card (simpleRoot Q split i) = 2) :
    simpleRemainder Q split i ≤ localKernel Q i := by
  apply remainder_le_kernel_of_normalized Q split i
  apply (normal_subgroupOf_iff_le_normalizer
    (show simpleRemainder Q split i ≤ split.U from inf_le_left)).mp
  exact normal_of_index_eq_two ((simpleRemainder_index Q split i).trans hc)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelKernel
