/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/GoldenFourAlternating.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianNormOneReductionSurjective
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# GoldenFourAlternating

The natural action of PSL₂ over the golden field modulo two identifies
SL₂(F₄) with A₅. The scalar center is trivial; simplicity makes the faithful
five-point action even, and the two groups have the same order.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/GoldenFourAlternating.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
The existing exceptional-isomorphism support supplies the center and projective
line counts; rank-two simplicity is used directly from Mathlib.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped MatrixGroups LinearAlgebra.Projectivization
attribute [local instance] Classical.propDecidable

theorem goldenFour_SL_center : Subgroup.center (SL(2,GoldenFour))=⊥ := by
  rw [Subgroup.eq_bot_iff_card]
  rw [Atlas.ExceptionalSupport.card_sl_center]
  have hc : Nat.card GoldenFour=4 := by rw [Nat.card_eq_fintype_card,goldenFour_card]
  rw [hc]
  norm_num

/-- The canonical central quotient is an isomorphism in dimension two over F4. -/
def goldenFourSLPSL : SL(2,GoldenFour) ≃* PSL(2,GoldenFour) :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center (SL(2,GoldenFour))))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk',goldenFour_SL_center]),
      QuotientGroup.mk'_surjective _⟩

theorem goldenFour_PSL_card : Nat.card (PSL(2,GoldenFour))=60 := by
  rw [← Nat.card_congr goldenFourSLPSL.toEquiv,goldenFour_SL_card]

abbrev GoldenFourProjectiveLine := ℙ GoldenFour (Fin 2 → GoldenFour)

instance goldenFourProjectiveLine_fintype : Fintype GoldenFourProjectiveLine := Fintype.ofFinite _

theorem goldenFourProjectiveLine_card : Nat.card GoldenFourProjectiveLine=5 := by
  rw [Atlas.card_projectiveSpace]
  have hc : Nat.card GoldenFour=4 := by rw [Nat.card_eq_fintype_card,goldenFour_card]
  rw [hc]
  norm_num

/-- A coordinate marking of the actual five-point projective line. -/
def goldenFourProjectiveMarking : GoldenFourProjectiveLine ≃ Fin 5 :=
  Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using goldenFourProjectiveLine_card)

def goldenFourPSLToFivePerm : PSL(2,GoldenFour) →* Equiv.Perm (Fin 5) :=
  goldenFourProjectiveMarking.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom (PSL(2,GoldenFour)) GoldenFourProjectiveLine)

theorem goldenFourPSLToFivePerm_injective : Function.Injective goldenFourPSLToFivePerm := by
  intro g h he
  apply (MulAction.toPerm_injective (β := GoldenFourProjectiveLine))
  exact goldenFourProjectiveMarking.permCongrHom.injective he

/-- The natural faithful action is even, by Mathlib's rank-two PSL simplicity theorem. -/
theorem goldenFourPSLToFivePerm_sign (g : PSL(2,GoldenFour)) :
    Equiv.Perm.sign (goldenFourPSLToFivePerm g)=1 := by
  have hc : Nat.card GoldenFour=4 := by rw [Nat.card_eq_fintype_card,goldenFour_card]
  let : IsSimpleGroup (PSL(2,GoldenFour)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hc])
  let s := Equiv.Perm.sign.comp goldenFourPSLToFivePerm
  have hs : s.ker=⊤ := by
    rcases s.normal_ker.eq_bot_or_eq_top with h | h
    · have hi := s.ker_eq_bot_iff.mp h
      have hh := Nat.card_le_card_of_injective s hi
      have hz : Nat.card ℤˣ=2 := by simp [Nat.card_eq_fintype_card]
      rw [goldenFour_PSL_card,hz] at hh
      omega
    · exact h
  have hg : g ∈ s.ker := hs ▸ Subgroup.mem_top g
  exact (MonoidHom.mem_ker.mp hg : s g = 1)

def goldenFourPSLToAlternating : PSL(2,GoldenFour) →* alternatingGroup (Fin 5) :=
  goldenFourPSLToFivePerm.codRestrict _ goldenFourPSLToFivePerm_sign

theorem goldenFourPSLToAlternating_bijective : Function.Bijective goldenFourPSLToAlternating := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  constructor
  · intro g h he
    exact goldenFourPSLToFivePerm_injective (congrArg Subtype.val he)
  · rw [goldenFour_PSL_card,nat_card_alternatingGroup]
    norm_num

/-- Identification with the actual alternating group through the explicit
five-point projective action, not recognition from an abstract order. -/
def goldenFourSLAlternatingFive : SL(2,GoldenFour) ≃* alternatingGroup (Fin 5) :=
  goldenFourSLPSL.trans (MulEquiv.ofBijective goldenFourPSLToAlternating
    goldenFourPSLToAlternating_bijective)

end Atlas.Algebra
