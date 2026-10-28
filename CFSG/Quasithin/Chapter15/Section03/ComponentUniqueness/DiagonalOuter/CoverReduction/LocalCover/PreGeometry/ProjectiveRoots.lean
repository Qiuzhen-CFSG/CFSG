module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.PreGeometry.Contracts
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.CubicRootGeometry

/-!
# The source plane and cubic actors on the actual projective Sylow

The source setup supplies the quotient Sylow in the original marking.
The root containment bounds the plane image from below, while its upstairs
order bounds it from above. Its S-invariance gives normality in the actual
Sylow, so the intrinsic normal-four calculation identifies its centre.

Normality of the component residual and its two-core identity show that
the opposite residual normalizes S ∩ L. That residual centralizes the plane
by definition. These two facts let every actual diagonal actor satisfy the
intrinsic cubic calculation, through the literal marked conjugation action.
No centre identity upstairs or later product conclusion enters the proof.

Source: Aschbacher--Smith, proof of 15.3.38, printed p.1136.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
open Candidates.LinearCore
variable {G : Type*} [Group G] [Finite G]

/-- Normality of the component residual transfers to its characteristic two-core. -/
theorem PreparedResiduals.opposite_normalizes_component_sylow
    {d : CharacteristicTwo.LocalData G} {I L : Subgroup G} {n : ℕ}
    {c : ProjectiveMarking L (2 ^ n)} {y : d.Yplus}
    (g : PreparedResiduals d I L c y) :
    planeResidual d.M d.Y g.borel.W₂ ≤ normalizer (d.S ⊓ L : Subgroup G) := by
  have hDY : planeResidual d.M d.Y g.borel.W₂ ≤ d.Yplus :=
    ((planeResidual_le _ _ _).trans inf_le_left).trans g.plus.ge
  have hYA : d.Yplus ≤ normalizer (componentPart d.Yplus L : Set G) :=
    ComponentIntersection.normalizes_intersectionResidual g.normalizes
  rw [← g.borel.component_core]
  exact (hDY.trans hYA).trans (normalizer_le_normalizer_characteristic_image
    (componentPart d.Yplus L) (pCore 2 (componentPart d.Yplus L)))

/-- The actual four-plane has order four in the given quotient marking. -/
theorem PreparedResiduals.plane_image_card
    {d : CharacteristicTwo.LocalData G} {I L : Subgroup G} {n : ℕ}
    {c : ProjectiveMarking L (2 ^ n)} {y : d.Yplus}
    (g : PreparedResiduals d I L c y) :
    Nat.card ((g.borel.W₂.subgroupOf L).map (projectiveMap c)) = 4 := by
  have hF : Nat.card c.F = 4 := by rw [c.card, g.parameter]; norm_num
  obtain ⟨a, ha⟩ := g.borel.root
  have hc : Nat.card (Matrix.PSL3Even.UnipotentGeometry.projectiveCenter c.F) = 4 := by
    rw [Matrix.PSL3Even.UnipotentGeometry.projectiveCenter,
      card_map_of_injective (Matrix.PSL3Even.UnipotentGeometry.projective_injective c.F),
      Matrix.PSL3Even.UnipotentGeometry.card_Z, hF]
  have hlo := card_le_of_le ha
  rw [card_map_of_injective (MulAut.conj a).injective, hc] at hlo
  have hup := Nat.le_of_dvd (Nat.card_pos (α := g.borel.W₂.subgroupOf L))
    ((g.borel.W₂.subgroupOf L).card_map_dvd (projectiveMap c))
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (g.borel.second_le_component_sylow.trans inf_le_right)).toEquiv,
    g.borel.second_card] at hup
  exact Nat.le_antisymm hup hlo

/-- The root and cubic calculations on the literal quotient Sylow, with the
original field and quotient equivalence retained. -/
theorem projectiveRootData_of_prepared
    {d : CharacteristicTwo.LocalData G} {I L : Subgroup G} {n : ℕ}
    (c : ProjectiveMarking L (2 ^ n)) (y : d.Yplus)
    (h : MatrixImage.SourceSetup d I L) (g : PreparedResiduals d I L c y) :
    Nonempty (ProjectiveRootData d.S L (planeResidual d.M d.Y g.borel.W₂)
      g.borel.W₂ c) := by
  have hF : Nat.card c.F = 4 := by rw [c.card, g.parameter]; norm_num
  have calculations := Matrix.PSL3.LinearThree.fourSylowRootCalculations c.F hF
  obtain ⟨P, hP⟩ := h.quotient_sylow c.equivalence
  change (P : Subgroup PSL(3,c.F)) = (d.S.subgroupOf L).map (projectiveMap c) at hP
  have hWL : g.borel.W₂ ≤ L := g.borel.second_le_component_sylow.trans inf_le_right
  have hWS : g.borel.W₂ ≤ d.S := g.borel.second_le_component_sylow.trans inf_le_left
  have hWP : (g.borel.W₂.subgroupOf L).map (projectiveMap c) ≤ P := by
    rw [hP]
    exact map_mono (fun _ hx => hWS hx)
  have hWnormal : (P : Subgroup PSL(3,c.F)) ≤
      normalizer ((g.borel.W₂.subgroupOf L).map (projectiveMap c) : Set PSL(3,c.F)) := by
    rw [hP]
    apply (map_mono (show d.S.subgroupOf L ≤ normalizer (g.borel.W₂.subgroupOf L) from ?_)).trans
      (le_normalizer_map _)
    rw [← subgroupOf_normalizer_eq hWL]
    exact fun _ hx => g.borel.second_invariant hx
  have hplane := calculations.normal_four P _ hWP hWnormal g.plane_image_card
  refine ⟨⟨P, hP.symm, hplane, ?_⟩⟩
  intro z hz hzdiag α hα
  have hzY : z ∈ d.Yplus := g.plus.ge ((planeResidual_le _ _ _ hz).1)
  let zN : normalizer (L : Set G) := ⟨z, g.normalizes hzY⟩
  have hαeq : markedAction c zN = α := markedAction_eq_of_realizes c zN hα
  obtain ⟨hz3, a, hout, hreal⟩ := hzdiag
  have hδeq : markedAction c zN = Matrix.PSL3.OuterSolvable.linearConj c.F a :=
    markedAction_eq_of_realizes c zN hreal
  have hδα : Matrix.PSL3.OuterSolvable.linearConj c.F a = α := hδeq.symm.trans hαeq
  have hα3 : α ^ 3 = 1 := by
    rw [← hαeq, ← map_pow]
    have hzN3 : zN ^ 3 = 1 := Subtype.ext ((orderOf_eq_prime_iff.mp hz3).1)
    rw [hzN3, map_one]
  have hαP : (P : Subgroup PSL(3,c.F)).map α.toMonoidHom = P := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨_, hp, rfl⟩
      rw [hP] at hp ⊢
      obtain ⟨u, hu, rfl⟩ := hp
      change α (projectiveMap c u) ∈ (d.S.subgroupOf L).map (projectiveMap c)
      rw [← hαeq, markedAction_apply]
      refine mem_map_of_mem (projectiveMap c) ?_
      have hnz := g.opposite_normalizes_component_sylow hz
      have huQ : (u : G) ∈ d.S ⊓ L := ⟨hu, u.property⟩
      exact ((mem_normalizer_iff.mp hnz u).mp huQ).1
    · rw [card_map_of_injective α.injective]
  have hαZ : (center P).map (P : Subgroup PSL(3,c.F)).subtype ≤ α.fixedSubgroup := by
    rw [← hplane]
    rintro _ ⟨u, hu, rfl⟩
    rw [MulAut.mem_fixedSubgroup, ← hαeq, markedAction_apply]
    apply congrArg (projectiveMap c)
    apply Subtype.ext
    have hc := (planeResidual_le _ _ _ hz).2.2 u hu
    change z * (u : G) * z⁻¹ = u
    rw [← hc, mul_inv_cancel_right]
  have result := calculations.cubic P a hout (hδα.symm ▸ hα3)
    (hδα.symm ▸ hαP) (hδα.symm ▸ hαZ)
  rw [hδα, ← hplane] at result
  exact result

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
