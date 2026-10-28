module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications.Alternatives
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications.Orders
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.SpecificGroups.SU3.BinarySylowOrder
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder


/-!
# Variable-field B.4 actors do not have a terminal component order

The three actual exceptional carriers have two-parts at most 2⁷. This bounds
all binary field degrees: Sp₄ and G₂ are excluded immediately, while SL₂
and SL₃ leave only small explicit orders. In characteristic two the actual
PSL₂ quotient is isomorphic to SL₂, covering the orthogonal-four row too.

For a general nondegenerate Hermitian form, the genuine projective image of
SU₃ has order divisible by q³. This forces q = 4; then the order 62400 of
that projective image does not divide any terminal order. Thus SU is never
silently replaced by PSU. Finally, Suzuki groups have order prime to three.

The final consumer applies these comparisons to the literal residual image
in the existing B.4 reduction, leaving just its fixed-group alternatives.

Source: Aschbacher–Smith, B.4.2/B.4.5, printed pp.86–87; K.3.2–6,
pp.454–457; terminal §13.6, p.935 (1 March 2004 manuscript).
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications

private theorem binary_exponent_le {N n : ℕ}
    (hc : N = 20160 ∨ N = 10200960 ∨ N = 604800) (hd : 2 ^ n ∣ N) : n ≤ 7 := by
  by_contra hn
  have h8 : 256 ∣ N := (Nat.pow_dvd_pow 2 (show 8 ≤ n by omega)).trans hd
  rcases hc with rfl | rfl | rfl <;> norm_num at h8

private theorem not_linearTwo_order {N n : ℕ}
    (hc : N = 20160 ∨ N = 10200960 ∨ N = 604800) (hn : 0 < n)
    (he : N = 2 ^ n * ((2 ^ n) ^ 2 - 1)) : False := by
  have hd : 2 ^ n ∣ N := by rw [he]; exact dvd_mul_right _ _
  have hb := binary_exponent_le hc hd
  interval_cases n <;> norm_num at he <;> omega

private theorem card_sl_three (F : BinaryField) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) =
      (2 ^ F.degree) ^ 3 * ((2 ^ F.degree) ^ 3 - 1) * ((2 ^ F.degree) ^ 2 - 1) := by
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (Matrix.SpecialLinearGroup (Fin 3) F.Carrier))
  rw [Atlas.ExceptionalSupport.card_sl_center] at hc
  rw [Fintype.card_fin] at hc
  exact (hc.trans (Matrix.PSL3.LinearThree.card_projective_mul_scalar F.Carrier)).trans
    (by rw [F.card_eq])

private theorem not_linearThree_order {N n : ℕ}
    (hc : N = 20160 ∨ N = 10200960 ∨ N = 604800) (hn : 0 < n)
    (he : N = (2 ^ n) ^ 3 * ((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1)) : False := by
  have hd : 2 ^ (n * 3) ∣ N := by
    rw [he, pow_mul]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hb := binary_exponent_le hc hd
  have hn2 : n ≤ 2 := by omega
  interval_cases n <;> norm_num at he <;> omega

private theorem not_unitary {L : Type*} [Group L]
    (hm : ExceptionalModel L) (F : BinaryField) (n : ℕ) (hn : 2 ≤ n)
    (hdeg : F.degree = 2 * n) (J : HermitianForm 3 F.Carrier)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (e : L ≃* J.specialSubgroup) : False := by
  have hF : Nat.card F.Carrier = (2 ^ n) ^ 2 := by
    rw [F.card_eq, hdeg, Nat.mul_comm 2 n, pow_mul]
  have hquot : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) ∣ Nat.card L := by
    rw [Nat.card_congr e.toEquiv]
    exact J.specialSubgroup.card_map_dvd Matrix.ProjGenLinGroup.mk
  have hd : 2 ^ (n * 3) ∣ Nat.card L := by
    rw [pow_mul]
    exact (HermitianForm.BinarySylowOrder.cube_dvd_card_projective J (by omega) hF hconj).trans hquot
  have hb := binary_exponent_le (exceptional_card hm) hd
  have hn2 : n = 2 := by omega
  subst n
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2 (by decide) hF hconj
  have hp := Representation.SU3.BinaryDegree.card_projective J hF hf
  norm_num only [Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
    Nat.reduceGcd, Nat.reduceDiv] at hp
  rw [hp] at hquot
  rcases exceptional_card hm with hc | hc | hc <;> rw [hc] at hquot <;> norm_num at hquot

/-- Actual order comparisons exclude every variable-field B.4 actor. -/
theorem not_classicalCompetitor_of_exceptional {L : Type*} [Group L]
    (hm : ExceptionalModel L) : ¬ ClassicalCompetitor L := by
  intro h
  have hc := exceptional_card hm
  cases h with
  | linearTwo F e =>
    apply not_linearTwo_order hc F.degree_pos
    exact (Nat.card_congr e.toEquiv).trans (by rw [Atlas.card_sl_two, F.card_eq])
  | linearThree F e =>
    exact not_linearThree_order hc F.degree_pos ((Nat.card_congr e.toEquiv).trans (card_sl_three F))
  | symplectic F hn e =>
    have he := (Nat.card_congr e.toEquiv).trans (Theory.SpecificGroups.SymplecticFour.card_sp F.Carrier)
    rw [F.card_eq] at he
    have hd : 2 ^ (F.degree * 4) ∣ Nat.card L := by
      rw [he, pow_mul]
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    have hb := binary_exponent_le hc hd
    omega
  | g2 F hn e =>
    have he := (Nat.card_congr e.toEquiv).trans (Atlas.G2.card_Model (K := F.Carrier))
    rw [F.card_eq] at he
    have hd : 2 ^ (F.degree * 6) ∣ Nat.card L := by
      rw [he, pow_mul]
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    have hb := binary_exponent_le hc hd
    omega
  | orthogonal _ F _ e =>
    let f := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F.Carrier)).symm
    apply not_linearTwo_order hc F.degree_pos
    exact (Nat.card_congr f.toEquiv).trans (by rw [Atlas.card_sl_two, F.card_eq])
  | unitary F n hn hdeg J hconj e => exact not_unitary hm F n hn hdeg J hconj e
  | suzuki k hk e =>
    have ht := suzukiMatrixGroup_three_free k hk
    rw [← Nat.card_congr e.toEquiv] at ht
    rcases hc with hc | hc | hc <;> rw [hc] at ht <;> norm_num at ht

universe u v
open Section08

/-- On the literal source residual image, small ratio leaves only a fixed
actor. The universal B.4 inputs retain their complete, unfiltered statements. -/
theorem source_fixedCompetitor_of_small_ratio
    {D : Type u} [Group D] [Finite D] {V : Type v} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (σ : Representation (ZMod 2) D V)
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦) (hB45 : FullB45.{u,v} 𝒦)
    (hyp : B4Hypotheses 𝒦 σ) (hz : center (generalizedFitting D) = ⊥)
    {G : Type*} [Group G] [Finite G] (H : Subgroup G) (S : Subgroup H)
    (hs : Components.Conclusion S)
    (e : generalizedFitting D ≃* Source.starImage H (terminalResidual H))
    (hq : quadraticRatio σ ≤ 2) :
    FixedCompetitor (Source.starImage H (terminalResidual H)) := by
  obtain ⟨hm, hc⟩ := source_competitors_of_small_ratio σ hB42 hB45 hyp hz H S hs e hq
  exact hc.resolve_left (not_classicalCompetitor_of_exceptional hm)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications
