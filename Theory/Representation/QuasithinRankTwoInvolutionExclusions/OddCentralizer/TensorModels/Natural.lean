module

public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.FiveLines
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.FieldDescent
public import Theory.Representation.BinaryNormalizerRank
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.TensorModels.Common
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.Representation.FirstCohomologyLinearTransport
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Tactic

/-!
# The natural L₂(4) module and its specified S₅ extension

The original F₄-column action and coordinate Frobenius generate the literal
binary subgroup used here. The existing five-line equivalence identifies it
with S₅, carrying the SL₂ layer to A₅ and Frobenius to a transposition. The
canonical field equivalence and the actual SL₂-to-PSL₂ quotient identify the
restricted representation with the natural L₂(4) module.

An inner involution has positive even binary rank and rank at most two.
The field involution has four fixed vectors, and descent conjugates every
outer involution to it. Thus both classes have rank two, unlike the
transpositions on the orthogonal module.

Source: Aschbacher–Smith, G.11.2(9), printed p.364 (PDF p.375), and the
case-(9) calculation in 6.2.19, printed p.691 (PDF p.708).
-/

@[expose] public section

namespace Representation.RankTwo.TensorModels.Natural
open Representation.SL2FourNatural Representation.SL2FourNatural.SemilinearNormalizer
abbrev Space := V
abbrev GroupModel := specialField
/-- The specified extension acts by its literal binary-linear operators. -/
def representation : Representation (ZMod 2) GroupModel Space :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp specialField.subtype
/-- The five-line group isomorphism preserves the SL₂ layer and the field involution. -/
noncomputable def groupEquiv : GroupModel ≃* Equiv.Perm (Fin 5) := symmetricFiveEquiv
/-- The original natural determinant-one action is the marked subgroup. -/
def inclusion : SL →* GroupModel :=
  action.codRestrict specialField (fun A => (show action.range ≤ specialField from le_sup_left) ⟨A, rfl⟩)
lemma restriction (A : SL) (v : Space) : representation (inclusion A) v = action A v := rfl
lemma marked_alternating : inclusion.range.map groupEquiv.toMonoidHom = alternatingGroup (Fin 5) := by
  have he : inclusion.range = action.range.subgroupOf specialField := by
    ext g
    constructor
    · rintro ⟨A, rfl⟩; exact ⟨A, rfl⟩
    · rintro ⟨A, hA⟩; exact ⟨A, Subtype.ext hA⟩
  rw [he]
  exact symmetricFiveEquiv_special

def fieldActor : GroupModel := ⟨frobeniusLinear,
  (show Subgroup.zpowers frobeniusLinear ≤ specialField from le_sup_right)
    (Subgroup.mem_zpowers frobeniusLinear)⟩
lemma marked_field : groupEquiv fieldActor = Equiv.swap 3 4 := symmetricFiveEquiv_frobenius
lemma representation_field : representation fieldActor = frobeniusLinear.toLinearMap := rfl
lemma finrank_space : Module.finrank (ZMod 2) Space = 4 := finrank_vector

private lemma field_dimension : Module.finrank (ZMod 2) F = 2 := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
  rw [Nat.card_eq_fintype_card, card_field, Nat.card_zmod] at hc
  exact Nat.pow_right_injective (by decide : 1 < 2) hc.symm

lemma finrank_inner (A : SL) (ha : A * A = 1) (hne : A ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.range ((action A).toLinearMap - 1)) = 2 := by
  let d : Space →ₗ[F] Space := specialLinearNatural 2 A - 1
  have hd : LinearMap.range ((action A).toLinearMap - 1) =
      d.range.restrictScalars (ZMod 2) := rfl
  have he := ((Submodule.restrictScalarsEquiv (ZMod 2) F Space d.range).restrictScalars
    (ZMod 2)).finrank_eq
  have heven : Module.finrank (ZMod 2) (LinearMap.range ((action A).toLinearMap - 1)) =
      2 * Module.finrank F d.range := by
    rw [hd, he, ← Module.finrank_mul_finrank (ZMod 2) F d.range, field_dimension]
  have h2 : (action A).toLinearMap * (action A).toLinearMap = 1 := by
    apply LinearMap.ext
    intro v
    change action A (action A v) = v
    rw [← LinearEquiv.mul_apply, ← map_mul, ha, map_one]
    rfl
  have hb := involution_rank_le_half (action A).toLinearMap h2
  rw [finrank_space] at hb
  have hp : Module.finrank (ZMod 2) (LinearMap.range ((action A).toLinearMap - 1)) ≠ 0 := by
    intro hz
    have hm := sub_eq_zero.mp (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz))
    apply hne
    apply action_faithful
    apply LinearEquiv.toLinearMap_injective
    have h1 : (action (1 : SL)).toLinearMap = 1 := by rw [map_one]; rfl
    exact hm.trans h1.symm
  omega

lemma finrank_frobenius :
    Module.finrank (ZMod 2) (LinearMap.range (frobeniusLinear.toLinearMap - 1)) = 2 := by
  have hf : Module.finrank (ZMod 2) fieldFixed = 2 := by
    have hc := card_fieldFixed
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 1 < 2) hc
  have he := (frobeniusLinear.toLinearMap - 1).finrank_range_add_finrank_ker
  have hk : LinearMap.ker (frobeniusLinear.toLinearMap - 1) = fieldFixed :=
    (LinearMap.fixedSubmodule_eq_ker frobeniusLinear.toLinearMap).symm
  rw [hk, hf, finrank_vector] at he
  omega

lemma finrank_outer (g : GroupModel) (hg : g * g = 1) (hout : g.val ∉ action.range) :
    Module.finrank (ZMod 2) (LinearMap.range (representation g - 1)) = 2 := by
  have hsq : g.val * g.val = 1 := congrArg Subtype.val hg
  obtain ⟨A, hA⟩ := specialField_involution_conjugate g.val g.property
    ((pow_two g.val).trans hsq) hout
  have he := congrArg (fun x : BinaryGL =>
    Module.finrank (ZMod 2) (LinearMap.range (x.toLinearMap - 1))) hA
  exact he.trans ((BinaryNormalizerRank.rank_conj (action A) frobeniusLinear).trans finrank_frobenius)

/-- Both involution classes of the specified natural S₅ extension have binary rank two. -/
lemma finrank_involution (g : GroupModel) (hg : g * g = 1) (hne : g ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.range (representation g - 1)) = 2 := by
  by_cases hi : g.val ∈ action.range
  · obtain ⟨A, hA⟩ := hi
    have ha : A * A = 1 := by
      apply action_faithful
      rw [map_mul, hA, ← Subgroup.coe_mul, hg, Subgroup.coe_one, map_one]
    have hAn : A ≠ 1 := by
      rintro rfl
      exact hne (Subtype.ext (hA.symm.trans action.map_one))
    have he := congrArg (fun x : BinaryGL =>
      Module.finrank (ZMod 2) (LinearMap.range (x.toLinearMap - 1))) hA
    exact he.symm.trans (finrank_inner A ha hAn)
  · exact finrank_outer g hg hi
/-- The original determinant-one carrier is the actual alternating five-group. -/
noncomputable def alternatingEquiv : SL ≃* alternatingGroup (Fin 5) :=
  (MonoidHom.ofInjective specialFiveLines_injective).trans
    (MulEquiv.subgroupCongr specialFiveLines_range)

/-- Identification with the canonical projective group uses the actual quotient map. -/
noncomputable def projectiveEquiv : SL ≃* Theory.PSL2.BinaryGroup 2 :=
  standardGroupEquiv.trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 2))

/-- The canonical binary restriction of the natural L₂(4) action. -/
noncomputable def canonicalNatural : Representation (ZMod 2) (Theory.PSL2.BinaryGroup 2)
    (Fin 2 → GaloisField 2 2) :=
  (restrictScalars (specialLinearNatural 2)).comp
    (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 2)).symm.toMonoidHom

/-- This is an equivalence of the marked natural representations, not merely their groups. -/
noncomputable def naturalEquiv : Representation.Equiv (representation.comp inclusion)
    (canonicalNatural.comp projectiveEquiv.toMonoidHom) where
  toLinearEquiv := standardVectorEquiv
  isIntertwining' A := by
    apply LinearMap.ext
    intro v
    change standardVectorEquiv (action A v) = specialLinearNatural 2
      ((Theory.PSL2.sl2QuotientEquiv (GaloisField 2 2)).symm
        ((Theory.PSL2.sl2QuotientEquiv (GaloisField 2 2)) (standardGroupEquiv A)))
      (standardVectorEquiv v)
    rw [MulEquiv.symm_apply_apply]
    exact standard_equivariant A v

end Representation.RankTwo.TensorModels.Natural
