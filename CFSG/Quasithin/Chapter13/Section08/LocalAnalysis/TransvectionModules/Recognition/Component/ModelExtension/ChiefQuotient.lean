module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.ChiefQuotient.Series
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Action
public import Theory.GroupAction.SubgroupConjugation
public import Theory.ElementaryAbelian.Quotient
public import Mathlib.FieldTheory.Finiteness

/-!
# Passing the two noncentral chief factors through V₁

The elementary abelian group U_H has its actual H-conjugation representation.
Restrict it to L₁ and map canonically to Additive(U_H/V₁), with its prescribed
H*-conjugation action restricted along L₁ → H → H*. The intertwiner is surjective,
and its kernel is identified elementwise with V₁. When |V₁|=2 this kernel has
binary dimension one and is pointwise fixed: every automorphism of its additive
group fixes its unique nonzero element.

The chief-series theorem in `ChiefQuotient.Series` therefore transfers exactly
two noncentral factors from U_H to the literal quotient. The final adapter has
the precise `literalRepresentation` type used by `FullModelConclusions`.
Normality of V₁ is relative to U_H throughout. The earlier chief-factor result
on U_H remains an explicit input, as required of this source-transfer helper.

Source: Aschbacher–Smith, The Classification of Quasithin Groups, combined
manuscript of 1 March 2004, 13.7.6(3a), printed pp.938–939, and 13.8.5(2a),
printed p.947. Applicability of the earlier theorem belongs to final assembly.
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.ChiefQuotient

variable {G : Type*} [Group G] (H V₃ : Subgroup G)

/-- Actual conjugation by H on its conjugate span U_H. -/
def uhAction : H →* MulAut (Source.UH H V₃) := by
  letI := conjMulDistribMulActionOfLeNormalizer H (Source.UH H V₃)
    (le_normalizer_conjugateSpanBy V₃ H)
  exact MulDistribMulAction.toMulAut H (Source.UH H V₃)

variable [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The binary H-representation on Additive U_H before taking the quotient. -/
def uhRepresentation : Representation (ZMod 2) H (Additive (Source.UH H V₃)) where
  toFun h := (uhAction H V₃ h).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro u
    change Additive.ofMul (uhAction H V₃ 1 u.toMul) = u
    rw [map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro u
    change Additive.ofMul (uhAction H V₃ (a * b) u.toMul) = _
    rw [map_mul]
    rfl

@[simp] theorem uhRepresentation_apply (h : H) (u : Source.UH H V₃) :
    uhRepresentation H V₃ h (Additive.ofMul u) =
      Additive.ofMul ⟨(h : G) * (u : G) * (h : G)⁻¹,
        le_normalizer_iff.mp (le_normalizer_conjugateSpanBy V₃ H)
          h h.property u u.property⟩ := rfl

variable (V₁ : Subgroup G) [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (L₁ : Subgroup G) (hL : L₁ ≤ H)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))

/-- The actual L₁-action on the unquotiented elementary abelian group. -/
abbrev loneRepresentation : Representation (ZMod 2) L₁ (Additive (Source.UH H V₃)) := (uhRepresentation H V₃).comp (inclusion hL)

/-- The actual restriction along L₁ → H → H*. -/
abbrev loneQuotientRepresentation :
    Representation (ZMod 2) L₁ (Additive (Source.Utilde H V₃ V₁)) :=
  ρ.comp ((QuotientGroup.mk' (pCore 2 H)).comp (inclusion hL))

/-- The canonical quotient map, with equivariance supplied by actual conjugation. -/
def quotientIntertwiner (hρ : IsConjugation H V₃ V₁ ρ) :
    (loneRepresentation H V₃ L₁ hL).IntertwiningMap
      (loneQuotientRepresentation H V₃ V₁ L₁ hL ρ) where
  toLinearMap := (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))).toAdditive.toZModLinearMap 2
  isIntertwining' l := by
    apply LinearMap.ext
    intro u
    exact (hρ (inclusion hL l) u.toMul).symm

@[simp] theorem quotientIntertwiner_apply (hρ : IsConjugation H V₃ V₁ ρ)
    (u : Source.UH H V₃) :
    quotientIntertwiner H V₃ V₁ L₁ hL ρ hρ (Additive.ofMul u) = vector H V₃ V₁ u := rfl

theorem quotientIntertwiner_surjective (hρ : IsConjugation H V₃ V₁ ρ) :
    Function.Surjective (quotientIntertwiner H V₃ V₁ L₁ hL ρ hρ) := by
  intro v
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
  exact ⟨Additive.ofMul u, congrArg Additive.ofMul hu⟩

/-- The intertwiner's kernel is exactly the actual subgroup V₁ inside U_H. -/
theorem mem_quotientIntertwiner_ker (hρ : IsConjugation H V₃ V₁ ρ)
    (u : Additive (Source.UH H V₃)) :
    u ∈ (quotientIntertwiner H V₃ V₁ L₁ hL ρ hρ).ker ↔ (u.toMul : G) ∈ V₁ := by
  change QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u.toMul = 1 ↔ _
  exact QuotientGroup.eq_one_iff u.toMul

/-- This equivalence identifies actual elements, rather than only their cardinalities. -/
def quotientKernelEquiv (hρ : IsConjugation H V₃ V₁ ρ) (hV : V₁ ≤ Source.UH H V₃) :
    (quotientIntertwiner H V₃ V₁ L₁ hL ρ hρ).ker.toSubmodule ≃ V₁ where
  toFun u := ⟨u.val.toMul, (mem_quotientIntertwiner_ker H V₃ V₁ L₁ hL ρ hρ u.val).mp u.property⟩
  invFun v := ⟨Additive.ofMul ⟨v, hV v.property⟩,
    (mem_quotientIntertwiner_ker H V₃ V₁ L₁ hL ρ hρ _).mpr v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem quotientKernel_card (hρ : IsConjugation H V₃ V₁ ρ) (hV : V₁ ≤ Source.UH H V₃)
    (hcard : Nat.card V₁ = 2) :
    Nat.card (quotientIntertwiner H V₃ V₁ L₁ hL ρ hρ).ker.toSubmodule = 2 := by
  rw [Nat.card_congr (quotientKernelEquiv H V₃ V₁ L₁ hL ρ hρ hV), hcard]

theorem quotientKernel_finrank [Finite G]
    (hρ : IsConjugation H V₃ V₁ ρ) (hV : V₁ ≤ Source.UH H V₃)
    (hcard : Nat.card V₁ = 2) :
    Module.finrank (ZMod 2) (quotientIntertwiner H V₃ V₁ L₁ hL ρ hρ).ker.toSubmodule = 1 := by
  let K := (quotientIntertwiner H V₃ V₁ L₁ hL ρ hρ).ker.toSubmodule
  let := Fintype.ofFinite K
  have hc := quotientKernel_card H V₃ V₁ L₁ hL ρ hρ hV hcard
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card] at hc
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) (hc.trans (pow_one 2).symm)

private theorem fixed_of_card_two {J E : Type*} [Group J] [AddCommGroup E]
    [Module (ZMod 2) E] (τ : Representation (ZMod 2) J E) (hcard : Nat.card E = 2) :
    ∀ g x, τ g x = x := by
  obtain ⟨z, hz, hu⟩ := (Nat.card_eq_two_iff' (0 : E)).mp hcard
  intro g x
  by_cases hx : x = 0
  · simp [hx]
  · have hgx : τ g x ≠ 0 := by
      intro he
      have he' := congrArg (τ g⁻¹) he
      have hi : τ g⁻¹ (τ g x) = x := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      rw [hi, map_zero] at he'
      exact hx he'
    exact (hu _ hgx).trans (hu x hx).symm

/-- An invariant subgroup of order two is pointwise fixed. Its invariance here
comes from the canonical intertwiner, so no ambient-normality premise is added. -/
theorem quotientKernel_fixed (hρ : IsConjugation H V₃ V₁ ρ) (hV : V₁ ≤ Source.UH H V₃)
    (hcard : Nat.card V₁ = 2) :
    ∀ l u, quotientIntertwiner H V₃ V₁ L₁ hL ρ hρ u = 0 →
      loneRepresentation H V₃ L₁ hL l u = u := by
  let p := quotientIntertwiner H V₃ V₁ L₁ hL ρ hρ
  have hf := fixed_of_card_two p.ker.toRepresentation
    (quotientKernel_card H V₃ V₁ L₁ hL ρ hρ hV hcard)
  intro l u hu
  exact congrArg Subtype.val (hf l ⟨u, hu⟩)

/-- The precise chief-factor passage required from 13.7.6(3a) to 13.8.5(2a).
The input is on U_H; the output is on the literal quotient U_H/V₁. -/
theorem twoNoncentralChiefFactors_utilde
    (hρ : IsConjugation H V₃ V₁ ρ) (hV : V₁ ≤ Source.UH H V₃)
    (hcard : Nat.card V₁ = 2)
    (hchief : CriticalGeometry.Reorientation.TwoNoncentralChiefFactors
      (loneRepresentation H V₃ L₁ hL)) :
    CriticalGeometry.Reorientation.TwoNoncentralChiefFactors
      (loneQuotientRepresentation H V₃ V₁ L₁ hL ρ) :=
  twoNoncentralChiefFactors_of_surjective_fixed_kernel
    (quotientIntertwiner H V₃ V₁ L₁ hL ρ hρ)
    (quotientIntertwiner_surjective H V₃ V₁ L₁ hL ρ hρ)
    (quotientKernel_fixed H V₃ V₁ L₁ hL ρ hρ hV hcard) hchief

/-- The H*-restriction agrees with the literal action used by the full model
conclusions, because both actions are conjugation on quotient representatives. -/
theorem loneQuotientRepresentation_eq_literal (hρ : IsConjugation H V₃ V₁ ρ)
    (Q : CriticalGeometry.AsymmetricPair.CenterQuotientAction H (Source.UH H V₃) V₁) :
    loneQuotientRepresentation H V₃ V₁ L₁ hL ρ =
      (CriticalGeometry.Reorientation.literalRepresentation Q).comp (inclusion hL) := by
  apply MonoidHom.ext
  intro l
  apply LinearMap.ext
  intro v
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
  have hv : vector H V₃ V₁ u = v := congrArg Additive.ofMul hu
  rw [← hv]
  change ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hL l)) (vector H V₃ V₁ u) =
    Additive.ofMul (Q.action (inclusion hL l)
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u))
  rw [hρ]
  exact (congrArg Additive.ofMul (Q.apply_mk (inclusion hL l) u)).symm

/-- The resulting statement has exactly the chief-factor type in
`CriticalGeometry.Reorientation.FullModelConclusions`. -/
theorem twoNoncentralChiefFactors_literal
    (hρ : IsConjugation H V₃ V₁ ρ) (hV : V₁ ≤ Source.UH H V₃)
    (hcard : Nat.card V₁ = 2)
    (Q : CriticalGeometry.AsymmetricPair.CenterQuotientAction H (Source.UH H V₃) V₁)
    (hchief : CriticalGeometry.Reorientation.TwoNoncentralChiefFactors
      (loneRepresentation H V₃ L₁ hL)) :
    CriticalGeometry.Reorientation.TwoNoncentralChiefFactors
      ((CriticalGeometry.Reorientation.literalRepresentation Q).comp (inclusion hL)) := by
  rw [← loneQuotientRepresentation_eq_literal H V₃ V₁ L₁ hL ρ hρ Q]
  exact twoNoncentralChiefFactors_utilde H V₃ V₁ L₁ hL ρ hρ hV hcard hchief

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.ChiefQuotient

end
