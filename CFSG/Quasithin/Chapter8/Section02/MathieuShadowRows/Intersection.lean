module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeHexacode
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global

/-!
# Coordinates on the original code intersection

The offender lies in the selected two-core P, while the original V normalizes P.
Every offender displacement therefore lies in V intersect P. The native sextet
core moves a ten-dimensional hyperplane; equality of dimensions identifies
this hyperplane with the literal original intersection, under the same marking.

Source: Aschbacher--Smith 8.2.2(7), 8.2.5 and 8.2.8(5), printed pp.715--718,
refs/quasithin.pdf. No replacement orbit or quotient actor is introduced.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open MathieuCode.NormalizedShadowRows.CodeHexacode
variable {G : Type*} [Group G] [Finite G]

/-- A core-normalized code marking identifies the original intersection. -/
theorem code_intersection_coordinates (V P A : Subgroup G) [IsElementaryAbelian 2 V]
    (hVN : V ≤ normalizer (P : Set G))
    (hAP : A ≤ P) (S : Sextet) (p : Automizer V →* M24)
    (F : Additive V ≃ₗ[ZMod 2] Code)
    (hF : ∀ b v, F (automizerRepresentation V b v) = codeRepresentation (p b) (F v))
    (hc : (inducedAutomizer V A).map p = CodeFlags.sextetCore S)
    (hrank : rank (V ⊓ P : Subgroup G) = 10) :
    ∀ v : V, (v : G) ∈ P ↔ F (Additive.ofMul v) ∈ evenCode S := by
  let W : Submodule (ZMod 2) (Additive V) :=
    AddSubgroup.toZModSubmodule 2 ((V ⊓ P : Subgroup G).subgroupOf V).toAddSubgroup
  have hcomm : ⁅A,V⁆ ≤ P := (commutator_mono hAP le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp hVN)
  have hm : subspaceCommutator (automizerRepresentation V) ⊤ (inducedAutomizer V A) ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b,⟨x,hx,rfl⟩,v,_,rfl⟩
    change (((automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict x) v - v).toMul : G)) ∈ V ⊓ P
    refine ⟨(automizerRepresentation V _ v - v).toMul.property, ?_⟩
    change ((V.normalizerMonoidHom x v.toMul / v.toMul : V) : G) ∈ P
    simpa only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv,
      normalizerMonoidHom_apply_apply_coe, div_eq_mul_inv, commutatorElement_def, Subgroup.subtype_apply]
      using hcomm (commutator_mem_commutator hx v.toMul.property)
  have he := subspaceCommutator_map_embedding (automizerRepresentation V) codeRepresentation
    p F.symm.toLinearMap (fun b v => by
      apply F.injective
      change F (automizerRepresentation V b (F.symm v)) = F (F.symm (codeRepresentation (p b) v))
      rw [hF,F.apply_symm_apply,F.apply_symm_apply])
    (inducedAutomizer V A) ⊤
  rw [Submodule.map_top,LinearEquiv.range,hc,sextetCore_moved] at he
  have hle : evenCode S ≤ W.map F.toLinearMap := by
    intro v hv
    refine ⟨F.symm v,hm ?_,F.apply_symm_apply _⟩
    rw [he]
    exact ⟨v,hv,rfl⟩
  have hdim : Module.finrank (ZMod 2) W = 10 := by
    let e : (V ⊓ P : Subgroup G) ≃ W := {
      toFun := fun x => ⟨Additive.ofMul ⟨x.val,x.property.1⟩,x.property⟩
      invFun := fun x => ⟨x.val.toMul.val,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [Nat.card_zmod, ← Nat.card_congr e] at hh
    have hl := congrArg (Nat.log 2) hh
    rw [Nat.log_pow Nat.one_lt_two] at hl
    exact hl.symm.trans hrank
  have heq : evenCode S = W.map F.toLinearMap :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [F.finrank_map_eq,hdim,evenCode_finrank])
  intro v
  rw [heq]
  constructor
  · intro hv
    exact ⟨Additive.ofMul v,⟨v.property,hv⟩,rfl⟩
  · rintro ⟨w,hw,he⟩
    have hwv := F.injective he
    subst w
    exact hw.2

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows

