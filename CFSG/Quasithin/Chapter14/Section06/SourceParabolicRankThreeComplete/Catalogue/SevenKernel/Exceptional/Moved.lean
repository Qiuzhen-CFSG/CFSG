module
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates

/-!
# The original exceptional moved subgroup

The displacement equivalence identifies the whole B.5 moved four-space with
[Ω₁Z(O₂(KR)),K]. Faithfulness on that space identifies its centralizer with
the original action kernel. The resulting A₇ marking is a marking of the
star quotient, retaining any central cover of the two-core quotient.

Source: Aschbacher--Smith B.5.1 and C.1.24(a), pp.99--103 and 130--131.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel.Exceptional
variable {A D : Type*} [Group A] [Group D]
variable (V K : Subgroup A) [V.Normal] [K.Normal] [IsElementaryAbelian 2 V]
variable (q : A →* D) (hq : Function.Surjective q) (hk : q.ker = centralizer (V : Set A))
variable (W : Subrepresentation (NormalElementaryQuotient.representation V q hq hk))
  (hW : W.toSubmodule = subspaceCommutator (NormalElementaryQuotient.representation V q hq hk) ⊤ (K.map q))
  (hf : Function.Injective W.toRepresentation)
variable [IsElementaryAbelian 2 (⁅V,K⁆ : Subgroup A)]

private noncomputable def coordinates :
    Additive (⁅V,K⁆ : Subgroup A) ≃ₗ[ZMod 2] W.toSubmodule :=
  (NormalElementaryQuotient.movedEquiv V q hq hk K).trans
    (LinearEquiv.ofEq _ _ hW.symm)

private theorem coordinates_conjugation (a : A) (v : Additive (⁅V,K⁆ : Subgroup A)) :
    coordinates V K q hq hk W hW (Additive.ofMul (MulAut.conjNormal a v.toMul)) =
      W.toRepresentation (q a) (coordinates V K q hq hk W hW v) := by
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (NormalElementaryQuotient.representation_apply V q hq hk a
    (coordinates V K q hq hk W hW v).val).symm

include W hW hf in
private theorem moved_kernel : q.ker = centralizer ((⁅V,K⁆ : Subgroup A) : Set A) := by
  apply le_antisymm
  · rw [hk]
    exact centralizer_le (commutator_le_left V K)
  · intro a ha
    apply hf
    rw [map_one]
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := (coordinates V K q hq hk W hW).surjective w
    change W.toRepresentation (q a) (coordinates V K q hq hk W hW v) =
      coordinates V K q hq hk W hW v
    rw [←coordinates_conjugation]
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    change a * (v.toMul : A) * a⁻¹ = (v.toMul : A)
    rw [←ha v.toMul v.toMul.property,mul_inv_cancel_right]

include hW hf in
/-- The exceptional row supplies the full original four-space and its
literal faithful quotient map, before any block or two-core recovery. -/
theorem moved_exceptional
    (eC : K.map q ≃* alternatingGroup (Fin 7))
    (hfull : K.map q = ⊤)
    (hd : Module.finrank (ZMod 2) W.toSubmodule = 4) :
    ∃ q' : A →* alternatingGroup (Fin 7), Function.Surjective q' ∧
      q'.ker = centralizer ((⁅V,K⁆ : Subgroup A) : Set A) ∧ K.map q' = ⊤ ∧
      Module.finrank (ZMod 2) (Additive (⁅V,K⁆ : Subgroup A)) = 4 := by
  let eD : D ≃* K.map q := (MulEquiv.ofBijective (K.map q).subtype
    ⟨(K.map q).subtype_injective,fun a => ⟨⟨a,hfull ▸ mem_top a⟩,rfl⟩⟩).symm
  let e := eD.trans eC
  let q' := e.toMonoidHom.comp q
  refine ⟨q',e.surjective.comp hq,?_,?_,(coordinates V K q hq hk W hW).finrank_eq.trans hd⟩
  · exact (MonoidHom.ker_comp_of_injective q e.toMonoidHom e.injective).trans
      (moved_kernel V K q hq hk W hW hf)
  · rw [show K.map q' = (K.map q).map e.toMonoidHom from (map_map _ _ _).symm,
      hfull,map_top_of_surjective _ e.surjective]
end CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel.Exceptional
