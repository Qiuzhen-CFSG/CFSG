module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Reconstruction.StarAction
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Reconstruction.Selection
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates

/-!
# The full moved subgroup of the seven-letter star action

The displacement-space equivalence identifies the B.5 moved space with
the literal subgroup commutator. Faithfulness on that full space preserves
the action kernel, and its zero central layer gives zero component fixed
points. The natural and exceptional coordinates therefore supply exactly
the whole-module inputs to C.1.24, before shortness is known.

Source: Aschbacher--Smith, B.5.1 and C.1.24(a), pp.99--103 and130--131.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction
open Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
variable {A D : Type*} [Group A] [Finite A] [Group D] [Finite D]
variable (V K : Subgroup A) [V.Normal] [K.Normal] [IsElementaryAbelian 2 V]
variable (q : A →* D) (hq : Function.Surjective q) (hk : q.ker = centralizer (V : Set A))
variable (m : AlternatingModels.ActionData
  (NormalElementaryQuotient.representation V q hq hk) (K.map q))

variable [IsElementaryAbelian 2 (⁅V,K⁆ : Subgroup A)]

private noncomputable def movedCoordinates :
    Additive (⁅V,K⁆ : Subgroup A) ≃ₗ[ZMod 2] m.sectionData.space.toSubmodule :=
  (NormalElementaryQuotient.movedEquiv V q hq hk K).trans
    (LinearEquiv.ofEq _ _ m.sectionData.space_eq.symm)

omit [Finite A] [Finite D] in
private theorem movedCoordinates_conjugation (a : A) (v : Additive (⁅V,K⁆ : Subgroup A)) :
    movedCoordinates V K q hq hk m (Additive.ofMul (MulAut.conjNormal a v.toMul)) =
      m.sectionData.space.toRepresentation (q a) (movedCoordinates V K q hq hk m v) := by
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (NormalElementaryQuotient.representation_apply V q hq hk a
    (movedCoordinates V K q hq hk m v).val).symm

include m in
omit [Finite A] [Finite D] in
private theorem moved_kernel : q.ker = centralizer ((⁅V,K⁆ : Subgroup A) : Set A) := by
  apply le_antisymm
  · rw [hk]
    exact centralizer_le (commutator_le_left V K)
  · intro a ha
    apply m.faithful
    rw [map_one]
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := (movedCoordinates V K q hq hk m).surjective w
    change m.sectionData.space.toRepresentation (q a) (movedCoordinates V K q hq hk m v) =
      movedCoordinates V K q hq hk m v
    rw [←movedCoordinates_conjugation]
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    change a * (v.toMul : A) * a⁻¹ = (v.toMul : A)
    rw [←ha v.toMul v.toMul.property,mul_inv_cancel_right]

include m in
omit [Finite A] [Finite D] in
private theorem moved_fixed : (⁅V,K⁆ : Subgroup A) ⊓ centralizer (K : Set A) = ⊥ := by
  apply bot_unique
  intro u hu
  let v : Additive (⁅V,K⁆ : Subgroup A) := Additive.ofMul ⟨u,hu.1⟩
  let w := movedCoordinates V K q hq hk m v
  have hw : w ∈ m.sectionData.central.toSubmodule := by
    rw [m.sectionData.central_eq]
    intro k
    obtain ⟨a,ha,he⟩ := k.property
    change m.sectionData.space.toRepresentation (k : D) w = w
    rw [←he]
    change m.sectionData.space.toRepresentation (q a) (movedCoordinates V K q hq hk m v) = _
    rw [←movedCoordinates_conjugation]
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    change a * u * a⁻¹ = u
    rw [hu.2 a ha,mul_inv_cancel_right]
  rw [m.central_eq_bot] at hw
  have hv : v = 0 := (movedCoordinates V K q hq hk m).injective (hw.trans (map_zero _).symm)
  exact congrArg (fun x : Additive (⁅V,K⁆ : Subgroup A) => (x.toMul : A)) hv

omit [Finite A] [Finite D] in
private theorem movedCoordinates_relabel {E : Type*} [Group E] (e : D ≃* E)
    (hq' : Function.Surjective (e.toMonoidHom.comp q))
    (hk' : (e.toMonoidHom.comp q).ker = centralizer ((⁅V,K⁆ : Subgroup A) : Set A))
    (a : E) (v : Additive (⁅V,K⁆ : Subgroup A)) :
    movedCoordinates V K q hq hk m
      (NormalElementaryQuotient.representation ⁅V,K⁆ (e.toMonoidHom.comp q) hq' hk' a v) =
      m.sectionData.space.toRepresentation (e.symm a) (movedCoordinates V K q hq hk m v) := by
  obtain ⟨a,rfl⟩ := hq' a
  change movedCoordinates V K q hq hk m
    (NormalElementaryQuotient.representation ⁅V,K⁆ (e.toMonoidHom.comp q) hq' hk'
      ((e.toMonoidHom.comp q) a) v) =
      m.sectionData.space.toRepresentation (e.symm (e (q a))) _
  rw [e.symm_apply_apply]
  have he : NormalElementaryQuotient.representation ⁅V,K⁆ (e.toMonoidHom.comp q) hq' hk'
      ((e.toMonoidHom.comp q) a) v = Additive.ofMul (MulAut.conjNormal a v.toMul) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact NormalElementaryQuotient.representation_apply _ _ hq' hk' a v
  rw [he]
  exact movedCoordinates_conjugation V K q hq hk m a v

include m in
omit [Finite A] [Finite D] in
/-- The actual full commutator has zero fixed subgroup and the required
whole-module coordinates; no block hypothesis is used. -/
theorem moved_wholeModule (eC : K.map q ≃* alternatingGroup (Fin 7)) :
    (⁅V,K⁆ : Subgroup A) ⊓ centralizer (K : Set A) = ⊥ ∧ WholeModule K ⁅V,K⁆ := by
  refine ⟨moved_fixed V K q hq hk m,?_⟩
  have hku := moved_kernel V K q hq hk m
  rcases m.models with ⟨e,heK⟩ | ⟨heK,hd⟩
  · let q' := e.groupEquiv.toMonoidHom.comp q
    have hq' : Function.Surjective q' := e.groupEquiv.surjective.comp hq
    have hk' : q'.ker = centralizer ((⁅V,K⁆ : Subgroup A) : Set A) :=
      (MonoidHom.ker_comp_of_injective q e.groupEquiv.toMonoidHom e.groupEquiv.injective).trans hku
    refine Or.inl ⟨q',hq',hk',?_,(movedCoordinates V K q hq hk m).trans e.linearEquiv,?_⟩
    · exact (map_map _ _ _).symm.trans heK
    · intro a v
      change e.linearEquiv (movedCoordinates V K q hq hk m
        (NormalElementaryQuotient.representation _ q' hq' hk' a v)) = _
      rw [movedCoordinates_relabel V K q hq hk m e.groupEquiv hq' hk',
        e.intertwines,e.groupEquiv.apply_symm_apply]
      rfl
  · let eD : D ≃* K.map q := (MulEquiv.ofBijective (K.map q).subtype
      ⟨(K.map q).subtype_injective,fun a => ⟨⟨a,heK ▸ mem_top a⟩,rfl⟩⟩).symm
    let e := eD.trans eC
    let q' := e.toMonoidHom.comp q
    have hq' : Function.Surjective q' := e.surjective.comp hq
    have hk' : q'.ker = centralizer ((⁅V,K⁆ : Subgroup A) : Set A) :=
      (MonoidHom.ker_comp_of_injective q e.toMonoidHom e.injective).trans hku
    refine Or.inr ⟨q',hq',hk',?_,(movedCoordinates V K q hq hk m).finrank_eq.trans hd⟩
    rw [show K.map q' = (K.map q).map e.toMonoidHom from (map_map _ _ _).symm,
      heK,map_top_of_surjective _ e.surjective]

end CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction
