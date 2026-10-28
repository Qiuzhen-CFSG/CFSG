module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalCoordinates
public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# Coordinates on the original Sylow action

The vanishing K-fixed kernel turns the marked natural quotient into actual
coordinates on V_H. The given A-star Sylow image is transported through the
literal residual-star equivalence and the original quotient marking. Sylow
conjugacy then changes basis on every natural summand simultaneously, giving
a surjective field parameter for the action of the original A.

This module does not recognize the reciprocal action of V_H on A. Its output
retains the original local conjugation action and is used by the subsequent
fixed-space and commutator calculations.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.3.7(4), printed p.773, using its preceding natural-summand paragraph.
-/

@[expose] public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] {T : Sylow 2 G} {H A : Subgroup G} {F : BinaryField}

structure NaturalSylowCoordinates (T : Sylow 2 G) (H A : Subgroup G)
    (F : BinaryField) (m : ℕ) where
  le_local : A ≤ H
  coordinates : omegaClosure T H ≃* Multiplicative (Fin m → Fin 2 → F.Carrier)
  parameter : A →* Multiplicative F.Carrier
  surjective : Function.Surjective parameter
  intertwines : ∀ (a : A) (v : omegaClosure T H) (i : Fin m),
    (coordinates (localAction T H (inclusion le_local a) v)).toAdd i =
      ![(coordinates v).toAdd i 0 + (parameter a).toAdd * (coordinates v).toAdd i 1,
        (coordinates v).toAdd i 1]

theorem NaturalQuotientMarking.coordinates_injective
    (c : NaturalQuotientMarking T H F)
    (hfixed : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥) :
    Function.Injective c.coordinates := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [c.kernel]
  apply bot_unique
  intro v hv
  apply Subtype.ext
  exact hfixed.le ⟨v.property,hv⟩

/-- Adapt the actual matrix action to upper-unipotent coordinates using Sylow
conjugacy. The matrix intertwiner is required for the literal local action. -/
theorem NaturalQuotientMarking.sylowCoordinates_of_matrix_action
    (c : NaturalQuotientMarking T H F)
    (hfixed : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hAH : A ≤ H) (σ : A →* SL(2,F.Carrier))
    (P : Sylow 2 SL(2,F.Carrier)) (hP : σ.range = P)
    (he : ∀ (a : A) (v : omegaClosure T H) (i : Fin c.multiplicity),
      (c.coordinates (localAction T H (inclusion hAH a) v)).toAdd i =
        (σ a).val *ᵥ (c.coordinates v).toAdd i) :
    Nonempty (NaturalSylowCoordinates T H A F c.multiplicity) := by
  obtain ⟨b,hb⟩ := MulAction.exists_smul_eq SL(2,F.Carrier) P
    (SpecialLinearGroup.upperUnipotentSylow F.Carrier 2)
  have hbP : (P : Subgroup SL(2,F.Carrier)).map (MulAut.conj b).toMonoidHom =
      SpecialLinearGroup.upperUnipotent F.Carrier := by
    change ((b • P : Sylow 2 SL(2,F.Carrier)) : Subgroup SL(2,F.Carrier)) = _
    rw [hb]
    rfl
  let τ := (MulAut.conj b).toMonoidHom.comp σ
  have hτ : τ.range = SpecialLinearGroup.upperUnipotent F.Carrier := by
    rw [MonoidHom.range_comp, hP, hbP]
  let τ' : A →* SpecialLinearGroup.upperUnipotent F.Carrier :=
    τ.codRestrict _ (fun a => hτ ▸ (show τ a ∈ τ.range from ⟨a,rfl⟩))
  have hτsurj : Function.Surjective τ' := by
    intro t
    obtain ⟨a,ha⟩ := hτ.ge t.property
    exact ⟨a,Subtype.ext ha⟩
  let e := MonoidHom.ofInjective (SpecialLinearGroup.upperUnipotentHom_injective F.Carrier)
  let parameter := e.symm.toMonoidHom.comp τ'
  let B : (Fin c.multiplicity → Fin 2 → F.Carrier) ≃ₗ[F.Carrier]
      (Fin c.multiplicity → Fin 2 → F.Carrier) :=
    LinearEquiv.piCongrRight fun _ => SpecialLinearGroup.toLin' b
  let coordinates := (MulEquiv.ofBijective c.coordinates
    ⟨c.coordinates_injective hfixed,c.surjective⟩).trans B.toAddEquiv.toMultiplicative
  refine ⟨⟨hAH,coordinates,parameter,e.symm.surjective.comp hτsurj,?_⟩⟩
  intro a v i
  have hp : SpecialLinearGroup.upperUnipotentHom F.Carrier (parameter a) = τ a := by
    exact congrArg Subtype.val (e.apply_symm_apply (τ' a))
  have hm : (τ a).val *ᵥ (b.val *ᵥ (c.coordinates v).toAdd i) =
      b.val *ᵥ ((σ a).val *ᵥ (c.coordinates v).toAdd i) := by
    change (b * σ a * b⁻¹) • (b • (c.coordinates v).toAdd i) =
      b • (σ a • (c.coordinates v).toAdd i)
    simp only [mul_smul,inv_smul_smul]
  change b.val *ᵥ (c.coordinates (localAction T H (inclusion hAH a) v)).toAdd i = _
  rw [he, ← hm, ← hp]
  change (SpecialLinearGroup.upperUnipotentHom F.Carrier (parameter a)).val *ᵥ
    (b.val *ᵥ (c.coordinates v).toAdd i) =
    ![(b.val *ᵥ (c.coordinates v).toAdd i) 0 +
      (parameter a).toAdd * (b.val *ᵥ (c.coordinates v).toAdd i) 1,
      (b.val *ᵥ (c.coordinates v).toAdd i) 1]
  ext j
  fin_cases j <;> simp [SpecialLinearGroup.upperUnipotentHom,
    SpecialLinearGroup.transvection_coe, Matrix.mulVec,dotProduct,Fin.sum_univ_two]

variable [Finite G]

/-- Build the upper-unipotent marking from the actual A-star Sylow image.
All identifications use the original star projection and residual quotient. -/
theorem NaturalQuotientMarking.sylowCoordinates
    (c : NaturalQuotientMarking T H F)
    (hfixed : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hTH : (T : Subgroup G) ≤ H) (hmove : ⁅omegaCenter T,H⁆ ≠ ⊥)
    [IsSimpleGroup (outsideResidual H ⧸ pCore 2 (outsideResidual H))]
    (hAH : A ≤ H) (P : Sylow 2 (residualStar T H))
    (hP : (P : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (A.subgroupOf H).map (starProjection T H)) :
    Nonempty (NaturalSylowCoordinates T H A F c.multiplicity) := by
  let α := (starProjection T H).comp (inclusion hAH)
  have hα (a : A) : α a ∈ residualStar T H := by
    have ha : α a ∈ (A.subgroupOf H).map (starProjection T H) :=
      mem_map_of_mem _ a.property
    rw [← hP] at ha
    exact map_subtype_le _ ha
  let φ : A →* residualStar T H := α.codRestrict _ hα
  have hφ : φ.range = P := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      have ha : α a ∈ (P : Subgroup (residualStar T H)).map
          (residualStar T H).subtype := by
        rw [hP]
        exact mem_map_of_mem _ a.property
      obtain ⟨p,hp,he⟩ := ha
      exact (Subtype.ext he : p = φ a) ▸ hp
    · intro hx
      have hh : (x : Star T H) ∈ (A.subgroupOf H).map (starProjection T H) := by
        rw [← hP]
        exact mem_map_of_mem _ hx
      obtain ⟨a,ha,he⟩ := hh
      exact ⟨⟨a,ha⟩,Subtype.ext he⟩
  let e := (residualStarEquiv T H hTH hmove).symm.trans c.quotientEquiv
  let σ := e.toMonoidHom.comp φ
  have hσ : σ.range =
      (P.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow 2 SL(2,F.Carrier)) := by
    rw [MonoidHom.range_comp,hφ]
    rfl
  apply c.sylowCoordinates_of_matrix_action hfixed hAH σ
    (P.mapSurjective (f := e.toMonoidHom) e.surjective) hσ
  intro a v i
  obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective (pCore 2 (outsideResidual H))
    ((residualStarEquiv T H hTH hmove).symm (φ a))
  have hkstar : residualStarMap T H k = α a := by
    have he := congrArg (fun q => (residualStarEquiv T H hTH hmove q : Star T H)) hk
    simpa only [residualStarEquiv_apply,MulEquiv.apply_symm_apply,
      residualStarMap,MonoidHom.comp_apply,φ,MonoidHom.codRestrict_apply] using he
  have haction : residualAction T H k v = localAction T H (inclusion hAH a) v := by
    exact congrArg (fun z => starAction T H z v) hkstar
  have hmatrix : c.quotientEquiv (QuotientGroup.mk' _ k) = σ a :=
    congrArg c.quotientEquiv hk
  rw [← haction, c.intertwines, hmatrix]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
