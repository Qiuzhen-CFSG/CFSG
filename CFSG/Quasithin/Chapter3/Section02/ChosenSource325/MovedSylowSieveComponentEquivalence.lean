module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveComponentAction
public import Theory.Representation.BinaryOffender.InvariantAction
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveExterior

/-!
# Constituent equivalences through the literal component image

An equivalence over the component's actual action image lifts along the
original subspace inclusions. When the component is SL₅(2), the common-offender
test identifies its ten-dimensional constituents without twisting the actor.
The chosen-seed consumer is `SeedAlternativesMovedSylowExterior`.

Source: Aschbacher--Smith D.3.5(5), printed p.196.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) H W)

theorem nested_invariant_equiv
    (U : Submodule (ZMod 2) W) (K : Subgroup H)
    (hKU : K ≤ subspaceStabilizer ρ U)
    (I J : Submodule (ZMod 2) U)
    (hI : restrictedSubgroup ρ U K ≤ subspaceStabilizer (subspaceImageRepresentation ρ U) I)
    (hJ : restrictedSubgroup ρ U K ≤ subspaceStabilizer (subspaceImageRepresentation ρ U) J)
    (hI' : K ≤ subspaceStabilizer ρ (I.map U.subtype))
    (hJ' : K ≤ subspaceStabilizer ρ (J.map U.subtype))
    (e : Representation.Equiv
      (invariantSubspace (subspaceImageRepresentation ρ U) _ I hI).toRepresentation
      (invariantSubspace (subspaceImageRepresentation ρ U) _ J hJ).toRepresentation) :
    Nonempty (Representation.Equiv
      (invariantSubspace ρ K (I.map U.subtype) hI').toRepresentation
      (invariantSubspace ρ K (J.map U.subtype) hJ').toRepresentation) := by
  let ai := Submodule.equivMapOfInjective U.subtype U.subtype_injective I
  let aj := Submodule.equivMapOfInjective U.subtype U.subtype_injective J
  let f := restrictedActionSurjection ρ U K hKU
  let E := ai.symm.trans (e.toLinearEquiv.trans aj)
  refine ⟨Representation.Equiv.mk E ?_⟩
  intro k
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := ai.surjective v
  have hi : (invariantSubspace ρ K (I.map U.subtype) hI').toRepresentation k (ai w) =
      ai ((invariantSubspace (subspaceImageRepresentation ρ U) _ I hI).toRepresentation (f k) w) := rfl
  have hE (w : I) : E (ai w) = aj (e w) :=
    congrArg (fun v : I => aj (e v)) (ai.symm_apply_apply w)
  change E ((invariantSubspace ρ K (I.map U.subtype) hI').toRepresentation k (ai w)) =
    (invariantSubspace ρ K (J.map U.subtype) hJ').toRepresentation k (E (ai w))
  have hj (z : J) :
      aj ((invariantSubspace (subspaceImageRepresentation ρ U) _ J hJ).toRepresentation (f k) z) =
      (invariantSubspace ρ K (J.map U.subtype) hJ').toRepresentation k (aj z) := rfl
  exact (congrArg E hi).trans ((hE _).trans
    ((congrArg aj (IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (f k) w)).trans
      ((hj (e w)).trans
        (congrArg ((invariantSubspace ρ K (J.map U.subtype) hJ').toRepresentation k) (hE w).symm))))
theorem invariant_equiv_of_common_budget_SL5
    (K : Subgroup H) (I J : Submodule (ZMod 2) W)
    (hI : IsIrrPlus ρ K I) (hJ : IsIrrPlus ρ K J)
    (hz : fixedSpace ρ K = ⊥)
    (e : K ≃* SL5TenDimensional.Group)
    (hi : Module.finrank (ZMod 2) I = 10) (hj : Module.finrank (ZMod 2) J = 10)
    (A : Subgroup H) (hA : IsElementaryTwo A) (hAK : A ≤ K)
    (hbi : fixedCodim (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A) ≤ rank A)
    (hbj : fixedCodim (subspaceImageRepresentation ρ J) (restrictedSubgroup ρ J A) ≤ rank A) :
    Nonempty (Representation.Equiv (invariantSubspace ρ K I hI.choose).toRepresentation
      (invariantSubspace ρ K J hJ.choose).toRepresentation) := by
  let τ := (invariantSubspace ρ K I hI.choose).toRepresentation
  let σ := (invariantSubspace ρ K J hJ.choose).toRepresentation
  let : IsIrreducible τ := invariant_irreducible_of_isIrrPlus ρ K I hI (by rw [hz,inf_bot_eq])
  let : IsIrreducible σ := invariant_irreducible_of_isIrrPlus ρ K J hJ (by rw [hz,inf_bot_eq])
  exact ten_dimensional_equiv_of_marked_common_offender τ σ e hi hj (A.subgroupOf K)
    (component_offender_of_restricted_budget ρ K A I hI.choose hAK hA hbi)
    (component_offender_of_restricted_budget ρ K A J hJ.choose hAK hA hbj)

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
