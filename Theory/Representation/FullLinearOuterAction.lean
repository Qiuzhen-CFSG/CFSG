module
public import Theory.Representation.BinaryOffender.IrreducibleSection
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.SpecificGroups.BinaryLinear.Parabolics

/-!
# Commuting actors in a full normal constituent

A faithful full constituent action transports conjugation by its stabilizer
into inner conjugation by the literal linear action. Consequently a commuting
actor fixes that linear action whenever the full linear group is centerless.
This retains the maps needed for the exceptional degree-four argument in
Aschbacher--Smith G.10.15(3), printed p.363.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender
namespace Representation.BinaryOffender

/-- The geometric obstruction needed to exclude an outer actor centralizing
all transvections with one nonzero center. This is an input proposition;
its validity in a specified dimension must be proved separately. -/
@[expose] def FullCenterOuterObstruction (V : Type*) [AddCommGroup V]
    [Module (ZMod 2) V] : Prop :=
  ∀ (a : MulAut (LinearMap.GeneralLinearGroup (ZMod 2) V)),
    a ∉ MulAut.innerSubgroup _ → ∀ i : V, i ≠ 0 →
    ¬ (∀ (f : Module.Dual (ZMod 2) V) (hf : f i = 0),
      a ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm
        (BinaryLinear.transvection i f hf)) =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm
        (BinaryLinear.transvection i f hf))

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) (H : Subgroup D) [H.Normal]
  (I : Submodule (ZMod 2) V) (hI : H ≤ subspaceStabilizer ρ I)
  (e : H ≃* LinearMap.GeneralLinearGroup (ZMod 2) I)
  (he : ∀ a, e a = (invariantSubspace ρ H I hI).toRepresentation.asGroupHom a)

include he

/-- The stabilizer acts on a full normal constituent by its actual linear map. -/
theorem normal_full_action_conjugation (y : subspaceStabilizer ρ I) :
    MulAut.congr e (MulAut.conjNormal (y : D)) =
      MulAut.conj ((stabilizerRepresentation ρ I).asGroupHom y) := by
  apply MulEquiv.ext
  intro k
  obtain ⟨a, rfl⟩ := e.surjective k
  change e (MulAut.conjNormal (y : D) (e.symm (e a))) =
    (stabilizerRepresentation ρ I).asGroupHom y * e a *
      ((stabilizerRepresentation ρ I).asGroupHom y)⁻¹
  rw [e.symm_apply_apply]
  rw [he, he, ← map_inv]
  apply Units.ext
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  change ρ ((y : D) * (a : D) * (y : D)⁻¹) u =
    ρ (y : D) (ρ (a : D) (ρ (y : D)⁻¹ u))
  simp only [map_mul, Module.End.mul_apply]

/-- A commuting ambient actor fixes each stabilizer action under the transported
conjugation automorphism. No faithfulness of the stabilizer is assumed. -/
theorem normal_full_action_fixed_of_commute
    (hc : center (LinearMap.GeneralLinearGroup (ZMod 2) I) = ⊥)
    (x : D) (y : subspaceStabilizer ρ I) (hxy : Commute (y : D) x) :
    MulAut.congr e (MulAut.conjNormal x)
      ((stabilizerRepresentation ρ I).asGroupHom y) =
      (stabilizerRepresentation ρ I).asGroupHom y := by
  let c : D →* MulAut (LinearMap.GeneralLinearGroup (ZMod 2) I) :=
    (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal
  have hcomm := hxy.map c
  change Commute (MulAut.congr e (MulAut.conjNormal (y : D)))
    (MulAut.congr e (MulAut.conjNormal x)) at hcomm
  rw [normal_full_action_conjugation ρ H I hI e he y] at hcomm
  apply Theory.GroupTheory.conj_injective_of_center_eq_bot hc
  have hh : ∀ (a : MulAut (LinearMap.GeneralLinearGroup (ZMod 2) I)) b,
      MulAut.conj (a b) = a * MulAut.conj b * a⁻¹ := by
    intro a b
    ext z : 1
    simp
  rw [hh, hcomm.eq.symm, mul_inv_cancel_right]

end Representation.BinaryOffender
