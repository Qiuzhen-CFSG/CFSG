module
public import Theory.Mathieu.M22.CoverDegreeFive
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PerfectCentralCoverLocalSplitting

/-!
# Odd-kernel representations of full M₂₂ covers

An odd action kernel in a quasisimple M₂₂ cover is proper and hence
central. Quotienting that exact kernel gives another full perfect cover
with a faithful representation. The eleven-by-five degree bound therefore
still applies. No faithful action of the original covering center is assumed.

Source application: Aschbacher--Smith A.1.28, printed p.26, and the
centralizer comparison of 4.2.13, printed p.612; H.12.1, p.394.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M22CentralCover

/-- An odd kernel suffices for the degree-five bound away from characteristic eleven. -/
theorem degree_ge_five_of_odd_kernel
    {F E V : Type*} [Field F] [Group E] [Finite E] [IsQuasisimple E]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (e : (E ⧸ center E) ≃* M22)
    (ρ : Representation F E V) (hkodd : Odd (Nat.card ρ.asGroupHom.ker))
    (h11 : (11 : F) ≠ 0) : 5 ≤ Module.finrank F V := by
  let f : PerfectCentralCovering.Cover E M22 := {
    toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
    isPerfect := inferInstance
    ker_le_center := by rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk'] }
  have hk : ρ.asGroupHom.ker ≤ center E := by
    rcases IsQuasisimple.normal_le_center_or_eq_top ρ.asGroupHom.ker with h | h
    · exact h
    have hodd : Odd (Nat.card E) := by simpa only [h,card_top] using hkodd
    have heven : 2 ∣ Nat.card E := (show 2 ∣ Nat.card M22 by rw [m22_order]; decide).trans
      (card_dvd_of_surjective f.toMonoidHom f.surjective)
    exact (hodd.not_two_dvd_nat heven).elim
  have hker : ρ.asGroupHom.ker ≤ f.toMonoidHom.ker := by
    change ρ.asGroupHom.ker ≤ (e.toMonoidHom.comp (QuotientGroup.mk' (center E))).ker
    rwa [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let g := f.quotientKernelSubgroup ρ.asGroupHom.ker hker
  let q := QuotientGroup.quotientKerEquivRange ρ.asGroupHom
  let σ : Representation F (E ⧸ ρ.asGroupHom.ker) V :=
    (Units.coeHom (Module.End F V)).comp (ρ.asGroupHom.range.subtype.comp q.toMonoidHom)
  have hσ : Function.Injective σ :=
    Units.val_injective.comp (ρ.asGroupHom.range.subtype_injective.comp q.injective)
  exact faithful_degree_ge_five g σ hσ h11
end Sporadic.Mathieu.M22CentralCover
