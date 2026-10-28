module
public import Theory.SpecificGroups.DihedralProduct.CentralEnlargementModel
/-!
# Detecting the canonical dihedral action kernel by the center

The four canonical central enlargements and the four central coordinate
involutions carry the same permutation action. Transporting the intrinsic
center-kernel theorem through the chosen marking gives the exact kernel
needed for ambient normalizer actions.

Source: Aschbacher–Smith 10.2.1, printed p.743.
-/
public section
open Subgroup
namespace DihedralProductCanonical
variable {G : Type*} [Group G]
theorem transportedFactorAction_eq_one_iff (e : G ≃* (Fin 4 → D)) (a : MulAut G) :
    transportedFactorAction e a = 1 ↔ ∀ z ∈ center G, a z = z := by
  rw [show transportedFactorAction e a = factorAction ((MulAut.congr e) a) from rfl,
    factorAction_eq_one_iff]
  constructor
  · intro h z hz
    apply e.injective
    have hze : e z ∈ center (Fin 4 → D) := by
      apply mem_center_iff.mpr
      intro x
      obtain ⟨y,rfl⟩ := e.surjective x
      simpa only [←map_mul] using congrArg e (mem_center_iff.mp hz y)
    have hh := h (e z) hze
    change e (a (e.symm (e z))) = e z at hh
    simpa only [e.symm_apply_apply] using hh
  · intro h z hz
    have hze : e.symm z ∈ center G := by
      apply mem_center_iff.mpr
      intro x
      apply e.injective
      simpa only [map_mul,e.apply_symm_apply] using mem_center_iff.mp hz (e x)
    change e (a (e.symm z)) = z
    rw [h _ hze,e.apply_symm_apply]
end DihedralProductCanonical
