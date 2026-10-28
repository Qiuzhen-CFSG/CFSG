module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.Basic
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic
/-!
# The marked line criterion for the plane SL₂ Levi

The ordered coordinates of the isotropic plane identify its marked line with
its first coordinate axis. The actual projective Levi preserves this line
exactly when its lower-left entry vanishes. Scalar projectivization does not
change stabilization. This connects the SL₂ upper-root normalizer calculation
to the literal flag in the unitary-five carrier.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, F.1.3
and F.1.12(7), printed pp.260 and 263--264.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.Flag
open PlaneCore
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

/-- The actual plane Levi preserves the flag precisely when it is upper triangular. -/
theorem planeSL_mem_line_iff (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (A : SpecialLinearGroup (Fin 2) F) :
    (planeSLParabolic J c hc hJ A).val ∈ lineParabolic J ↔ A.val 1 0 = 0 := by
  have hp : project J (planeLeviSU J c hc hJ (planeSLtoGL A)) ∈ lineParabolic J ↔
      planeLeviSU J c hc hJ (planeSLtoGL A) ∈ specialStabilizer J (line F) := by
    exact Iff.of_eq (congrArg (fun H : Subgroup J.specialSubgroup =>
      planeLeviSU J c hc hJ (planeSLtoGL A) ∈ H)
      (Subgroup.comap_map_eq_self (ker_project_le_specialStabilizer J (line F))))
  change project J (planeLeviSU J c hc hJ (planeSLtoGL A)) ∈ lineParabolic J ↔ _
  rw [hp, mem_specialStabilizer_iff]
  have hmem (B : SpecialLinearGroup (Fin 2) F) (hb : B.val 1 0 = 0)
      (v : Fin 5 → F) (hv : v ∈ line F) :
      linearAction J (planeLeviSU J c hc hJ (planeSLtoGL B)) v ∈ line F := by
    let w : plane F := ⟨v, line_le_plane F hv⟩
    have he := planeLeviGL_plane J c (planeSLtoGL B) (planeEquiv F w)
    rw [LinearEquiv.symm_apply_apply] at he
    change (planeLeviGL J c (planeSLtoGL B)).val *ᵥ v ∈ line F
    rw [he]
    have hv2 : v 2 = 0 := hv.2.1
    simp [planeEquiv, line, planeSLtoGL, mulVec, dotProduct, Fin.sum_univ_two, w, hv2, hb]
  constructor
  · intro h
    let v : Fin 5 → F := ![1,1,0,0,0]
    have hv : v ∈ line F := by simp [v, line]
    have he := planeLeviGL_plane J c (planeSLtoGL A) ![1,0]
    have hh := (h v).mpr hv
    change (planeLeviGL J c (planeSLtoGL A)).val *ᵥ v ∈ line F at hh
    have hv' : ((planeEquiv F).symm ![1,0]).val = v := rfl
    rw [hv'] at he
    rw [he] at hh
    have hz := hh.2.1
    simpa [planeEquiv, planeSLtoGL, mulVec, dotProduct, Fin.sum_univ_two] using hz
  · intro ha v
    constructor
    · intro hv
      have hi : A⁻¹.val 1 0 = 0 := by simp [adjugate_fin_two, ha]
      have hh := hmem A⁻¹ hi _ hv
      change linearAction J (planeLeviSU J c hc hJ (planeSLtoGL A⁻¹))
        (linearAction J (planeLeviSU J c hc hJ (planeSLtoGL A)) v) ∈ line F at hh
      rw [map_inv, map_inv, map_inv] at hh
      simpa using hh
    · exact hmem A ha v
end Theory.SpecificGroups.UnitaryFive.Flag
