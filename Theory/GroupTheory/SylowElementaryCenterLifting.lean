module
public import Theory.GroupTheory.SylowCharacteristicKernelLifting
public import Theory.GroupTheory.PGroup.OmegaCenterIn

/-!
# Lifting the elementary Sylow center

The squares of the full Sylow center generate a characteristic subgroup.
An elementary image center puts those squares in the residual-centralized
kernel, so characteristic-normal exclusion kills them. No central
complement or disappearance of the original fixed layer is assumed.

Source: Niles, *Pushing-up in finite groups* (1979), the final
characteristic-kernel argument on p.62. The original Baumann application
is in NonbinarySymplectic.CriticalReduction.RootProductCenter.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement

namespace Theory.GroupTheory

variable {G X : Type*} [Group G] [Finite G] [Group X]

/-- An elementary image center lifts through a residual-centralized kernel
when the source Sylow has no nontrivial characteristic ambient-normal subgroup. -/
theorem omegaCenterIn_eq_centerIn_of_image (S : Sylow 2 G) (hno : NoCharacteristicNormal (S : Subgroup G))
    (f : G →* X) (hk : pResidual 2 G ≤ centralizer (f.ker : Set G))
    (he : omegaCenterIn ((S : Subgroup G).map f) = centerIn ((S : Subgroup G).map f)) :
    omegaCenterIn (S : Subgroup G) = centerIn (S : Subgroup G) := by
  let A : Subgroup S := closure {x | ∃ z : S, z ∈ center S ∧ x = z^2}
  let : A.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a
    apply (closure_le _).mpr
    rintro _ ⟨z,hz,rfl⟩
    change a (z^2) ∈ A
    rw [map_pow]
    apply Subgroup.subset_closure
    refine ⟨a z,?_,rfl⟩
    exact characteristic_iff_le_comap.mp (inferInstance : (center S).Characteristic) a hz
  have hAk : A.map (S : Subgroup G).subtype ≤ f.ker := by
    rw [map_le_iff_le_comap]
    apply (closure_le _).mpr
    rintro _ ⟨z,hz,rfl⟩
    change f ((z:G)^2)=1
    rw [map_pow]
    have hzc : f (z:G) ∈ centerIn ((S : Subgroup G).map f) := by
      refine ⟨mem_map_of_mem f z.property,?_⟩
      rintro _ ⟨y,hy,rfl⟩
      have hh : y * (z:G) = (z:G) * y :=
        congrArg (fun x : S => (x : G)) (mem_center_iff.mp hz ⟨y,hy⟩)
      simpa only [map_mul] using congrArg f hh
    rw [←he] at hzc
    exact ((mem_omegaCenterIn_iff _ _).mp hzc).2.2
  have hAb := characteristic_eq_bot_of_residual_centralizes S hno f.ker hk A hAk
  apply le_antisymm
  · intro z hz
    exact ⟨((mem_omegaCenterIn_iff _ _).mp hz).1,((mem_omegaCenterIn_iff _ _).mp hz).2.1⟩
  · intro z hz
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨hz.1,hz.2,?_⟩
    let s : S := ⟨z,hz.1⟩
    have hsz : s ∈ center S := mem_center_iff.mpr (fun y => Subtype.ext (hz.2 y y.property))
    have hm : s^2 ∈ A := Subgroup.subset_closure ⟨s,hsz,rfl⟩
    exact congrArg (fun x : S => (x : G)) (mem_bot.mp (hAb ▸ hm))


end Theory.GroupTheory
