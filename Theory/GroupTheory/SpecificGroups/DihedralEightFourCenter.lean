module
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Four-center geometry from a dihedral supplement

Suppose U and D lie in T, the centralizer of U in T lies in D, and D is
dihedral of order eight. If d is a noncentral involution of D centralizing
U, and z is the central involution of D and is central in T, then the
center of C_T(d) is exactly ⟨z,d⟩. Conjugation inside D also fuses d with zd.

The upper center bound follows by centralizing U, then calculating C_D(d).
Only the eight-element dihedral calculation is checked by finite reduction.
This is the local group-theoretic step used in Aschbacher--Smith 14.3.20,
printed pp.997--998.
-/

public section
namespace Subgroup

open Subgroup
private theorem dihedral_data : ∀ z d : DihedralGroup 4,
    z ∈ center (DihedralGroup 4) → z ≠ 1 → d^2 = 1 → d ≠ 1 → d ≠ z →
    (∀ x : DihedralGroup 4, x*d=d*x → x=1 ∨ x=z ∨ x=d ∨ x=z*d) ∧
      ∃ c : DihedralGroup 4, c*d*c⁻¹=z*d := by
  decide +kernel

variable {G : Type*} [Group G]
theorem four_center_of_dihedral_supplement
    (T U D : Subgroup G) (z d : G) (eD : D ≃* DihedralGroup 4)
    (hUT : U ≤ T) (hDT : D ≤ T)
    (hCU : T ⊓ centralizer (U : Set G) ≤ D)
    (hdD : d ∈ D) (hdU : d ∈ centralizer (U : Set G))
    (hzD : z ∈ D) (hzT : z ∈ centralizer (T : Set G)) (hz1 : z ≠ 1)
    (hd2 : d^2 = 1) (hd1 : d ≠ 1) (hdz : d ≠ z) :
    (center (T ⊓ centralizer ({d} : Set G) : Subgroup G)).map
      (T ⊓ centralizer ({d} : Set G)).subtype = closure ({z,d} : Set G) ∧
      IsConj d (z*d) := by
  let zD : D := ⟨z,hzD⟩
  let dD : D := ⟨d,hdD⟩
  have hzC : eD zD ∈ center (DihedralGroup 4) := by
    rw [mem_center_iff]
    intro x
    obtain ⟨y,rfl⟩ := eD.surjective x
    exact (map_mul eD y zD).symm.trans
      ((congrArg eD (Subtype.ext (hzT y (hDT y.property)))).trans (map_mul eD zD y))
  have hz1' : eD zD ≠ 1 := by
    intro he
    exact hz1 (congrArg Subtype.val (eD.injective (he.trans eD.map_one.symm)))
  have hd2' : (eD dD)^2=1 := by
    rw [←map_pow, show dD^2=1 from Subtype.ext hd2, map_one]
  have hd1' : eD dD ≠ 1 := by
    intro he
    exact hd1 (congrArg Subtype.val (eD.injective (he.trans eD.map_one.symm)))
  have hdz' : eD dD ≠ eD zD := fun he => hdz (congrArg Subtype.val (eD.injective he))
  obtain ⟨hcent, c, hc⟩ := dihedral_data (eD zD) (eD dD) hzC hz1' hd2' hd1' hdz'
  let R := T ⊓ centralizer ({d} : Set G)
  have hdR : d ∈ R := ⟨hDT hdD, mem_centralizer_singleton_iff.mpr rfl⟩
  have hUR : U ≤ R := fun u hu => ⟨hUT hu, mem_centralizer_singleton_iff.mpr (hdU u hu)⟩
  have hzR : z ∈ R := ⟨hDT hzD, mem_centralizer_singleton_iff.mpr (hzT d (hDT hdD)).symm⟩
  have hzZ : z ∈ (center R).map R.subtype := by
    refine ⟨⟨z,hzR⟩,mem_center_iff.mpr ?_,rfl⟩
    intro x
    exact Subtype.ext (hzT x x.property.1)
  have hdZ : d ∈ (center R).map R.subtype := by
    refine ⟨⟨d,hdR⟩,mem_center_iff.mpr ?_,rfl⟩
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2)
  refine ⟨le_antisymm ?_ ((closure_le _).mpr ?_), ?_⟩
  · rintro x ⟨a,ha,rfl⟩
    change (a:G) ∈ closure ({z,d}:Set G)
    have haU : (a:G) ∈ centralizer (U : Set G) := by
      intro u hu
      exact congrArg Subtype.val (mem_center_iff.mp ha ⟨u,hUR hu⟩)
    let aD : D := ⟨a,hCU ⟨a.property.1,haU⟩⟩
    have had : eD aD * eD dD = eD dD * eD aD := by
      rw [←map_mul,←map_mul]
      exact congrArg eD (Subtype.ext (mem_centralizer_singleton_iff.mp a.property.2))
    rcases hcent (eD aD) had with hh | hh | hh | hh
    · have he : (a:G)=1 := congrArg Subtype.val (eD.injective (hh.trans eD.map_one.symm))
      exact he.symm ▸ (closure ({z,d}:Set G)).one_mem
    · have he : (a:G)=z := congrArg Subtype.val (eD.injective hh)
      exact he.symm ▸ subset_closure (by simp)
    · have he : (a:G)=d := congrArg Subtype.val (eD.injective hh)
      exact he.symm ▸ subset_closure (by simp)
    · have he : (a:G)=z*d := congrArg Subtype.val (eD.injective (hh.trans (map_mul eD zD dD).symm))
      exact he.symm ▸ (closure ({z,d}:Set G)).mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  · intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hzZ
    · rw [Set.mem_singleton_iff.mp hx]
      exact hdZ
  · have he : (eD.symm c : D)*dD*(eD.symm c : D)⁻¹=zD*dD := by
      apply eD.injective
      simpa only [map_mul,map_inv,eD.apply_symm_apply] using hc
    exact isConj_iff.mpr ⟨(eD.symm c : G), congrArg Subtype.val he⟩

end Subgroup
