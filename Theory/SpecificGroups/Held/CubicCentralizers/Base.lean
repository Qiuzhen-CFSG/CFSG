module
public import Theory.SpecificGroups.Held.OddCubeCandidates.Cardinality
import all Theory.SpecificGroups.Held.OddCubeCandidates.Cardinality
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Fusion.Normalizer
public import Mathlib.GroupTheory.Sylow
/-! The literal extraspecial Sylow-three subgroup and its central cubic.
The certified order27 and the normalizer order show it is Sylow. Its collected
normal forms will reduce arbitrary cubics to the finite fusion certificates.
Source: ATLAS HeG1-p2058B0; Aschbacher–Smith 2.4.25, p.543. -/
public section
open Subgroup
open scoped Pointwise
namespace Held.CubicCentralizers
open OddCubeCandidates OddCubeCandidates.CardinalityCertificates
@[expose] def x : He := threeFirst
@[expose] def y : He := threeSecond
@[expose] def z : He := y⁻¹ * x⁻¹ * y * x
@[expose] def normalForm (t : Fin 27) : He :=
  x ^ (t.val % 3) * y ^ (t.val / 3 % 3) * z ^ (t.val / 9)
theorem representation_x : representation x = threeX := threeX_eq.symm
theorem representation_y : representation y = threeY := threeY_eq.symm
theorem representation_z : representation z = threeZ := by
  simp only [z,map_mul,map_inv,representation_x,representation_y,threeZ_eq]
theorem x_cube : x^3=1 := by
  apply representation_injective
  rw [map_pow,map_one,representation_x,threeX_pow]
theorem y_cube : y^3=1 := by
  apply representation_injective
  rw [map_pow,map_one,representation_y,threeY_pow]
theorem z_cube : z^3=1 := by
  apply representation_injective
  rw [map_pow,map_one,representation_z,threeZ_pow]
theorem xz_commute : Commute x z := by
  apply representation_injective
  simpa only [map_mul,representation_x,representation_z] using threeX_commute.eq
theorem yz_commute : Commute y z := by
  apply representation_injective
  simpa only [map_mul,representation_y,representation_z] using threeY_commute.eq
theorem yx_swap : y*x=x*y*z := by simp only [z]; group

theorem normalForm_cover {g : He} (hg : g ∈ three) : ∃ t : Fin 27, normalForm t = g := by
  obtain ⟨⟨i,j,k⟩,ht⟩ :=
    CardinalityProof.cover x y z 3 (by decide) x_cube y_cube z_cube xz_commute yz_commute yx_swap hg
  refine ⟨⟨i.val+3*j.val+9*k.val,by omega⟩,?_⟩
  have hi : (i.val+3*j.val+9*k.val)%3=i.val := by omega
  have hj : (i.val+3*j.val+9*k.val)/3%3=j.val := by omega
  have hk : (i.val+3*j.val+9*k.val)/9=k.val := by omega
  simpa only [normalForm,hi,hj,hk] using ht

theorem three_le_centralizer_z : three ≤ centralizer ({z} : Set He) := by
  apply (closure_le _).mpr
  intro u hu
  rcases (show u=threeFirst ∨ u=threeSecond by simpa using hu) with rfl | rfl
  · exact mem_centralizer_singleton_iff.mpr xz_commute.eq
  · exact mem_centralizer_singleton_iff.mpr yz_commute.eq

theorem twenty_seven_dvd_centralizer_z : 27 ∣ Nat.card (centralizer ({z} : Set He)) := by
  rw [←card_three]
  exact card_dvd_of_le three_le_centralizer_z

theorem three_sylow : IsPGroup 3 three ∧ ¬ 3 ∣ three.index := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨IsPGroup.of_card (n := 3) card_three,?_⟩
  intro hi
  have hd : 81 ∣ Nat.card He := by
    rw [←three.card_mul_index,card_three]
    exact Nat.mul_dvd_mul_left 27 hi
  have he : Nat.card He ∣ Nat.card LocalPairs.PermutationNormalizer :=
    card_dvd_of_injective (inclusion permutationGroup.le_normalizer)
      (inclusion_injective _)
  have hb := hd.trans he
  rw [OuterInvolution.Fusion.normalizer_card] at hb
  norm_num at hb

end Held.CubicCentralizers
