module

public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.SecondNormalizer.Characteristic
public import Theory.SpecificGroups.Tits.ReeLocalBlockOrders
public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers

/-!
# The intrinsic normalizer defining the second Tits parabolic

The first parabolic has Sylow index five, and its reflection does not
normalize the explicit second center E. Thus its intersection with N(E)
is exactly the Sylow subgroup. The second parabolic acts transitively on
the three nonidentity elements of E. For g in N(E), choose t in the second
parabolic with the same conjugation image of r5. Then t⁻¹g centralizes r5.
Assuming the independent identity P₁ = C(r5), the intersection calculation
puts t⁻¹g in the Sylow subgroup, and hence g in P₂.

Together with E = Z₂(S), this proves invariance of P₂ under every ambient
automorphism preserving S. The first-centralizer identity is the only
explicit premise, retained for independent construction by its owner.

Source: Parrott (1972), pp.672,683; Aschbacher–Smith 2.3.9(7), printed p.526.
-/

@[expose] public section

open Subgroup
namespace Tits.RelativeParabolicNormalizers
open ExceptionalParabolics
local notation "x" => atlas1600R5
local notation "y" => secondCenterMate
local notation "r1" => atlas1600ParrottAssignment ParrottGenerator.r1
local notation "r8" => atlas1600ParrottAssignment ParrottGenerator.r8
local notation "s8" => atlas1600ParrottAssignment ParrottGenerator.s8
local notation "N" => normalizer (secondCenter : Set Atlas1600Group)

private theorem val_mul (a b : Atlas1600Group) : (a * b).val = a.val * b.val := rfl
private theorem val_inv (a : Atlas1600Group) : (a⁻¹).val = a.val⁻¹ := rfl
private theorem val_pow (a : Atlas1600Group) (n : ℕ) : (a ^ n).val = a.val ^ n := rfl
private theorem x_val : (x).val = SecondCenterCertificate.x := by
  simp only [atlas1600R5_eq, val_mul, val_pow, atlas1600ParrottAssignment_val,
    Atlas1600ParrottData.permutation, SecondCenterCertificate.x]
private theorem y_val : (y).val = SecondCenterCertificate.y := by
  simp only [secondCenterMate, val_mul, val_pow, atlas1600ParrottAssignment_val,
    Atlas1600ParrottData.permutation, SecondCenterCertificate.y]
private theorem x_mem : x ∈ secondCenter := mem_sup_left (mem_zpowers _)
private theorem y_mem : y ∈ secondCenter := mem_sup_right (mem_zpowers _)

private theorem conjugate_mem (g : Atlas1600Group) (hg : g ∈ N)
    (a : Atlas1600Group) (ha : a ∈ secondCenter) : g * a * g⁻¹ ∈ secondCenter := by
  rw [← mem_normalizer_iff_map_conj_eq.mp hg]
  exact mem_map_of_mem (MulAut.conj g).toMonoidHom ha

private theorem first_reflection_not_mem_normalizer : r1 ∉ N := by
  intro hr
  have hm := conjugate_mem r1 hr y y_mem
  rcases mem_secondCenter_iff.mp hm with he | he | he | he
  all_goals
    have hp := congrArg (fun a : Atlas1600Group => a.val 0) he
    simp only [val_mul, val_inv, x_val, y_val, atlas1600ParrottAssignment_val,
      Atlas1600ParrottData.permutation] at hp
  · exact SecondNormalizerCertificate.r1_y_out.1 hp
  · exact SecondNormalizerCertificate.r1_y_out.2.2.1 hp
  · exact SecondNormalizerCertificate.r1_y_out.2.1 hp
  · exact SecondNormalizerCertificate.r1_y_out.2.2.2 hp

private theorem first_sylow_relIndex : S.relIndex first = 5 := by
  have h := relIndex_mul_relIndex (⊥ : Subgroup Atlas1600Group) S first bot_le sylow_le_first
  rw [relIndex_bot_left, relIndex_bot_left, sylow_card, ReeLocalBlockOrders.first_card] at h
  omega

/-- Inside the first parabolic, exactly the Sylow subgroup normalizes the second center. -/
theorem first_inf_normalizer_secondCenter : first ⊓ N = S := by
  have hS : S ≤ first ⊓ N := le_inf sylow_le_first
    (sylow_le_second.trans second_le_normalizer_secondCenter)
  apply le_antisymm _ hS
  have h := relIndex_mul_relIndex S (first ⊓ N) first hS inf_le_left
  rw [first_sylow_relIndex] at h
  have hp : Nat.Prime (S.relIndex (first ⊓ N) * (first ⊓ N).relIndex first) :=
    h.symm ▸ (by decide : Nat.Prime 5)
  rcases Nat.prime_mul_iff.mp hp with ⟨_, hj⟩ | ⟨_, hs⟩
  · have hf : first ≤ first ⊓ N := relIndex_eq_one.mp hj
    exact (first_reflection_not_mem_normalizer (hf reflection_mem_first).2).elim
  · exact relIndex_eq_one.mp hs

private theorem reflection_x : r8 * x * r8⁻¹ = y := by
  apply Subtype.ext
  simpa only [val_mul, val_inv, x_val, y_val, atlas1600ParrottAssignment_val,
    Atlas1600ParrottData.permutation] using SecondCenterCertificate.reflection_x

private theorem s8_y : s8 * y * s8⁻¹ = x * y := by
  apply Subtype.ext
  simpa only [val_mul, val_inv, x_val, y_val, atlas1600ParrottAssignment_val,
    Atlas1600ParrottData.permutation, Atlas1600SylowTwoCenterCertificate.generator,
    if_pos rfl, if_true] using SecondCenterCertificate.sylow_y 7

private theorem s8_mem : s8 ∈ S := by
  rw [S, atlas1600SylowTwoSubgroup_eq]
  exact subset_closure (by simp)

private theorem exists_second_conjugator (a : Atlas1600Group)
    (ha : a ∈ secondCenter) (hne : a ≠ 1) :
    ∃ t ∈ second, t * x * t⁻¹ = a := by
  rcases mem_secondCenter_iff.mp ha with he | he | he | he
  · exact (hne he).elim
  · exact ⟨r8, reflection_mem_second, reflection_x.trans he.symm⟩
  · exact ⟨1, second.one_mem, by simpa using he.symm⟩
  · refine ⟨s8 * r8, second.mul_mem (sylow_le_second s8_mem) reflection_mem_second, ?_⟩
    calc
      (s8 * r8) * x * (s8 * r8)⁻¹ = s8 * (r8 * x * r8⁻¹) * s8⁻¹ := by group
      _ = x * y := by rw [reflection_x, s8_y]
      _ = a := he.symm

/-- The second parabolic is the full normalizer of the characteristic Sylow subgroup,
assuming only the independent first-parabolic centralizer identification. -/
theorem second_eq_normalizer_secondCenter
    (hfirst : first = centralizer {x}) : second = N := by
  apply le_antisymm second_le_normalizer_secondCenter
  intro g hg
  have hge := conjugate_mem g hg x x_mem
  have hgne : g * x * g⁻¹ ≠ 1 := by
    intro h
    exact atlas1600R5_ne_one ((MulAut.conj g).map_eq_one_iff.mp h)
  obtain ⟨t, ht, he⟩ := exists_second_conjugator _ hge hgne
  have hconj : (t⁻¹ * g) * x * (t⁻¹ * g)⁻¹ = x := by
    calc
      (t⁻¹ * g) * x * (t⁻¹ * g)⁻¹ = t⁻¹ * (g * x * g⁻¹) * t := by group
      _ = t⁻¹ * (t * x * t⁻¹) * t := by rw [← he]
      _ = x := by group
  have hc : t⁻¹ * g ∈ first := by
    rw [hfirst, mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp hconj
  have hn : t⁻¹ * g ∈ N :=
    (N).mul_mem ((N).inv_mem (second_le_normalizer_secondCenter ht)) hg
  have hs : t⁻¹ * g ∈ S := first_inf_normalizer_secondCenter.le ⟨hc, hn⟩
  simpa only [mul_inv_cancel_left] using second.mul_mem ht (sylow_le_second hs)

/-- Every Sylow-preserving automorphism preserves the second parabolic. -/
theorem second_stabilized_of_first_centralizer
    (hfirst : first = centralizer {x}) (β : MulAut Atlas1600Group)
    (hβ : atlas1600SylowTwoSubgroup.map β.toMonoidHom = atlas1600SylowTwoSubgroup) :
    second.map β.toMonoidHom = second :=
  second_stabilized_of_characteristic_normalizer secondCenter_characteristic
    (second_eq_normalizer_secondCenter hfirst) β hβ

end Tits.RelativeParabolicNormalizers

end
