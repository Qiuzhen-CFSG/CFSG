module

public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers
public import Theory.SpecificGroups.Tits.SharpOuterBound.KernelCertificate

/-!
# The kernel of Tits Sylow restriction has order at most two

A pointwise Sylow fixer preserves both intrinsic parabolics. The existing
overlap-centralizer bounds place each reflection displacement inside the
Sylow subgroup. Six certified overlap elements and the original relators
then force the first displacement to be trivial and leave only two second
displacements. Since the Sylow subgroup and the reflections generate Tits,
there are at most two such automorphisms.

Source: Parrott (1972), §5, p.683; the sharp counting step used for the
full automorphism assertion in Aschbacher–Smith F.1.12, printed p.263.
-/

namespace Tits.SharpOuterBound
open Subgroup OuterOddSubgroups ExceptionalParabolics

local notation "g" => atlas1600ParrottAssignment
local notation "NF" => atlas1600SylowTwoNormalForm
local notation "K" => sylowRestriction.ker

private def perm : Atlas1600Group →* Equiv.Perm (Fin 1600) :=
  { toFun := fun x => x.val
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

private theorem perm_injective : Function.Injective perm := by
  intro x y h
  exact Subtype.ext h

private theorem perm_gen (i : ParrottGenerator) :
    perm (g i) = Atlas1600ParrottData.permutation i := atlas1600ParrottAssignment_val i

private theorem perm_nf (n : Fin 2048) :
    perm (NF n) = Atlas1600SylowTwoCertificate.normalForm n :=
  atlas1600SylowTwoNormalForm_val n

private theorem nf_zero : NF 0 = 1 := by
  apply perm_injective
  rw [perm_nf, map_one]
  exact Atlas1600SylowTwoCenterCertificate.normalForm_zero

private theorem s_mem (i : ParrottGenerator) (h1 : i ≠ .r1) (h8 : i ≠ .r8) : g i ∈ S := by
  rw [S, atlas1600SylowTwoSubgroup_eq]
  apply subset_closure
  cases i <;> simp_all

private theorem r1_sq : g .r1 ^ 2 = 1 := by
  simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
    using atlas1600ParrottAssignment_relations .i_r1

private theorem r8_sq : g .r8 ^ 2 = 1 := by
  simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
    using atlas1600ParrottAssignment_relations .i_r8

private theorem first_overlap_witness (i : Fin 6) :
    NF (KernelCertificate.firstWitness i) ∈ reflectionOverlap (g .r1) := by
  refine ⟨atlas1600SylowTwoNormalForm_mem _, ?_⟩
  change g .r1 * NF _ * (g .r1)⁻¹ ∈ S
  have hinv : (g .r1)⁻¹ = g .r1 := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using r1_sq)
  have he : g .r1 * NF (KernelCertificate.firstWitness i) * g .r1 =
      NF (KernelCertificate.firstConjugate i) := by
    apply perm_injective
    simpa only [map_mul, perm_gen, perm_nf, Atlas1600ParrottData.permutation] using
      KernelCertificate.first_conjugate i
  rw [hinv, he]
  exact atlas1600SylowTwoNormalForm_mem _

private theorem second_overlap_witness (i : Fin 6) :
    NF (KernelCertificate.secondWitness i) ∈ reflectionOverlap (g .r8) := by
  refine ⟨atlas1600SylowTwoNormalForm_mem _, ?_⟩
  change g .r8 * NF _ * (g .r8)⁻¹ ∈ S
  have hinv : (g .r8)⁻¹ = g .r8 := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using r8_sq)
  have he : g .r8 * NF (KernelCertificate.secondWitness i) * g .r8 =
      NF (KernelCertificate.secondConjugate i) := by
    apply perm_injective
    simpa only [map_mul, perm_gen, perm_nf, Atlas1600ParrottData.permutation] using
      KernelCertificate.second_conjugate i
  rw [hinv, he]
  exact atlas1600SylowTwoNormalForm_mem _

private theorem displacement_in_sylow (P : Subgroup Atlas1600Group)
    (r : Atlas1600Group) (hr : r ∈ P)
    (hP : ∀ a : sylowStabilizer, P.map a.val.toMonoidHom = P)
    (hc : P ⊓ centralizer (reflectionOverlap r : Set Atlas1600Group) ≤ S)
    (a : K) : r⁻¹ * (a.val : MulAut Atlas1600Group) r ∈ S := by
  apply hc
  refine ⟨P.mul_mem (P.inv_mem hr) ?_, displacement_mem_centralizer a r⟩
  rw [← hP a.val]
  exact mem_map_of_mem a.val.val.toMonoidHom hr

private theorem displacement_test (a : K) (r : Atlas1600Group) (n w : Fin 2048)
    (hn : NF n = r⁻¹ * (a.val : MulAut Atlas1600Group) r)
    (hw : NF w ∈ reflectionOverlap r) :
    Atlas1600SylowTwoCertificate.normalForm n (Atlas1600SylowTwoCertificate.normalForm w 0) =
      Atlas1600SylowTwoCertificate.normalForm w (Atlas1600SylowTwoCertificate.normalForm n 0) := by
  have hc := mem_centralizer_iff.mp (displacement_mem_centralizer a r) (NF w) hw
  rw [← hn] at hc
  have he := congrArg (fun x : Atlas1600Group => perm x 0) hc
  simpa only [map_mul, perm_nf, Equiv.Perm.mul_apply] using he.symm

/-- A pointwise Sylow fixer fixes the first marked reflection. -/
public theorem kernel_fixes_first_reflection (a : K) :
    (a.val : MulAut Atlas1600Group) (g .r1) = g .r1 := by
  obtain ⟨n, hn⟩ := atlas1600SylowTwoNormalForm_surjective
    (displacement_in_sylow first _ reflection_mem_first preserves_first
      first_overlap_centralizer_le a)
  have he : (a.val : MulAut Atlas1600Group) (g .r1) = g .r1 * NF n := by
    rw [hn, mul_inv_cancel_left]
  have hpow : (g .s1 * g .r1) ^ 5 = 1 := by
    simpa only [parrottRelator, map_pow, map_mul, FreeGroup.lift_apply_of]
      using atlas1600ParrottAssignment_relations .vi_s1_r1
  have hpow' := congrArg (a.val : MulAut Atlas1600Group) hpow
  rw [map_pow, map_mul, map_one, he,
    kernel_fixes_sylow a (s_mem .s1 (by decide) (by decide)), ← mul_assoc] at hpow'
  have hp := congrArg (fun x : Atlas1600Group => perm x 0) hpow'
  simp only [map_pow, map_mul, map_one, perm_gen, perm_nf,
    Atlas1600ParrottData.permutation, Equiv.Perm.one_apply] at hp
  have hn0 := KernelCertificate.first_displacement n
    (fun i => displacement_test a _ n _ hn (first_overlap_witness i)) hp
  rw [he, hn0, nf_zero, mul_one]

/-- Only two normal forms can be the second reflection displacement. -/
public theorem kernel_second_reflection_cases (a : K) :
    (a.val : MulAut Atlas1600Group) (g .r8) = g .r8 ∨
    (a.val : MulAut Atlas1600Group) (g .r8) = g .r8 * NF 74 := by
  obtain ⟨n, hn⟩ := atlas1600SylowTwoNormalForm_surjective
    (displacement_in_sylow second _ reflection_mem_second preserves_second
      second_overlap_centralizer_le a)
  have he : (a.val : MulAut Atlas1600Group) (g .r8) = g .r8 * NF n := by
    rw [hn, mul_inv_cancel_left]
  have hpow := congrArg (a.val : MulAut Atlas1600Group) r8_sq
  rw [map_pow, map_one, he] at hpow
  have hp := congrArg (fun x : Atlas1600Group => perm x 0) hpow
  simp only [map_pow, map_mul, map_one, perm_gen, perm_nf,
    Atlas1600ParrottData.permutation, Equiv.Perm.one_apply] at hp
  rcases KernelCertificate.second_displacement n
    (fun i => displacement_test a _ n _ hn (second_overlap_witness i)) hp with h | h
  · exact Or.inl (by simpa only [h, nf_zero, mul_one] using he)
  · exact Or.inr (by simpa only [h] using he)

private theorem kernel_ext {a b : K}
    (h8 : (a.val : MulAut Atlas1600Group) (g .r8) =
      (b.val : MulAut Atlas1600Group) (g .r8)) : a = b := by
  let E := a.val.val.toMonoidHom.eqLocus b.val.val.toMonoidHom
  have hS : S ≤ E := by
    intro x hx
    exact (kernel_fixes_sylow a hx).trans (kernel_fixes_sylow b hx).symm
  have hr1 : closure {g .r1} ≤ E :=
    (closure_le _).mpr (by
      rintro x (rfl : x = _)
      exact (kernel_fixes_first_reflection a).trans (kernel_fixes_first_reflection b).symm)
  have hr8 : closure {g .r8} ≤ E :=
    (closure_le _).mpr (by rintro x (rfl : x = _); exact h8)
  have ht : (⊤ : Subgroup Atlas1600Group) ≤ E := by
    rw [← ExceptionalParabolics.generate]
    exact sup_le (sup_le hS hr1) (sup_le hS hr8)
  apply Subtype.ext
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  exact ht (mem_top x)

/-- At most two full automorphisms fix the certified Sylow subgroup pointwise. -/
public theorem sylowRestriction_kernel_card_le_two : Nat.card K ≤ 2 := by
  classical
  let f : K → Bool := fun a => decide ((a.val : MulAut Atlas1600Group) (g .r8) = g .r8)
  have hf : Function.Injective f := by
    intro a b hab
    apply kernel_ext
    have hab' : ((a.val : MulAut Atlas1600Group) (g .r8) = g .r8) ↔
        ((b.val : MulAut Atlas1600Group) (g .r8) = g .r8) :=
      decide_eq_decide.mp hab
    rcases kernel_second_reflection_cases a with ha | ha
    · exact ha.trans (hab'.mp ha).symm
    · rcases kernel_second_reflection_cases b with hb | hb
      · exact (hab'.mpr hb).trans hb.symm
      · exact ha.trans hb.symm
  simpa only [Nat.card_eq_fintype_card, Fintype.card_bool] using Nat.card_le_card_of_injective f hf

end Tits.SharpOuterBound
