module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Ring

/-!
# Detecting kernels in products of odd-prime dihedral groups

A normal subgroup of a product of odd-prime dihedral groups is trivial if
it contains none of the standard rotations. Commuting a nonidentity
coordinate with a rotation or reflection produces a nonzero rotation in
that coordinate; primality then recovers its standard generator.

This is the faithfulness argument in Aschbacher--Smith G.9.2, printed
p.352. It applies to arbitrary monoid-valued homomorphisms, in particular
to the restricted linear actions used in the degree induction.
-/

public section

open DihedralGroup

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralDegree

variable {ι : Type*} [DecidableEq ι] {p : ι → ℕ}

theorem rotation_mem_of_nonzero
    (hp : ∀ i, (p i).Prime) (N : Subgroup (∀ i, DihedralGroup (p i)))
    (i : ι) (a : ZMod (p i)) (ha : a ≠ 0)
    (h : Pi.mulSingle i (r a) ∈ N) : Pi.mulSingle i (r 1) ∈ N := by
  let : Fact (p i).Prime := ⟨hp i⟩
  have := N.pow_mem h a⁻¹.val
  simpa only [← Pi.mulSingle_pow, r_pow, ZMod.natCast_zmod_val,
    mul_inv_cancel₀ ha] using this

theorem normal_eq_bot_of_rotations_not_mem
    (hp : ∀ i, (p i).Prime) (ho : ∀ i, Odd (p i))
    (N : Subgroup (∀ i, DihedralGroup (p i))) [N.Normal]
    (hrot : ∀ i : ι, Pi.mulSingle i (r (1 : ZMod (p i))) ∉ N) : N = ⊥ := by
  apply bot_unique
  intro g hg
  change g = 1
  funext i
  let : Fact (p i).Prime := ⟨hp i⟩
  have htwo : (2 : ZMod (p i)) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 (p i)).mp h
    have he := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left (hp i).ne_one
    have := ho i
    exact (by decide : ¬Odd 2) (he ▸ this)
  have hc (x : DihedralGroup (p i)) :
      Pi.mulSingle i (g i * x * (g i)⁻¹ * x⁻¹) ∈ N := by
    have h := N.mul_mem hg (N.inv_mem
      (Subgroup.Normal.conj_mem inferInstance g hg (Pi.mulSingle i x)))
    convert h using 1
    ext j
    by_cases hj : j = i
    · subst j
      simp [mul_assoc]
    · simp [Pi.mulSingle_eq_of_ne hj, mul_assoc]
  cases hgi : g i with
  | r a =>
    have hh := hc (sr 0)
    simp only [hgi, inv_r, inv_sr, r_mul_sr, sr_mul_r, sr_mul_sr,
      zero_sub, neg_add_rev, neg_neg] at hh
    have ha : a = 0 := by
      by_contra ha
      apply hrot i
      apply rotation_mem_of_nonzero hp N i (a + a) _ hh
      rw [← two_mul]
      exact mul_ne_zero htwo ha
    simp [ha]
  | sr a =>
    have hh := hc (r 1)
    simp only [hgi, inv_sr, inv_r, sr_mul_r, sr_mul_sr, r_mul_r] at hh
    apply False.elim
    apply hrot i
    apply rotation_mem_of_nonzero hp N i (a - (a + 1) + -1) _ hh
    convert neg_ne_zero.mpr htwo using 1
    ring

theorem injective_of_rotations_ne_one {M : Type*} [Monoid M]
    (hp : ∀ i, (p i).Prime) (ho : ∀ i, Odd (p i))
    (f : (∀ i, DihedralGroup (p i)) →* M)
    (hrot : ∀ i, f (Pi.mulSingle i (r 1)) ≠ 1) : Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  exact normal_eq_bot_of_rotations_not_mem hp ho f.ker hrot

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralDegree
