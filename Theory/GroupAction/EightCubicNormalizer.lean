module
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Tactic.IntervalCases

/-!
# Normalizers of cubic point stabilizers on groups of order eight

A nonidentity cubic automorphism fixes exactly two elements: fixed-point
counting modulo three and divisibility of the fixed subgroup's order leave
only two or eight, and eight would make the automorphism trivial. Thus a
subgroup of automorphisms containing a cubic and fixing a nonidentity point
has a unique such common fixed point. Its normalizer fixes that point too.

Source application: Aschbacher–Smith, proof of 14.7.32, printed p.1058,
refs/quasithin.pdf. This controls the original point-parabolic residual
through the natural action of L/O₂(L), without a normalizer recognition input.
-/

public section
open Subgroup
namespace MulAut
variable {D : Type*} [Group D] [Finite D]

/-- A nontrivial cubic on a group of order eight fixes exactly two elements. -/
theorem cubic_fixed_card_of_card_eight (b : MulAut D) (hb : b^3=1) (hne : b≠1)
    (hc : Nat.card D=8) : Nat.card b.fixedSubgroup=2 := by
  let A := zpowers b
  have hp : IsPGroup 3 A := IsPGroup.of_card_dvd_pow (n:=1) (by
    simpa only [A,Nat.card_zpowers,pow_one] using orderOf_dvd_of_pow_eq_one hb)
  have heq : FixedPoints.subgroup A D=b.fixedSubgroup := by
    ext x
    constructor
    · intro hx
      exact (MulAut.mem_fixedSubgroup b x).mpr (hx ⟨b,mem_zpowers b⟩)
    · intro hx
      have hle : A ≤ MulAction.stabilizer (MulAut D) x :=
        zpowers_le.mpr ((MulAut.mem_fixedSubgroup b x).mp hx)
      exact fun y => hle y.property
  have hm := hp.card_modEq_card_fixedPoints D
  change Nat.card D % 3=Nat.card (FixedPoints.subgroup A D) % 3 at hm
  rw [heq,hc] at hm
  have hd : Nat.card b.fixedSubgroup ∣ 8 := hc ▸ b.fixedSubgroup.card_subgroup_dvd_card
  have htop : b.fixedSubgroup≠⊤ := by
    intro he
    apply hne
    ext x
    exact (MulAut.mem_fixedSubgroup b x).mp (he ▸ mem_top x)
  obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card b.fixedSubgroup∣2^3 from hd)
  interval_cases k
  · simp only [pow_zero] at he; omega
  · simpa only [pow_one] using he
  · have hh : Nat.card b.fixedSubgroup = 4 := by simpa only [Nat.reducePow] using he
    omega
  · exact (htop ((card_eq_iff_eq_top _).mp (he.trans hc.symm))).elim

/-- A cubic makes the nonidentity common fixed point unique, so the full
normalizer of the acting subgroup preserves it. -/
theorem normalizer_fixes_point_of_cubic (A : Subgroup (MulAut D))
    (hc : Nat.card D=8) (z : D) (hz : z≠1)
    (hfix : ∀ a ∈ A, a z=z)
    (b : MulAut D) (hb : b∈A) (hb3 : orderOf b=3) :
    normalizer (A : Set (MulAut D)) ≤ MulAction.stabilizer (MulAut D) z := by
  have hcard := cubic_fixed_card_of_card_eight b (hb3 ▸ pow_orderOf_eq_one b)
    (by intro he; rw [he,orderOf_one] at hb3; omega) hc
  obtain ⟨w,hw,hall⟩ := (Nat.card_eq_two_iff' (1 : b.fixedSubgroup)).mp hcard
  have huniq (v : D) (hv : v≠1) (hvf : b v=v) : v=z := by
    let v' : b.fixedSubgroup := ⟨v,(MulAut.mem_fixedSubgroup b v).mpr hvf⟩
    let z' : b.fixedSubgroup := ⟨z,(MulAut.mem_fixedSubgroup b z).mpr (hfix b hb)⟩
    have he1 : v'=w := hall v' (fun he => hv (congrArg Subtype.val he))
    have he2 : z'=w := hall z' (fun he => hz (congrArg Subtype.val he))
    exact congrArg Subtype.val (he1.trans he2.symm)
  intro a ha
  apply huniq (a z) (fun he => hz (a.injective (he.trans a.map_one.symm)))
  have hba : a⁻¹*b*a ∈ A :=
    (mem_normalizer_iff.mp ((normalizer (A : Set (MulAut D))).inv_mem ha) b).mp hb
  have hf := congrArg a (hfix _ hba)
  simpa only [MulAut.mul_apply,MulAut.inv_apply,MulEquiv.apply_symm_apply] using hf
end MulAut
