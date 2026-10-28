module

public import Theory.SpecificGroups.PSL3.OrdinaryCenterRecognition
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Marked perfect covers of PSL₃ in odd binary degree

For a field of order 2ⁿ with odd n greater than one, the ordinary center
bound divides gcd(3,2ⁿ−1) = 1. The whole center is therefore trivial.
The scalar-cover lift is an isomorphism and preserves the supplied
projective marking. If the initial marking uses any central normal kernel,
its equality with the whole center is proved first from the centerlessness
of PSL₃; it is never assumed as a quotient convention.

Source: Aschbacher–Smith A.2.12(I), A.2.18 and I.1.3(2), printed pp.36,
40 and407. The intended application is the full overcomponent in
10.2.3(4), printed p.747, after its projective quotient has been recognized.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
namespace Matrix.PSL3.OddDegreeCentralRecognition
variable {F : Type*} [Field F] [Finite F]
variable {L : Type*} [Group L] [Group.IsPerfect L]
omit [Field F] [Finite F] in
private theorem field_ne_two_four {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hF : Nat.card F = 2^n) : Nat.card F ≠ 2 ∧ Nat.card F ≠ 4 := by
  have hn3 : 3 ≤ n := by have := Nat.odd_iff.mp ho; omega
  have h8 : 8 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn3
  omega

/-- Odd binary degree kills the full center of the marked perfect cover. -/
theorem center_eq_bot {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hF : Nat.card F = 2^n) (e : L ⧸ center L ≃* PSL(3,F)) : center L = ⊥ := by
  obtain ⟨h2,h4⟩ := field_ne_two_four hn ho hF
  have hd := OrdinaryCenterRecognition.center_card_dvd h2 h4 e
  rw [hF,(Nat.BinaryTorusParity.coprime_three_sub_one ho).gcd_eq_one] at hd
  exact (center L).eq_bot_of_card_eq (Nat.dvd_one.mp hd)

/-- The scalar lift is an isomorphism with its original projective triangle. -/
theorem marked_recognition {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hF : Nat.card F = 2^n) (e : L ⧸ center L ≃* PSL(3,F)) :
    center L = ⊥ ∧ ∃ j : SL(3,F) ≃* L,
      (centralQuotientCover e).toMonoidHom.comp j.toMonoidHom = projection F := by
  have hz := center_eq_bot hn ho hF e
  obtain ⟨h2,h4⟩ := field_ne_two_four hn ho hF
  obtain ⟨k,hks,hk⟩ := OrdinaryCenterRecognition.exists_scalar_lift h2 h4 e
  have hpk : (projection F).ker = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [card_projectionKernel,hF,(Nat.BinaryTorusParity.coprime_three_sub_one ho).gcd_eq_one]
  have hki : Function.Injective k := by
    intro x y hxy
    apply (projection F).ker_eq_bot_iff.mp hpk
    have hh := congrArg (centralQuotientCover e).toMonoidHom hxy
    change ((centralQuotientCover e).toMonoidHom.comp k) x =
      ((centralQuotientCover e).toMonoidHom.comp k) y at hh
    rwa [hk] at hh
  exact ⟨hz,MulEquiv.ofBijective k ⟨hki,hks⟩,hk⟩

omit [Finite F] [Group.IsPerfect L] in
private theorem central_kernel_eq_center (N : Subgroup L) [N.Normal]
    (hN : N ≤ center L) (e : L ⧸ N ≃* PSL(3,F)) : N = center L := by
  apply le_antisymm hN
  intro x hx
  have hz : e (QuotientGroup.mk x) ∈ center PSL(3,F) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z,rfl⟩ := e.surjective y
    obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective N z
    change e ((QuotientGroup.mk' N) z) * e ((QuotientGroup.mk' N) x) =
      e ((QuotientGroup.mk' N) x) * e ((QuotientGroup.mk' N) z)
    rw [←map_mul,←map_mul,←map_mul,←map_mul,mem_center_iff.mp hx z]
  rw [Group.IsPerfect.center_quotient_center_eq_bot SL(3,F),mem_bot] at hz
  exact (QuotientGroup.eq_one_iff x).mp (e.injective (hz.trans e.map_one.symm))

/-- Recognition through the literal central kernel, including its triviality. -/
theorem central_quotient_marked_recognition {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hF : Nat.card F = 2^n) (N : Subgroup L) [N.Normal]
    (hN : N ≤ center L) (e : L ⧸ N ≃* PSL(3,F)) :
    N = ⊥ ∧ center L = ⊥ ∧ ∃ j : SL(3,F) ≃* L,
      (e.toMonoidHom.comp (QuotientGroup.mk' N)).comp j.toMonoidHom = projection F := by
  have hNc := central_kernel_eq_center N hN e
  let e' : L ⧸ center L ≃* PSL(3,F) :=
    (QuotientGroup.quotientMulEquivOfEq hNc.symm).trans e
  obtain ⟨hz,j,hj⟩ := marked_recognition hn ho hF e'
  refine ⟨hNc.trans hz,hz,j,?_⟩
  ext x
  exact DFunLike.congr_fun hj x
end Matrix.PSL3.OddDegreeCentralRecognition
