module
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenScalarLift
public import Theory.GroupTheory.CoveringKernelCard

/-!
# The two actual binary unitary covering models

A quasisimple group with trivial two-core mapping onto PSU₃(2ⁿ) is
either that projective group or the actual SU₃ group over the same
Hermitian form. The proved scalar lift supplies a surjection from SU₃.
The two kernels multiply to its scalar-kernel order, which divides three.
If the original kernel is trivial the original projection is an
isomorphism; otherwise the scalar lift is an isomorphism.

Source: Aschbacher--Smith I.1.3 and the covering step in E.2.2(2a),
printed pp.407 and 215--216. This retains the possible odd central cover.
-/

public section
open Subgroup Theory.GroupTheory
open BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover
variable {F L : Type*} [Field F] [Finite F]
  [Group L] [Finite L] [IsQuasisimple L]

theorem binary_cover_models (J : HermitianForm 3 F) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (f : L →* ProjectiveSpecialUnitaryMatrixGroup J) (hf : Function.Surjective f)
    (hcore : pCore 2 L = ⊥) :
    Nonempty (L ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (L ≃* J.specialSubgroup) := by
  obtain ⟨k,hk,hfac⟩ := exists_even_scalar_lift J hn hcard hconj f hf hcore
  have hd : Nat.card f.ker ∣ 3 := by
    have hd := kernel_card_dvd_of_surjective_factor J.specialToProjective f k hk hfac
    rw [card_kernel J hcard hconj] at hd
    exact hd.trans (Nat.gcd_dvd_left 3 (2^n+1))
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd with hone | hthree
  · exact Or.inl ⟨MulEquiv.ofBijective f
      ⟨f.ker_eq_bot_iff.mp (f.ker.eq_bot_of_card_eq hone),hf⟩⟩
  · have hc := kernel_card_eq_mul_of_surjective_factor J.specialToProjective f k hf hk hfac
    have hs : Nat.card J.specialToProjective.ker = 3 := by
      rw [card_kernel J hcard hconj]
      apply Nat.dvd_antisymm (Nat.gcd_dvd_left 3 (2^n+1))
      have hd := kernel_card_dvd_of_surjective_factor J.specialToProjective f k hk hfac
      simpa only [hthree,card_kernel J hcard hconj] using hd
    have hker : Nat.card k.ker = 1 := by rw [hs,hthree] at hc; omega
    exact Or.inr ⟨(MulEquiv.ofBijective k
      ⟨k.ker_eq_bot_iff.mp (k.ker.eq_bot_of_card_eq hker),hk⟩).symm⟩
end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover
