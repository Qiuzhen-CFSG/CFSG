module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Tactic.NoncommRing

/-!
# Idempotent lifting in complete algebras

Let `A` be an algebra over a commutative ring `R`, complete and separated
for the submodules `Iⁿ A`. Every element idempotent modulo `I A` is congruent
to an actual idempotent. No commutativity of `A` is required.

The correction `x ↦ x + (1 - 2x)(x² - x)` squares the error. Its iterates
form an adic Cauchy sequence; completeness gives a limit, and separatedness
makes the limit idempotent. We also prove completeness of finite free
modules by taking limits in a finite basis. The group-algebra matrix
application is in `IntegralLifting.Idempotents`.

Source: the complete-algebra idempotent lifting argument of Feit,
*The Representation Theory of Finite Groups*, I.12.3--4.
-/

public section
noncomputable section
open Submodule Module

namespace AdicIdempotentLift

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

private lemma mul_mem (I J : Ideal R) {x y : A}
    (hx : x ∈ I • (⊤ : Submodule R A)) (hy : y ∈ J • (⊤ : Submodule R A)) :
    x * y ∈ (I * J) • (⊤ : Submodule R A) := by
  refine Submodule.smul_induction_on hx (fun r hr a _ => ?_) (fun u v hu hv => ?_)
  · refine Submodule.smul_induction_on hy (fun s hs b _ => ?_) (fun u v hu hv => ?_)
    · rw [smul_mul_smul_comm]
      exact Submodule.smul_mem_smul (Ideal.mul_mem_mul hr hs) trivial
    · simpa only [mul_add] using Submodule.add_mem _ hu hv
  · simpa only [add_mul] using Submodule.add_mem _ hu hv

private lemma mul_mem_left (I : Ideal R) (x : A) {y : A}
    (hy : y ∈ I • (⊤ : Submodule R A)) :
    x * y ∈ I • (⊤ : Submodule R A) := by
  refine Submodule.smul_induction_on hy (fun s hs b _ => ?_) (fun u v hu hv => ?_)
  · rw [Algebra.mul_smul_comm]
    exact Submodule.smul_mem_smul hs trivial
  · simpa only [mul_add] using Submodule.add_mem _ hu hv

private lemma mul_mem_right (I : Ideal R) {x : A} (hx : x ∈ I • (⊤ : Submodule R A))
    (y : A) : x * y ∈ I • (⊤ : Submodule R A) := by
  refine Submodule.smul_induction_on hx (fun s hs b _ => ?_) (fun u v hu hv => ?_)
  · rw [Algebra.smul_mul_assoc]
    exact Submodule.smul_mem_smul hs trivial
  · simpa only [add_mul] using Submodule.add_mem _ hu hv

private def improve (x : A) : A := x + (1 - 2 * x) * (x * x - x)

private lemma improve_error (x : A) :
    improve x * improve x - improve x =
      (x * x - x) * (x * x - x) * (4 * (x * x - x) - 3) := by
  dsimp [improve]
  noncomm_ring

private lemma improve_sub (x : A) : improve x - x = (1 - 2 * x) * (x * x - x) := by
  dsimp [improve]
  abel

private def approximant (x : A) : ℕ → A
  | 0 => x
  | n + 1 => improve (approximant x n)

private lemma approximant_error (I : Ideal R) (x : A)
    (hx : x * x - x ∈ I • (⊤ : Submodule R A)) (n : ℕ) :
    approximant x n * approximant x n - approximant x n ∈
      I ^ (n + 1) • (⊤ : Submodule R A) := by
  induction n with
  | zero => simpa [approximant] using hx
  | succ n ih =>
    rw [approximant, improve_error]
    apply mul_mem_right
    apply Submodule.pow_smul_top_le I A (show n + 1 + 1 ≤ (n + 1) + (n + 1) by omega)
    rw [pow_add]
    exact mul_mem _ _ ih ih

private lemma approximant_step (I : Ideal R) (x : A)
    (hx : x * x - x ∈ I • (⊤ : Submodule R A)) (n : ℕ) :
    approximant x (n + 1) - approximant x n ∈
      I ^ (n + 1) • (⊤ : Submodule R A) := by
  rw [approximant, improve_sub]
  exact mul_mem_left _ _ (approximant_error I x hx n)

private lemma approximant_cauchy (I : Ideal R) (x : A)
    (hx : x * x - x ∈ I • (⊤ : Submodule R A)) {m n : ℕ} (hmn : m ≤ n) :
    approximant x m ≡ approximant x n [SMOD I ^ m • (⊤ : Submodule R A)] := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    apply ih.trans
    rw [SModEq.sub_mem, ← neg_sub]
    apply Submodule.neg_mem
    apply Submodule.pow_smul_top_le I A (by omega : m ≤ n + 1)
    exact approximant_step I x hx n

/-- Idempotents lift in any algebra complete for the scalar ideal topology. -/
theorem exists_idempotent (I : Ideal R) [IsAdicComplete I A] (x : A)
    (hx : x * x - x ∈ I • (⊤ : Submodule R A)) :
    ∃ e : A, IsIdempotentElem e ∧ e - x ∈ I • (⊤ : Submodule R A) := by
  obtain ⟨e, he⟩ := IsPrecomplete.prec' (I := I) (approximant x)
    (fun h => approximant_cauchy I x hx h)
  have hdiff (n : ℕ) : e - approximant x n ∈ I ^ n • (⊤ : Submodule R A) :=
    (SModEq.sub_mem.mp (he n).symm)
  refine ⟨e, ?_, ?_⟩
  · change e * e = e
    apply sub_eq_zero.mp
    apply IsHausdorff.haus' (I := I)
    intro n
    rw [SModEq.sub_mem, sub_zero]
    have herror := Submodule.pow_smul_top_le I A (Nat.le_succ n)
      (approximant_error I x hx n)
    have hid : e * e - e =
        (e - approximant x n) * e + approximant x n * (e - approximant x n) -
          (e - approximant x n) +
          (approximant x n * approximant x n - approximant x n) := by noncomm_ring
    rw [hid]
    exact Submodule.add_mem _ (Submodule.sub_mem _
      (Submodule.add_mem _ (mul_mem_right _ (hdiff n) e)
        (mul_mem_left _ _ (hdiff n))) (hdiff n)) herror
  · have h := Submodule.add_mem _ (hdiff 1) (approximant_step I x hx 0)
    simpa only [pow_one, approximant, sub_add_sub_cancel] using h

end AdicIdempotentLift

namespace AdicIdempotentLift
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]

/-- Membership in an ideal multiple is detected by all finite-basis coordinates. -/
lemma mem_smul_top_iff (b : Basis ι R M) (I : Ideal R) (x : M) :
    x ∈ I • (⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
  constructor
  · intro hx i
    have h := Submodule.smul_top_le_comap_smul_top I (b.coord i) hx
    simpa using h
  · intro hx
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) trivial

/-- A finite free module over an adically complete ring is adically complete. -/
theorem complete_of_basis (I : Ideal R) [IsAdicComplete I R] (b : Basis ι R M) :
    IsAdicComplete I M where
  haus' x hx := by
    apply b.repr.injective
    ext i
    simp only [map_zero, Finsupp.zero_apply]
    apply IsHausdorff.haus' (I := I)
    intro n
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
    exact (mem_smul_top_iff b _ _).mp (by simpa [SModEq.sub_mem] using hx n) i
  prec' f hf := by
    have hc (i : ι) : ∃ a : R, ∀ n, b.repr (f n) i ≡ a [SMOD I ^ n • (⊤ : Submodule R R)] := by
      apply IsPrecomplete.prec'
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have h := (mem_smul_top_iff b _ _).mp (SModEq.sub_mem.mp (hf hmn)) i
      simpa using h
    choose a ha using hc
    refine ⟨b.equivFun.symm a, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_smul_top_iff b]
    intro i
    have hi := ha i n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hi
    simpa only [map_sub, Finsupp.sub_apply, ← b.coord_apply, b.coord_equivFun_symm] using hi

end AdicIdempotentLift
