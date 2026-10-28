module
public import Theory.AtlasPort.OtherSporadic.Algebra.BinaryWalshRank

/-!
# Small binary quadratic forms with free cubic symmetry

The Walsh-square identity gives the two possible nonsingular-vector counts
of a nondegenerate binary quadratic form. In even dimension at most six,
divisibility of this count by three distinguishes the sign: the counts are
0, 3, 6 and 36. A fixed-point-free cubic group supplies that divisibility.
The consumer is the symplectic normal-cubic exclusion used in G.11.5.

Source: the elementary quadratic-form count in the proof of Aschbacher--Smith
G.9.4 and G.11.5, printed pp.354--355 and365; the Walsh-square identity is
provided by the cited ATLAS port.
-/

public section
open Module Atlas.Algebra
namespace QuadraticForm.BinarySmall
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
private theorem walsh_card (Q : QuadraticForm (ZMod 2) V) [Fintype V] :
    binaryWalsh Q 0 = (Fintype.card V : ℤ) - 2 * Nat.card {v : V // Q v = 1} := by
  classical
  have hv (v : V) : binaryWalshSign (Q v) = 1 - 2 * (if Q v = 1 then 1 else 0 : ℤ) := by
    generalize Q v = a
    fin_cases a <;> decide
  simp only [binaryWalsh, AddMonoidHom.zero_apply, add_zero, hv, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp

/-- In dimensions at most six a free cubic symmetry determines the quadratic census. -/
theorem nonsingular_card_cases (Q : QuadraticForm (ZMod 2) V)
    (hQ : Q.polarBilin.Nondegenerate) (hd : finrank (ZMod 2) V ≤ 6)
    (he : Even (finrank (ZMod 2) V))
    (hthree : 3 ∣ Nat.card {v : V // Q v = 1}) :
    (finrank (ZMod 2) V = 0 ∧ Nat.card {v : V // Q v = 1} = 0) ∨
    (finrank (ZMod 2) V = 2 ∧ Nat.card {v : V // Q v = 1} = 3) ∨
    (finrank (ZMod 2) V = 4 ∧ Nat.card {v : V // Q v = 1} = 6) ∨
    (finrank (ZMod 2) V = 6 ∧ Nat.card {v : V // Q v = 1} = 36) := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Fintype V := Fintype.ofFinite V
  have hr : binaryWalshRadical Q = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro x y hxy
    apply sub_eq_zero.mp
    apply hQ.1 (x-y)
    intro z
    have hz := LinearMap.congr_fun hxy z
    simpa [map_sub] using sub_eq_zero.mpr hz
  have hc : BinaryWalshCompatible Q 0 := by
    intro v hv
    have : v = 0 := by simpa only [hr, Submodule.mem_bot] using hv
    simp [this]
  have hw := binaryWalsh_sq_of_compatible Q 0 hc
  have hrad : Fintype.card (binaryWalshRadical Q) = 1 := by rw [hr]; simp
  rw [hrad, Nat.cast_one, mul_one, walsh_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card] at hw
  obtain ⟨k,hk⟩ := hthree
  obtain ⟨n,hn⟩ := he
  have hn3 : n ≤ 3 := by omega
  interval_cases n <;> norm_num only [hn, Nat.reduceAdd, Nat.reducePow, Nat.cast_ofNat] at hw
  · refine Or.inl ⟨by omega, ?_⟩
    have : Nat.card {v : V // Q v = 1} = 0 ∨ Nat.card {v : V // Q v = 1} = 1 := by
      have hh : ((Nat.card {v : V // Q v = 1} : ℤ)) *
          ((Nat.card {v : V // Q v = 1} : ℤ) - 1) = 0 := by nlinarith [hw]
      rcases mul_eq_zero.mp hh with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast (sub_eq_zero.mp h)
    omega
  · refine Or.inr (Or.inl ⟨by omega, ?_⟩)
    have hh : ((Nat.card {v : V // Q v = 1} : ℤ) - 1) *
        ((Nat.card {v : V // Q v = 1} : ℤ) - 3) = 0 := by nlinarith [hw]
    rcases mul_eq_zero.mp hh with h | h <;> have := sub_eq_zero.mp h <;> omega
  · refine Or.inr (Or.inr (Or.inl ⟨by omega, ?_⟩))
    have hh : ((Nat.card {v : V // Q v = 1} : ℤ) - 6) *
        ((Nat.card {v : V // Q v = 1} : ℤ) - 10) = 0 := by nlinarith [hw]
    rcases mul_eq_zero.mp hh with h | h <;> have := sub_eq_zero.mp h <;> omega
  · refine Or.inr (Or.inr (Or.inr ⟨by omega, ?_⟩))
    have hh : ((Nat.card {v : V // Q v = 1} : ℤ) - 28) *
        ((Nat.card {v : V // Q v = 1} : ℤ) - 36) = 0 := by nlinarith [hw]
    rcases mul_eq_zero.mp hh with h | h <;> have := sub_eq_zero.mp h <;> omega
end QuadraticForm.BinarySmall
