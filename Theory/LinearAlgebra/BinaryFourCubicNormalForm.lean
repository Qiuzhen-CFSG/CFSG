module

public import Theory.LinearAlgebra.BinaryFourCubicCentralizer
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel

/-!
# Normal form of a binary cubic operator in dimension four

A nonidentity operator `t` with `t ^ 3 = 1` on a four-dimensional binary
vector space, if it has a nonzero fixed vector, admits a basis in which its
matrix is the direct sum of `I₂` and `!![0,1; 1,1]`.

Choose a moved vector `w`. Then `u = w + t w` and `t u` span an invariant
cubic plane, disjoint from every fixed line. Extend a fixed vector together
with this plane to a basis using a vector `x`. The remaining coordinate is
fixed by `t`, since the only nonzero binary scalar is one. Thus
`x + t x + t² x` is a second independent fixed vector, giving the required
basis without classifying all four-dimensional matrices.

This supplies the linear-algebra normal form for the three-cycle fixed-point
argument used toward Aschbacher--Smith, *The Classification of Quasithin
Groups*, Lemma I.1.6(8), printed p.408/PDF p.419. The source lemma concerns
cohomology vanishing; the theorem here is its independently proved
linear-algebra input.
-/

open Module

namespace BinaryFourCubic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem binary_add_self (x : V) : x + x = 0 := by
  calc
    x + x = ((1 : ZMod 2) + 1) • x := by rw [add_smul, one_smul]
    _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul]

private theorem cubic_apply (t : Module.End (ZMod 2) V) (ht : t ^ 3 = 1) (x : V) :
    t (t (t x)) = x := by
  simpa [pow_succ, Module.End.mul_apply] using congrArg (fun f : Module.End (ZMod 2) V => f x) ht

/-- The image of `1 + t` contains an irreducible cubic plane. -/
private theorem exists_cubic_pair (t : Module.End (ZMod 2) V)
    (ht : t ^ 3 = 1) (htne : t ≠ 1) :
    ∃ u : V, u ≠ 0 ∧ t (t u) = u + t u ∧
      LinearIndependent (ZMod 2) ![u, t u] := by
  have hmove : ∃ w, t w ≠ w := by
    by_contra! h
    exact htne (LinearMap.ext h)
  obtain ⟨w, hw⟩ := hmove
  let u := w + t w
  have hu : u ≠ 0 := by
    intro h
    apply hw
    have := congrArg (fun z => w + z) h
    simpa [u, ← add_assoc, binary_add_self] using this
  have htu : t (t u) = u + t u := by
    dsimp [u]
    rw [map_add, map_add, cubic_apply t ht]
    calc
      t (t w) + w = (w + t (t w)) + (t w + t w) := by rw [binary_add_self, add_zero, add_comm]
      _ = (w + t w) + (t w + t (t w)) := by abel
  have htu0 : t u ≠ 0 := by
    intro h
    have := cubic_apply t ht u
    rw [h, map_zero, map_zero] at this
    exact hu this.symm
  have hne : u ≠ t u := by
    intro h
    have h2 : t (t u) = u := by rw [← h, ← h]
    rw [h2, ← h, binary_add_self] at htu
    exact hu htu
  refine ⟨u, hu, htu, (LinearIndependent.pair_iff' hu).mpr ?_⟩
  intro a
  fin_cases a
  · change (0 : ZMod 2) • u ≠ t u
    simpa using Ne.symm htu0
  · change (1 : ZMod 2) • u ≠ t u
    simpa using hne

/-- The trace operator separates a fixed line from the cubic plane. -/
private theorem independent_fixed_cubic (t : Module.End (ZMod 2) V)
    (v u : V) (hv : v ≠ 0) (htv : t v = v)
    (htu : t (t u) = u + t u)
    (hu : LinearIndependent (ZMod 2) ![u, t u]) :
    LinearIndependent (ZMod 2) ![v, u, t u] := by
  let p : Module.End (ZMod 2) V := 1 + t + t ^ 2
  have hpv : p v = v := by
    simp [p, pow_two, Module.End.mul_apply, htv, binary_add_self]
  have hpu : p u = 0 := by
    simp [p, pow_two, Module.End.mul_apply, htu, binary_add_self]
  have hptu : p (t u) = 0 := by
    simp only [p, LinearMap.add_apply, Module.End.one_apply, pow_two,
      Module.End.mul_apply, htu, map_add]
    calc
      t u + (u + t u) + (t u + (u + t u)) =
          (t u + (u + t u)) + (t u + (u + t u)) := rfl
      _ = 0 := binary_add_self _
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hc' : c 0 • v + (c 1 • u + c 2 • t u) = 0 := by
    simpa [Fin.sum_univ_succ] using hc
  have hc0 : c 0 = 0 := by
    have hp := congrArg p hc'
    simp only [map_add, map_smul, hpv, hpu, hptu, smul_zero, add_zero, map_zero] at hp
    exact (smul_eq_zero.mp hp).resolve_right hv
  have hc12 : ∀ j : Fin 2, ![c 1, c 2] j = 0 := by
    apply Fintype.linearIndependent_iff.mp hu
    simpa [Fin.sum_univ_succ, hc0] using hc'
  fin_cases i
  · exact hc0
  · exact hc12 0
  · exact hc12 1

/-- An invariant hyperplane with a fixed line yields a second fixed vector. -/
private theorem exists_fixed_companion [FiniteDimensional (ZMod 2) V]
    (hdim : Module.finrank (ZMod 2) V = 4)
    (t : Module.End (ZMod 2) V) (ht : t ^ 3 = 1)
    (v u : V) (htv : t v = v) (htu : t (t u) = u + t u)
    (hvu : LinearIndependent (ZMod 2) ![v, u, t u]) :
    ∃ z : V, t z = z ∧ LinearIndependent (ZMod 2) ![v, z, u, t u] := by
  classical
  obtain ⟨x, hx⟩ := exists_linearIndependent_cons_of_lt_finrank hvu
    (show 3 < Module.finrank (ZMod 2) V by omega)
  let b : Basis (Fin 4) (ZMod 2) V :=
    basisOfLinearIndependentOfCardEqFinrank hx (by simpa using hdim.symm)
  have hb : ∀ i, b i = ![x, v, u, t u] i := by
    intro i
    simp [b]
  have hb0 : b 0 = x := hb 0
  have hb1 : b 1 = v := hb 1
  have hb2 : b 2 = u := hb 2
  have hb3 : b 3 = t u := hb 3
  let q : V →ₗ[ZMod 2] ZMod 2 := b.coord 0
  have hqx : q x = 1 := by simp [q, ← hb0]
  have hqv : q v = 0 := by simp [q, ← hb1]
  have hqu : q u = 0 := by simp [q, ← hb2]
  have hqtu : q (t u) = 0 := by rw [← hb3]; simp [q]
  have hexpand (y : V) : y = q y • x +
      (b.repr y 1 • v + (b.repr y 2 • u + b.repr y 3 • t u)) := by
    simpa only [Fin.sum_univ_four, add_assoc, hb0, hb1, hb2, hb3,
      q, Basis.coord_apply] using (b.sum_repr y).symm
  have hqt (y : V) : q (t y) = q (t x) * q y := by
    conv_lhs => rw [hexpand y]
    simp [map_add, map_smul, htv, htu, hqv, hqu, hqtu, smul_eq_mul, mul_comm]
  have hqtx : q (t x) = 1 := by
    have hne : q (t x) ≠ 0 := by
      intro h0
      have h := hqt (t (t x))
      rw [cubic_apply t ht, hqx, h0, zero_mul] at h
      exact one_ne_zero h
    generalize q (t x) = a at hne ⊢
    fin_cases a
    · exact (hne rfl).elim
    · rfl
  have hqt' (y : V) : q (t y) = q y := by rw [hqt, hqtx, one_mul]
  let z := x + t x + t (t x)
  have htz : t z = z := by
    simp only [z, map_add, cubic_apply t ht]
    abel
  have hqz : q z = 1 := by
    simp only [z, map_add, hqt', hqx]
    decide
  refine ⟨z, htz, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hc' : c 0 • v + (c 1 • z + (c 2 • u + c 3 • t u)) = 0 := by
    simpa [Fin.sum_univ_succ] using hc
  have hc1 : c 1 = 0 := by
    have h := congrArg q hc'
    simpa only [map_add, map_smul, hqv, hqz, hqu, hqtu,
      smul_zero, smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, map_zero] using h
  have hc023 : ∀ j : Fin 3, ![c 0, c 2, c 3] j = 0 := by
    apply Fintype.linearIndependent_iff.mp hvu
    simpa [Fin.sum_univ_succ, hc1] using hc'
  fin_cases i
  · exact hc023 0
  · exact hc1
  · exact hc023 1
  · exact hc023 2

/-- A nonidentity cubic operator on a binary four-space with a nonzero fixed
vector has a basis consisting of a fixed plane and an irreducible cubic plane. -/
public theorem exists_basis_fixedPlaneMatrix [FiniteDimensional (ZMod 2) V]
    (hdim : Module.finrank (ZMod 2) V = 4)
    (t : Module.End (ZMod 2) V) (ht : t ^ 3 = 1) (htne : t ≠ 1)
    (hfixed : ∃ v : V, v ≠ 0 ∧ t v = v) :
    ∃ basis : Module.Basis (Fin 4) (ZMod 2) V,
      LinearMap.toMatrix basis basis t = fixedPlaneMatrix := by
  classical
  obtain ⟨v, hv, htv⟩ := hfixed
  obtain ⟨u, _, htu, hu⟩ := exists_cubic_pair t ht htne
  have hvu := independent_fixed_cubic t v u hv htv htu hu
  obtain ⟨z, htz, hbasis⟩ := exists_fixed_companion hdim t ht v u htv htu hvu
  let b : Basis (Fin 4) (ZMod 2) V :=
    basisOfLinearIndependentOfCardEqFinrank hbasis (by simpa using hdim.symm)
  have hb : ∀ i, b i = ![v, z, u, t u] i := by
    intro i
    simp [b]
  have ht0 : t (b 0) = b 0 := by simpa [hb] using htv
  have ht1 : t (b 1) = b 1 := by simpa [hb] using htz
  have ht2 : t (b 2) = b 3 := by simp only [hb]; rfl
  have ht3 : t (b 3) = b 2 + b 3 := by simpa [hb] using htu
  refine ⟨b, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, ht0, ht1, ht2, ht3, fixedPlaneMatrix]

end BinaryFourCubic
