/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.IsometryQuotients.Quotient

/-!
# Full isometry quotients in split and odd rank at least two

The first two standard hyperbolic pairs instantiate elementary shell
transitivity. The full isometry quotient consequently has two-power order,
and its prime-to-characteristic residual is the actual elementary subgroup.
In particular the split four-space over F₃ is included without perfectness.

The frame constructions adapt `Atlas/LinearGroups/Orthogonal/WittTwoStandard.lean`;
the index and residual applications use CFSG's exact carriers and maps.
Source: GLS3 §2.7; Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup
namespace ClassicalOrthogonal
open ClassicalOrthogonal.Quadratic
variable {F : Type*} [Field F]

def wittTwoFrameD (n : ℕ) : WittTwoFrame (formD (n+2) F) where
  e₁ := e 0
  f₁ := f 0
  e₂ := e 1
  f₂ := f 1
  qe₁ := formD_e _
  qf₁ := formD_f _
  qe₂ := formD_e _
  qf₂ := formD_f _
  pair₁ := polarD_ef _
  pair₂ := polarD_ef _
  ee := by rw [polarD_e]; simp [e]
  ef := by rw [polarD_f]; simp [e]
  fe := by rw [polarD_e]; simp [f]
  ff := by rw [polarD_f]; simp [f]

def wittTwoFrameB (n : ℕ) : WittTwoFrame (formB (n+2) F) where
  e₁ := ((wittTwoFrameD n).e₁, 0)
  f₁ := ((wittTwoFrameD n).f₁, 0)
  e₂ := ((wittTwoFrameD n).e₂, 0)
  f₂ := ((wittTwoFrameD n).f₂, 0)
  qe₁ := by simp only [formB_apply, (wittTwoFrameD n).qe₁, zero_pow (by decide : 2 ≠ 0), add_zero]
  qf₁ := by simp only [formB_apply, (wittTwoFrameD n).qf₁, zero_pow (by decide : 2 ≠ 0), add_zero]
  qe₂ := by simp only [formB_apply, (wittTwoFrameD n).qe₂, zero_pow (by decide : 2 ≠ 0), add_zero]
  qf₂ := by simp only [formB_apply, (wittTwoFrameD n).qf₂, zero_pow (by decide : 2 ≠ 0), add_zero]
  pair₁ := by simp only [polarB_apply, (wittTwoFrameD n).pair₁, mul_zero, add_zero]
  pair₂ := by simp only [polarB_apply, (wittTwoFrameD n).pair₂, mul_zero, add_zero]
  ee := by simp only [polarB_apply, (wittTwoFrameD n).ee, mul_zero, add_zero]
  ef := by simp only [polarB_apply, (wittTwoFrameD n).ef, mul_zero, add_zero]
  fe := by simp only [polarB_apply, (wittTwoFrameD n).fe, mul_zero, add_zero]
  ff := by simp only [polarB_apply, (wittTwoFrameD n).ff, mul_zero, add_zero]


/-- The odd polar form is nondegenerate when two is nonzero. -/
theorem polarB_nondegenerate {n : ℕ} (h2 : (2 : F) ≠ 0) :
    (formB n F).polarBilin.Nondegenerate := by
  constructor
  · exact polarB_separating_of_two_ne_zero h2
  · intro x hx
    apply polarB_separating_of_two_ne_zero h2 x
    intro y
    rw [Quadratic.polar_swap]
    exact hx y

namespace Fundamental.SplitOddBlocks.IsometryQuotients

/-- Odd characteristic makes the scalar two nonzero. -/
theorem two_ne_zero_of_odd_prime (p : ℕ) [Fact p.Prime] [CharP F p] (hp : p ≠ 2) :
    (2 : F) ≠ 0 := by
  intro h
  have hd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp h
  exact hp (((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left (Fact.out : p.Prime).ne_one)

variable [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p] (hp : p ≠ 2)

include hp in
/-- The elementary index in the full odd isometry group, in rank at least two. -/
theorem elementary_index_coprime_formB_stable (n : ℕ) :
    Nat.Coprime p (elementarySubgroup (formB (n + 2) F)).index :=
  elementary_index_coprime _ (wittTwoFrameB n)
    (polarB_nondegenerate (two_ne_zero_of_odd_prime (F := F) p hp))
    (two_ne_zero_of_odd_prime (F := F) p hp) p ((Fact.out : p.Prime).odd_of_ne_two hp)

include hp in
/-- Every requested split rank, including rank two over the ternary field. -/
theorem elementary_index_coprime_formD (k : ℕ) (hk : 2 ≤ k) :
    Nat.Coprime p (elementarySubgroup (formD k F)).index := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm 2 n]
  exact elementary_index_coprime (formD (n + 2) F)
    (wittTwoFrameD n) polarD_nondegenerate (two_ne_zero_of_odd_prime (F := F) p hp)
    p ((Fact.out : p.Prime).odd_of_ne_two hp)

include hp in
/-- The literal full-isometry residual in odd rank at least two. -/
theorem primeToResidual_formB_stable (n : ℕ) :
    Subgroup.primeToResidual p (quadraticIsometrySubgroup (formB (n + 2) F)) =
      elementarySubgroup (formB (n + 2) F) :=
  primeToResidual_eq_elementary_of_index _ p (elementary_index_coprime_formB_stable p hp n)

include hp in
/-- The literal full-isometry residual in every requested split rank. -/
theorem primeToResidual_formD (k : ℕ) (hk : 2 ≤ k) :
    Subgroup.primeToResidual p (quadraticIsometrySubgroup (formD k F)) =
      elementarySubgroup (formD k F) :=
  primeToResidual_eq_elementary_of_index _ p (elementary_index_coprime_formD p hp k hk)

end Fundamental.SplitOddBlocks.IsometryQuotients
end ClassicalOrthogonal
