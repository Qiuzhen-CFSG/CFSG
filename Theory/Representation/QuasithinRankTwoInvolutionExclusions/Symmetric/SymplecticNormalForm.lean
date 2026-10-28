module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Symmetric.SymplecticCoordinates
public import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FinCases

/-!
# The normal form of binary symplectic involutions of type a₂

For a form-preserving involution, write `N = t - 1`. The form
`C(x,y) = B(x,N y)` is symmetric and the moved space is totally isotropic.
The type-a₂ condition makes `C` alternating. Nondegeneracy of `B` and the
nonzero moved space supply `u,v` with `C(u,v) = 1`. Then `N u,N v` are
independent and, by displacement rank two, span the moved space. Pairing
with `u` and `v` recovers the coefficients of every `N x`, giving the
specified isotropic-pair formula.

The representation specialization uses the literal action `ρ v` and the
moved space `LinearMap.range (ρ v - 1)` from `Basic.movedSpace`. It discharges
the coordinate premise for the separate symplectic product calculation.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Definition E.2.6, printed p.218 (PDF p.229), and the type-a₂ product argument
in the proof of 6.2.19, printed p.691 (PDF p.708).
-/

namespace Representation.RankTwo.Symmetric

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private lemma binary_one_of_ne_zero (c : ZMod 2) (hc : c ≠ 0) : c = 1 := by
  fin_cases c
  · exact (hc rfl).elim
  · rfl

/-- The intrinsic binary symplectic type-a₂ conditions imply the isotropic-pair
normal form. No coordinates or product-order conclusion are assumed. -/
public theorem hasA2NormalForm_of_intrinsic [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (t : Module.End (ZMod 2) V)
    (hAlt : B.IsAlt) (hND : B.Nondegenerate)
    (ht : t * t = 1) (hpres : ∀ x y, B (t x) (t y) = B x y)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (t - 1)) = 2)
    (hType : ∀ x, B x (t x) = 0) : HasA2NormalForm B t := by
  classical
  let N : Module.End (ZMod 2) V := t - 1
  have hsymm (x y : V) : B x y = B y x := by
    simpa only [CharTwo.neg_eq] using hAlt.neg_eq x y
  have htt (x : V) : t (t x) = x := LinearMap.congr_fun ht x
  have hadj (x y : V) : B (t x) y = B x (t y) := by
    simpa only [htt] using hpres x (t y)
  have hdiag (x : V) : B x (N x) = 0 := by
    change B x (t x - x) = 0
    rw [map_sub, hType, hAlt.self_eq_zero, sub_self]
  have hswap (x y : V) : B x (N y) = B y (N x) := by
    change B x (t y - y) = B y (t x - x)
    rw [map_sub, map_sub, ← hadj, hsymm (t x) y, hsymm x y]
  have hiso (x y : V) : B (N x) (N y) = 0 := by
    change B (t x - x) (t y - y) = 0
    rw [LinearMap.BilinForm.sub_left, map_sub, map_sub, hpres, hadj]
    simp only [CharTwo.sub_eq_add, add_assoc, CharTwo.add_cancel_left,
      CharTwo.add_self_eq_zero]
  have hN : N ≠ 0 := by
    intro hz
    have hh : Module.finrank (ZMod 2) (LinearMap.range N) = 0 := by simp [hz]
    rw [hr] at hh
    exact (by decide : (2 : ℕ) ≠ 0) hh
  obtain ⟨u, hu⟩ : ∃ u, N u ≠ 0 := by
    by_contra! h
    exact hN (LinearMap.ext h)
  obtain ⟨v, hv⟩ : ∃ v, B v (N u) ≠ 0 := by
    by_contra! h
    exact hu (hND.2 _ h)
  have hvu : B v (N u) = 1 := binary_one_of_ne_zero _ hv
  have huv : B u (N v) = 1 := (hswap u v).trans hvu
  have hind : LinearIndependent (ZMod 2) ![N u, N v] := by
    rw [linearIndependent_fin2]
    change N v ≠ 0 ∧ ∀ c : ZMod 2, c • N v ≠ N u
    constructor
    · intro hzero
      have hh := huv
      rw [hzero, map_zero] at hh
      exact zero_ne_one hh
    · intro c hc
      have hh := congrArg (B v) hc
      apply (zero_ne_one : (0 : ZMod 2) ≠ 1)
      simpa only [map_smul, hdiag, smul_zero, hvu] using hh
  have hspan : Submodule.span (ZMod 2) ({N u, N v} : Set V) = N.range := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      intro w hw
      rcases hw with rfl | rfl
      · exact ⟨u, rfl⟩
      · exact ⟨v, rfl⟩
    · rw [hr, ← Matrix.range_cons_cons_empty (N u) (N v) ![],
        finrank_span_eq_card hind, Fintype.card_fin]
  refine ⟨N u, N v, hiso u v, ?_⟩
  intro x
  have hx : N x ∈ Submodule.span (ZMod 2) ({N u, N v} : Set V) := by
    rw [hspan]
    exact ⟨x, rfl⟩
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hx
  have hc : c = B x (N v) := by
    have hh := congrArg (B v) hcd
    simpa only [map_add, map_smul, hvu, hdiag, smul_eq_mul,
      mul_one, mul_zero, add_zero, hswap v x] using hh
  have hd : d = B x (N u) := by
    have hh := congrArg (B u) hcd
    simpa only [map_add, map_smul, huv, hdiag, smul_eq_mul,
      mul_one, mul_zero, zero_add, hswap u x] using hh
  have hNx : N x = B x (N u) • N v + B x (N v) • N u := by
    rw [← hcd, hc, hd, add_comm]
  have htx : t x = N x + x := sub_add_cancel (t x) x |>.symm
  rw [htx, hNx]
  ac_rfl

/-- A rank-two type-a₂ element in a form-preserving binary representation has
the normal form used by the symplectic product calculation. The rank is taken
on the actual `movedSpace ρ v`, with no change of action or quotient. -/
public theorem hasA2NormalForm_of_representation {G : Type*} [Group G]
    [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (ρ : Representation (ZMod 2) G V) (v : G)
    (hAlt : B.IsAlt) (hND : B.Nondegenerate) (hv : v * v = 1)
    (hpres : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    (hr : Module.finrank (ZMod 2) (movedSpace ρ v) = 2)
    (hType : ∀ x, B x (ρ v x) = 0) : HasA2NormalForm B (ρ v) := by
  apply hasA2NormalForm_of_intrinsic B (ρ v) hAlt hND ?_ (hpres v) hr hType
  rw [← map_mul, hv, map_one]

end Representation.RankTwo.Symmetric
