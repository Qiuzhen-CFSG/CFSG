module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ScalarShape.Operators
public import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# Fixed Cartan coordinates of diagonal central E6 words

A signed simple operator has a zero row on every other Cartan coordinate.
The quadratic-curve identity therefore shows that the extra Cartan coordinate
functionals are fixed by each generator and by every six-node word. This
uses evaluated-word membership, with no centrality assumption.

For a diagonal central word, its commutation with a positive simple operator
equates the entries on adjacent Cartan nodes: the root-to-Cartan coefficients
are two on the diagonal and one along a diagram edge. The fixed seventh
Cartan entry and the connected E6 diagram force all six subsystem Cartan
entries to be one. E8's eighth Cartan entry is fixed separately. Only two
is cancelled, so characteristic three is included.

This normalizes the Cartan entries once diagonality is proved; it does not
assert that an arbitrary central word is diagonal or determine its remaining
root entries. Sources: GLS3 §§1.12.5–6 and 2.6.2; Aschbacher–Smith A.2.17,
printed p.39.
-/

@[expose] public section

open RootPairing.SimpleGeckGroup RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup.StandardRootSystem
noncomputable section

namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.ScalarShape

attribute [local instance] Classical.decEq

private theorem odd_two_ne_zero {F : Type*} [Field F] (hodd : Odd (ringChar F)) : (2 : F) ≠ 0 := by
  intro h
  rcases (Nat.dvd_prime Nat.prime_two).mp (ringChar.dvd h) with h | h
  · exact CharP.ringChar_ne_one (R := F) h
  · exact hodd.not_two_dvd_nat (by rw [h])

section Generic
variable {ι R M N F : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι] [Field F]

/-- A simple operator has zero row on each other Cartan coordinate. -/
theorem simpleCoefficient_cartan_row_zero (s : Bool) (i k : b.support) (hki : k ≠ i)
    (c : b.support ⊕ ι) :
    (simpleFamily (b := b)).coefficient (S := F) (s, i) 1 (Sum.inl k) c = 0 := by
  cases s <;> cases c <;>
    simp [IntegralCubicFamily.coefficient, simpleFamily, eDividedPower_one,
      fDividedPower_one, eMatrix, fMatrix, hki]
end Generic

section Matrix
variable {n κ F : Type*} [Fintype n] [DecidableEq n] [Field F]

private theorem mul_apply_of_fixed_row (A B : Matrix n n F) (r : n)
    (hA : ∀ c, A r c = (1 : Matrix n n F) r c) (c : n) :
    (A * B) r c = B r c := by
  simp [Matrix.mul_apply, hA, Matrix.one_apply]

private theorem inv_apply_of_fixed_row (g : (Matrix n n F)ˣ) (r : n)
    (hg : ∀ c, g.val r c = (1 : Matrix n n F) r c) (c : n) :
    (g⁻¹).val r c = (1 : Matrix n n F) r c := by
  calc
    (g⁻¹).val r c = (g.val * (g⁻¹).val) r c :=
      (mul_apply_of_fixed_row g.val (g⁻¹).val r hg c).symm
    _ = (1 : Matrix n n F) r c := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

/-- A coordinate functional fixed by every generator is fixed by every evaluated word. -/
theorem eval_fixed_row (v : SixNodeWord F →* (Matrix n n F)ˣ) (r : n)
    (hv : ∀ s i t c, (v (FreeGroup.of (s, i, t))).val r c = (1 : Matrix n n F) r c)
    (w : SixNodeWord F) (c : n) : (v w).val r c = (1 : Matrix n n F) r c := by
  have h : ∀ c, (v w).val r c = (1 : Matrix n n F) r c := by
    induction w using FreeGroup.induction_on with
    | C1 => simp
    | of x => obtain ⟨s, i, t⟩ := x; exact hv s i t
    | inv_of x hx =>
      intro c
      simpa only [map_inv] using inv_apply_of_fixed_row (v (FreeGroup.of x)) r hx c
    | mul x y hx hy =>
      intro c
      simpa only [map_mul, Units.val_mul] using
        (mul_apply_of_fixed_row (v x).val (v y).val r hx c).trans (hy c)
  exact h c

/-- A zero row of the linear operator gives a fixed row of its quadratic curve. -/
theorem curve_fixed_row (D : IntegralCubicFamily κ n) (i : κ)
    (h3 : D.dividedPower i 3 = 0) (r : n)
    (h2 : (2 : F) ≠ 0) (hrow : ∀ c, D.coefficient (S := F) i 1 r c = 0)
    (t : F) (c : n) : D.curve i t r c = (1 : Matrix n n F) r c := by
  have hc2 : D.coefficient (S := F) i 2 r c = 0 := by
    have h := congrArg (fun A : Matrix n n F => A r c) (D.coefficient_mul (S := F) i 1 1)
    have he : (2 : F) * D.coefficient (S := F) i 2 r c = 0 := by
      simpa [Matrix.mul_apply, hrow] using h.symm
    exact (mul_eq_zero.mp he).resolve_left h2
  have hc3 : D.coefficient (S := F) i 3 = 0 := by
    simp [IntegralCubicFamily.coefficient, h3]
  simp [IntegralCubicFamily.curve, hrow, hc2, hc3]

/-- A nonzero operator entry equates two entries of a commuting diagonal matrix. -/
theorem diagonal_entries_eq_of_commute {g A : Matrix n n F} (hg : g.IsDiag)
    (hc : Commute g A) (r c : n) (hA : A r c ≠ 0) : g r r = g c c := by
  have h := congrArg (fun B : Matrix n n F => B r c) hc.eq
  rw [← hg.diagonal_diag] at h
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diag_apply] at h
  exact mul_right_cancel₀ hA (h.trans (mul_comm _ _))
end Matrix

local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _

/-- Every E7 six-node word fixes the extra Cartan coordinate functional. -/
theorem e7Six_extraCartan_row (F : Type*) [Field F] (hodd : Odd (ringChar F))
    (w : SixNodeWord F) (k : Fin 7) (hk : 6 ≤ k.val)
    (c : typeE7RootPairing_base.support ⊕ typeE7Roots) :
    (e7Six F w).val.val (Sum.inl (typeE7RootPairing_baseEquiv k)) c =
      (1 : Matrix (typeE7RootPairing_base.support ⊕ typeE7Roots)
        (typeE7RootPairing_base.support ⊕ typeE7Roots) F)
      (Sum.inl (typeE7RootPairing_baseEquiv k)) c := by
  apply eval_fixed_row ((ExceptionalSplit.rootGenerated _ _ F).subtype.comp (e7Six F))
  intro s i t c
  change (e7Six F (FreeGroup.of (s, i, t))).val.val _ c = _
  simp only [e7Six_of, e7Simple, signedSimple_val, IntegralCubicFamily.unit_val]
  apply curve_fixed_row _ _ (e7_simple_third_zero s _) _ (odd_two_ne_zero hodd)
  intro c
  apply simpleCoefficient_cartan_row_zero
  intro he
  have h := congrArg Fin.val (typeE7RootPairing_baseEquiv.injective he)
  simp only [Fin.val_castLE] at h
  omega

/-- Every E8 six-node word fixes both extra Cartan coordinate functionals. -/
theorem e8Six_extraCartan_row (F : Type*) [Field F] (hodd : Odd (ringChar F))
    (w : SixNodeWord F) (k : Fin 8) (hk : 6 ≤ k.val)
    (c : typeE8RootPairing_base.support ⊕ typeE8Roots) :
    (e8Six F w).val.val (Sum.inl (typeE8RootPairing_baseEquiv k)) c =
      (1 : Matrix (typeE8RootPairing_base.support ⊕ typeE8Roots)
        (typeE8RootPairing_base.support ⊕ typeE8Roots) F)
      (Sum.inl (typeE8RootPairing_baseEquiv k)) c := by
  apply eval_fixed_row ((ExceptionalSplit.rootGenerated _ _ F).subtype.comp (e8Six F))
  intro s i t c
  change (e8Six F (FreeGroup.of (s, i, t))).val.val _ c = _
  simp only [e8Six_of, e8Simple, signedSimple_val, IntegralCubicFamily.unit_val]
  apply curve_fixed_row _ _ (e8_simple_third_zero s _) _ (odd_two_ne_zero hodd)
  intro c
  apply simpleCoefficient_cartan_row_zero
  intro he
  have h := congrArg Fin.val (typeE8RootPairing_baseEquiv.injective he)
  simp only [Fin.val_castLE] at h
  omega

section GenericCartan
variable {ι R M N F : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι] [Field F]

private theorem diagonal_cartan_eq_of_commute (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) F)
    (hA : A.IsDiag) (i k : b.support)
    (hc : Commute A ((simpleFamily (b := b)).coefficient (true, i) 1))
    (h2 : (2 : F) ≠ 0) (hik : b.cartanMatrix i k = -1) :
    A (Sum.inl i) (Sum.inl i) = A (Sum.inl k) (Sum.inl k) := by
  have hi : (simpleFamily (b := b)).coefficient (S := F) (true, i) 1
      (Sum.inr i) (Sum.inl i) = 2 := by
    simp [IntegralCubicFamily.coefficient, simpleFamily, eMatrix]
  have hk : (simpleFamily (b := b)).coefficient (S := F) (true, i) 1
      (Sum.inr i) (Sum.inl k) = 1 := by
    simp [IntegralCubicFamily.coefficient, simpleFamily, eMatrix, hik]
  exact (diagonal_entries_eq_of_commute hA hc _ _ (hi ▸ h2)).symm.trans
    (diagonal_entries_eq_of_commute hA hc _ _ (hk ▸ one_ne_zero))
end GenericCartan

/-- A diagonal central E7 six-node word fixes every Cartan coordinate. -/
theorem e7Six_diagonal_cartan_eq_one (F : Type*) [Field F] (hodd : Odd (ringChar F))
    (w : SixNodeWord F) (hc : ∀ z, Commute (e7Six F w) (e7Six F z))
    (hd : (e7Six F w).val.val.IsDiag) (k : typeE7RootPairing_base.support) :
    (e7Six F w).val.val (Sum.inl k) (Sum.inl k) = 1 := by
  let d (k : Fin 7) := (e7Six F w).val.val
    (Sum.inl (typeE7RootPairing_baseEquiv k)) (Sum.inl (typeE7RootPairing_baseEquiv k))
  have hs (i : Fin 6) (j : Fin 7)
      (hij : typeE7CartanMatrix (i.castLE (by decide)) j = -1) :
      d (i.castLE (by decide)) = d j := by
    apply diagonal_cartan_eq_of_commute _ hd _ _
      ((e7Six_central_iff_operators F hodd w).mp hc true i) (odd_two_ne_zero hodd)
    exact (typeE7RootPairing_base_cartan_apply _ _).trans hij
  have h6 : d 6 = 1 := by
    simpa [d] using e7Six_extraCartan_row F hodd w 6 (by decide)
      (Sum.inl (typeE7RootPairing_baseEquiv 6))
  have h5 : d 5 = 1 := (hs 5 6 (by decide)).trans h6
  have h4 : d 4 = 1 := (hs 4 5 (by decide)).trans h5
  have h2 : d 2 = 1 := (hs 2 4 (by decide)).trans h4
  have h3 : d 3 = 1 := (hs 3 2 (by decide)).trans h2
  have h1 : d 1 = 1 := (hs 1 2 (by decide)).trans h2
  have h0 : d 0 = 1 := (hs 0 1 (by decide)).trans h1
  obtain ⟨k, rfl⟩ := typeE7RootPairing_baseEquiv.surjective k
  change d k = 1
  fin_cases k <;> assumption

/-- A diagonal central E8 six-node word fixes every Cartan coordinate. -/
theorem e8Six_diagonal_cartan_eq_one (F : Type*) [Field F] (hodd : Odd (ringChar F))
    (w : SixNodeWord F) (hc : ∀ z, Commute (e8Six F w) (e8Six F z))
    (hd : (e8Six F w).val.val.IsDiag) (k : typeE8RootPairing_base.support) :
    (e8Six F w).val.val (Sum.inl k) (Sum.inl k) = 1 := by
  let d (k : Fin 8) := (e8Six F w).val.val
    (Sum.inl (typeE8RootPairing_baseEquiv k)) (Sum.inl (typeE8RootPairing_baseEquiv k))
  have hs (i : Fin 6) (j : Fin 8)
      (hij : typeE8CartanMatrix (i.castLE (by decide)) j = -1) :
      d (i.castLE (by decide)) = d j := by
    apply diagonal_cartan_eq_of_commute _ hd _ _
      ((e8Six_central_iff_operators F hodd w).mp hc true i) (odd_two_ne_zero hodd)
    exact (typeE8RootPairing_base_cartan_apply _ _).trans hij
  have h6 : d 6 = 1 := by
    simpa [d] using e8Six_extraCartan_row F hodd w 6 (by decide)
      (Sum.inl (typeE8RootPairing_baseEquiv 6))
  have h7 : d 7 = 1 := by
    simpa [d] using e8Six_extraCartan_row F hodd w 7 (by decide)
      (Sum.inl (typeE8RootPairing_baseEquiv 7))
  have h5 : d 5 = 1 := (hs 5 6 (by decide)).trans h6
  have h4 : d 4 = 1 := (hs 4 5 (by decide)).trans h5
  have h2 : d 2 = 1 := (hs 2 4 (by decide)).trans h4
  have h3 : d 3 = 1 := (hs 3 2 (by decide)).trans h2
  have h1 : d 1 = 1 := (hs 1 2 (by decide)).trans h2
  have h0 : d 0 = 1 := (hs 0 1 (by decide)).trans h1
  obtain ⟨k, rfl⟩ := typeE8RootPairing_baseEquiv.surjective k
  change d k = 1
  fin_cases k <;> assumption

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.ScalarShape
