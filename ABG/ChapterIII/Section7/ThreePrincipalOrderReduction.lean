module
public import ABG.ChapterIII.Section7.ThreePrincipalPairing

/-!
# The integer order formula from the local involution-pair evaluation

If |C_G(x)| = 48ab and the local pairing of 1 − χ₁ + χ⁽²⁾ is 2b/a,
then |G|(f₁ − 3)² = 4608ab³f₁(f₁ − 1). The root transfer gives the global
pairing. Its character expansion supplies the rational degree expression;
clearing the nonzero denominators proves the integer formula.

This is a conditional reduction. Local group geometry must supply the two
counts, and involution fusion must also be established by the caller.

Source: Alperin–Brauer–Gorenstein, III.2 Proposition 6, equation (4),
and III.7 equation (8), article pp.68 and 103–104.
-/

namespace ABG.ThreePrincipalData
open Theory.Character
noncomputable section
attribute [local instance] Fintype.ofFinite

private theorem order_identity_arithmetic (g a b d : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hd : 1 < d)
    (h : (g : ℂ) / (48 * a * b)^2 *
      (1 - 9 / (d : ℂ) + 4 / ((d : ℂ) - 1)) = 2 * (b : ℂ) / a) :
    (g : ℤ) * ((d : ℤ) - 3)^2 =
      4608 * (a * b^3 : ℕ) * (d : ℤ) * ((d : ℤ) - 1) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hd1 : (d : ℂ) - 1 ≠ 0 := by
    have hh : (d : ℂ) ≠ 1 := by exact_mod_cast (by omega : d ≠ 1)
    exact sub_ne_zero.mpr hh
  have he : (g : ℂ) * ((d : ℂ) - 3)^2 =
      4608 * ((a * b^3 : ℕ) : ℂ) * (d : ℂ) * ((d : ℂ) - 1) := by
    push_cast
    field_simp at h
    linear_combination h
  exact_mod_cast he

/-- The characteristic-three order formula, conditional only on involution
fusion and the two local counts. The supplied characters remain unchanged. -/
public theorem order_identity_of_local_pairing
    {G : Type*} [Group G] [Finite G] {x : G} (c : ThreePrincipalData G x)
    (hx : orderOf x = 2) (hfuse : ∀ u : G, orderOf u = 2 → IsConj u x)
    (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcard : Nat.card (Subgroup.centralizer ({x} : Set G)) = 48 * a * b)
    (hlocal : scalarProduct (Subgroup.centralizer ({x} : Set G)) c.localOrderFunction
      (fun u => (involutionPairCount u : ℂ)) = 2 * (b : ℂ) / a) :
    (Nat.card G : ℤ) * ((c.degree 0 : ℤ) - 3)^2 =
      4608 * (a * b^3 : ℕ) * (c.degree 0 : ℤ) * ((c.degree 0 : ℤ) - 1) := by
  have hp := c.orderFunction_pairing hx hfuse
  rw [c.orderFunction_pairing_eq_local hx hfuse, hlocal, hcard] at hp
  have he : (Nat.card G : ℂ) / (48 * (a : ℂ) * b)^2 *
      (1 - 9 / (c.degree 0 : ℂ) + 4 / ((c.degree 0 : ℂ) - 1)) = 2 * (b : ℂ) / a := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hp.symm
  have hd : 1 < c.degree 0 := by
    rcases c.degree_alternatives with h | h <;> omega
  exact order_identity_arithmetic (Nat.card G) a b (c.degree 0) ha hb hd he

end
end ABG.ThreePrincipalData
