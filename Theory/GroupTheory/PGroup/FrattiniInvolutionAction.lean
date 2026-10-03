module

public import Theory.Frattini.BinarySquares
public import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Tactic

/-!
# Involutions acting centrally on a Frattini base

Suppose a normal self-centralizing subgroup lies in the Frattini subgroup of
a finite two-group, and its elements of square one are central. An involution
whose conjugation action on the base is central cannot invert only elements
of square one unless it belongs to the base.

Conjugation differences lie in the base and are inverted by the involution.
They are therefore central involutions. Conjugating twice shows that every
square centralizes the involution. Squares generate the Frattini subgroup,
so self-centrality of the base finishes the argument.

This isolates a Frattini argument for the C₄-square extensions occurring in
MacWilliams, Trans. AMS 150 (1970), §4, pp.392–393; compare Janko–Thompson,
Math. Z. 113 (1970), 1.4(c), p.386.
-/

namespace IsPGroup

open Subgroup

/-- Central-action involutions cannot escape a self-centralizing Frattini base
if all the base elements they invert have square one. -/
public theorem involution_mem_of_le_frattini_of_central_action
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (D : Subgroup P) [D.Normal]
    (hDC : centralizer (D : Set P) ≤ D) (hDΦ : D ≤ frattini P)
    (hcentral : ∀ d ∈ D, d ^ 2 = 1 → d ∈ center P)
    (x : P) (hx : x ^ 2 = 1)
    (hcomm : ∀ g : P, Commute (MulAut.conjNormal (H := D) g)
      (MulAut.conjNormal (H := D) x))
    (hinv : ∀ d ∈ D, x * d * x⁻¹ = d⁻¹ → d ^ 2 = 1) : x ∈ D := by
  have hdiff (g : P) :
      g * x * g⁻¹ * x⁻¹ ∈ center P ∧ (g * x * g⁻¹ * x⁻¹) ^ 2 = 1 := by
    let d := g * x * g⁻¹ * x⁻¹
    have hker : (MulAut.conjNormal (H := D)) d = 1 := by
      dsimp [d]
      simp only [map_mul, map_inv]
      rw [(hcomm g).eq]
      group
    have hd : d ∈ D := by
      apply hDC
      intro a ha
      have hh := congrArg (fun t : MulAut D => (t ⟨a, ha⟩ : P)) hker
      change d * a * d⁻¹ = a at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hde : (d * x) ^ 2 = 1 := by
      change (g * x * g⁻¹ * x⁻¹ * x) ^ 2 = 1
      rw [inv_mul_cancel_right, ← MulAut.conj_apply, ← map_pow, hx, map_one]
    have hdi : x * d * x⁻¹ = d⁻¹ := by
      have hprod : d * (x * d * x⁻¹) = 1 := by
        calc
          d * (x * d * x⁻¹) = (d * x) ^ 2 * (x ^ 2)⁻¹ := by
            simp only [pow_two]; group
          _ = 1 := by rw [hde, hx]; simp
      exact eq_inv_of_mul_eq_one_right hprod
    have hd2 := hinv d hd hdi
    exact ⟨hcentral d hd hd2, hd2⟩
  have hsquare (g : P) : Commute (g ^ 2) x := by
    let d := g * x * g⁻¹ * x⁻¹
    have hdx : g * x * g⁻¹ = d * x := by simp [d]
    have hdg : g * d * g⁻¹ = d := by
      rw [mem_center_iff.mp (hdiff g).1 g, mul_inv_cancel_right]
    have hfix : g ^ 2 * x * (g ^ 2)⁻¹ = x := by
      calc
        g ^ 2 * x * (g ^ 2)⁻¹ = g * (g * x * g⁻¹) * g⁻¹ := by
          simp only [pow_two]; group
        _ = g * (d * x) * g⁻¹ := by rw [hdx]
        _ = (g * d * g⁻¹) * (g * x * g⁻¹) := by group
        _ = d * (d * x) := by rw [hdg, hdx]
        _ = x := by rw [← mul_assoc, ← pow_two, (hdiff g).2, one_mul]
    exact mul_inv_eq_iff_eq_mul.mp hfix
  have hΦ : frattini P ≤ centralizer ({x} : Set P) := by
    rw [hP.frattini_eq_closure_squares]
    apply (closure_le _).mpr
    rintro _ ⟨g, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (hsquare g).eq
  apply hDC
  intro d hd
  exact mem_centralizer_singleton_iff.mp (hΦ (hDΦ hd))

end IsPGroup
