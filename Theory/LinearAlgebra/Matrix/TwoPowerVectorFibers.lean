module

public import Theory.LinearAlgebra.Matrix.TwoPowerNormReduction
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Tactic.Ring

/-!
# Uniform fibers of two-power vector reduction

Coordinatewise reduction from `ZMod (2 ^ n)` to `ZMod (2 ^ (n - 2))` is
surjective, and each vector in the target has sixteen preimages.  The result
is stated for an arbitrary predicate on the reduced vectors, so it can be
applied directly to reduced matrix equations.

Source context: the elementary homocyclic norm calculation in the
MacWilliams--Sah bound quoted by Janko--Thompson, Math. Z. 113 (1970), 1.1,
printed p.385.
-/

public section

open Matrix
namespace TwoPowerNorm

/-- Pulling back any predicate along two-power vector reduction multiplies its
cardinality by the sixteen lifts of each vector. -/
public theorem lift_count (n : ℕ) (hn : 2 ≤ n)
    (P : (Fin 2 → ZMod (2 ^ (n - 2))) → Prop) :
    let r := ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le n 2)) (ZMod (2 ^ (n - 2)))
    Nat.card {v : Fin 2 → ZMod (2 ^ n) // P (r ∘ v)} =
      16 * Nat.card {u : Fin 2 → ZMod (2 ^ (n - 2)) // P u} := by
  let r := ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le n 2)) (ZMod (2 ^ (n - 2)))
  let f0 : ZMod (2 ^ n) →+ ZMod (2 ^ (n - 2)) :=
    (r : ZMod (2 ^ n) →+ ZMod (2 ^ (n - 2)))
  let f : (Fin 2 → ZMod (2 ^ n)) →+ (Fin 2 → ZMod (2 ^ (n - 2))) :=
    AddMonoidHom.piMap (fun _ => f0)
  have hf : Function.Surjective f := by
    intro u
    obtain ⟨v, hv⟩ :=
      Function.Surjective.piMap
        (fun _ => ZMod.castHom_surjective (pow_dvd_pow 2 (Nat.sub_le n 2))) u
    exact ⟨v, by ext i; simpa [f, f0, r] using congrFun hv i⟩
  have hf_apply (v : Fin 2 → ZMod (2 ^ n)) : f v = r ∘ v := by
    ext i
    rfl
  have hfiber (u : Fin 2 → ZMod (2 ^ (n - 2))) :
      Nat.card {v : Fin 2 → ZMod (2 ^ n) // f v = u} =
        Nat.card {v : Fin 2 → ZMod (2 ^ n) // f v = 0} := by
    let e := AddMonoidHom.fiberEquivOfSurjective hf u 0
    exact Nat.card_congr e
  have hdomratio : Nat.card (Fin 2 → ZMod (2 ^ n)) =
      16 * Nat.card (Fin 2 → ZMod (2 ^ (n - 2))) := by
    simp only [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Nat.card_zmod]
    rw [show 2 ^ n = 4 * 2 ^ (n - 2) by
      rw [show 4 = 2 ^ 2 from rfl, ← pow_add, Nat.add_sub_cancel' hn]]
    ring
  have hsum := Nat.card_congr
    (Equiv.sigmaFiberEquiv
      (f : (Fin 2 → ZMod (2 ^ n)) → (Fin 2 → ZMod (2 ^ (n - 2))))).symm
  rw [Nat.card_sigma] at hsum
  have hcommon : Nat.card {v : Fin 2 → ZMod (2 ^ n) // f v = 0} = 16 := by
    have hsum' : 16 * Nat.card (Fin 2 → ZMod (2 ^ (n - 2))) =
        Nat.card (Fin 2 → ZMod (2 ^ (n - 2))) *
          Nat.card {v : Fin 2 → ZMod (2 ^ n) // f v = 0} := by
      rw [← hdomratio, hsum]
      simp_rw [hfiber]
      simp [Finset.sum_const]
    have hcpos : 0 < Nat.card (Fin 2 → ZMod (2 ^ (n - 2))) := by
      exact Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_left hcpos (by simpa [mul_comm] using hsum')).symm
  let e :=
    (Equiv.sigmaFiberEquiv
      (f : (Fin 2 → ZMod (2 ^ n)) → (Fin 2 → ZMod (2 ^ (n - 2))))).symm
  have he : Nat.card {v : Fin 2 → ZMod (2 ^ n) // P (f v)} =
      Nat.card {p : (Σ u : Fin 2 → ZMod (2 ^ (n - 2)),
        {v : Fin 2 → ZMod (2 ^ n) // f v = u}) // P p.1} := by
    exact Nat.card_congr (e.subtypeEquiv (by intro v; simp [e]))
  dsimp only
  rw [show (fun v : Fin 2 → ZMod (2 ^ n) => P (r ∘ v)) = (fun v => P (f v)) by
    funext v; rw [hf_apply]]
  let : Fintype (Subtype P) := Fintype.ofFinite _
  rw [he, Nat.card_congr (Equiv.subtypeSigmaEquiv
    (fun u : Fin 2 → ZMod (2 ^ (n - 2)) =>
      {v : Fin 2 → ZMod (2 ^ n) // f v = u}) P), Nat.card_sigma]
  simp_rw [hfiber, hcommon]
  simp [Finset.sum_const, Nat.card_eq_fintype_card, mul_comm]

end TwoPowerNorm
