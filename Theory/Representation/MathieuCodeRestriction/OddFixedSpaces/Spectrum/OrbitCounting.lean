module

public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Counting native point orbits of prime-order subgroups

Every nonidentity element of a prime-order group generates it, so Burnside's
formula becomes `p · orbits = 24 + (p - 1) · fixedPoints`. This retains the
literal action of the subgroup on the native twenty-four points.

Used for Aschbacher–Smith, H.15.7, printed pp.401–402.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
open Sporadic.Mathieu
namespace MathieuCode

theorem prime_point_orbit_count (D : Subgroup M24) {p : ℕ} (hp : p.Prime)
    (hD : Nat.card D = p) :
    Nat.card (MulAction.orbitRel.Quotient D (Fin 24)) * p =
      24 + (p - 1) * Nat.card (MulAction.fixedPoints D (Fin 24)) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype D := Fintype.ofFinite D
  let : Fintype (MulAction.orbitRel.Quotient D (Fin 24)) := Fintype.ofFinite _
  let : ∀ a : D, Fintype (MulAction.fixedBy (Fin 24) a) := fun _ => Fintype.ofFinite _
  have hf (a : D) (ha : a ≠ 1) :
      MulAction.fixedBy (Fin 24) a = MulAction.fixedPoints D (Fin 24) := by
    ext x
    constructor
    · intro hx b
      exact smul_eq_self_of_mem_zpowers (mem_zpowers_of_prime_card hD ha) hx
    · intro hx
      exact hx a
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group D (Fin 24)
  have hsum : (∑ a : D, Nat.card (MulAction.fixedBy (Fin 24) a)) =
      24 + (p - 1) * Nat.card (MulAction.fixedPoints D (Fin 24)) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : D))]
    have hs : (∑ a ∈ Finset.univ.erase (1 : D), Nat.card (MulAction.fixedBy (Fin 24) a)) =
        (Fintype.card D - 1) * Nat.card (MulAction.fixedPoints D (Fin 24)) := by
      rw [show (∑ a ∈ Finset.univ.erase (1 : D), Nat.card (MulAction.fixedBy (Fin 24) a)) =
        ∑ _a ∈ Finset.univ.erase (1 : D), Nat.card (MulAction.fixedPoints D (Fin 24)) from
        Finset.sum_congr rfl (fun a ha => congrArg (fun S : Set (Fin 24) => Nat.card S) (hf a (Finset.mem_erase.mp ha).1))]
      simp
    have hc : Fintype.card D = p := by simpa only [Nat.card_eq_fintype_card] using hD
    rw [hs, MulAction.fixedBy_one_eq_univ]
    simp [Nat.card_eq_fintype_card, hc, Nat.add_comm]
  have hbn : (∑ a : D, Nat.card (MulAction.fixedBy (Fin 24) a)) =
      Nat.card (MulAction.orbitRel.Quotient D (Fin 24)) * Nat.card D := by
    simpa only [Nat.card_eq_fintype_card] using hb
  rw [hD] at hbn
  exact hbn.symm.trans hsum
end MathieuCode
