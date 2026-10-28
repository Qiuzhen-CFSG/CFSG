module
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow two-subgroups of a product of two symmetric triples

Every Sylow two-subgroup of S₃ × S₃ is elementary abelian of order four.
The order follows from the ambient order 36; each coordinate of a
fourth-power-one element squares to one. The result transports through
an actual group equivalence and supplies the actor in the Omega fixed-line
calculation used by Aschbacher--Smith 14.1.17 and 15.2.3.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace SymmetricThreeProductResidual
theorem sylow_elementary_four {D : Type*} [Group D]
    (e : D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) (P : Sylow 2 D) :
    IsElementaryAbelian 2 P ∧ Nat.card P = 4 := by
  let : Finite D := Finite.of_equiv _ e.symm.toEquiv
  have hD : Nat.card D = 36 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_fin]
    decide
  have hP : Nat.card P = 4 := by rw [P.card_eq_multiplicity, hD]; decide +kernel
  have hs : ∀ a : Equiv.Perm (Fin 3), a ^ 4 = 1 → a ^ 2 = 1 := by decide +kernel
  let : IsMulCommutative P := IsPGroup.isMulCommutative_of_card_eq_prime_sq
    (show Nat.card P = 2 ^ 2 from hP)
  refine ⟨{ exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ },hP⟩
  intro a
  apply Subtype.ext
  change (a : D) ^ 2 = 1
  apply e.injective
  rw [map_pow, map_one]
  have ha : (e a.val) ^ 4 = 1 := by
    have h := pow_card_eq_one' (x := a)
    rw [hP] at h
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one] using
      congrArg (fun x : P => e x.val) h
  exact Prod.ext (hs _ (congrArg Prod.fst ha)) (hs _ (congrArg Prod.snd ha))
end SymmetricThreeProductResidual
