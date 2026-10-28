module

public import Theory.GroupTheory.ChiefFactorDirectPower
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Simplicity when a prime occurs once in a chief factor's order

A finite characteristically simple group is a positive direct power Sⁿ of a
simple subgroup. If p divides its order but p² does not, then p divides |S|
and n must be one. This numerical consequence of the direct-power theorem
is useful for proving simplicity of concrete minimal normal subgroups.

Source: the characteristically simple structure theorem proved in the imported
module (Aschbacher, 1986, 8.2); the final divisibility argument is elementary.
-/

public section

namespace CharacteristicallySimple
variable {G : Type*} [Group G] [Finite G] [Nontrivial G]

/-- A finite characteristically simple group is simple if some prime occurs
to exponent one in its order. -/
theorem isSimpleGroup_of_prime_dvd_card_of_sq_not_dvd
    (hchar : ∀ C : Subgroup G, C.Characteristic → C = ⊥ ∨ C = ⊤)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card G) (hsq : ¬ p ^ 2 ∣ Nat.card G) :
    IsSimpleGroup G := by
  obtain ⟨S, hS, n, hn, ⟨e⟩⟩ := exists_simple_subgroup_power hchar
  have hc : Nat.card G = Nat.card S ^ n := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_fin]
  have hdp : p ∣ Nat.card S := hp.dvd_of_dvd_pow (hc ▸ hd)
  have hn1 : n = 1 := by
    by_contra hne
    have hn2 : 2 ≤ n := by omega
    apply hsq
    rw [hc]
    exact (pow_dvd_pow_of_dvd hdp 2).trans (pow_dvd_pow _ hn2)
  subst n
  exact ((e.trans (MulEquiv.piUnique (fun _ : Fin 1 => S))).isSimpleGroup_congr).mpr hS

end CharacteristicallySimple
