module

public import Theory.SpecificGroups.SymmetricFourSylow
public import Mathlib.Data.ZMod.Basic

/-!

# Sylow two-subgroups of C₂ times S₄

Every supplied Sylow two-subgroup of a finite group isomorphic to `C₂ × S₄`
is isomorphic to `C₂ × D₈`. The product of the whole C₂ factor with a Sylow
two-subgroup of S₄ has order sixteen, the full two-part of the model's order
48. Sylow conjugacy identifies any other Sylow with this product, and an
actual group isomorphism transports the result to the supplied group.

This elementary model calculation supplies the involution-centralizer shape
in the order-32 branch of Kurzweil–Stellmacher, The Theory of Finite Groups,
Chapter 12, printed p. 367. The dihedral S₄ Sylow calculation is imported
from `Theory.SpecificGroups.SymmetricFourSylow`.
-/

namespace CyclicTwoSymmetricFour

/-- Every Sylow two-subgroup of a `C₂ × S₄` model is `C₂ × D₈`. -/
public theorem sylow_two_equiv
    {K : Type*} [Group K] [Finite K]
    (hModel : Nonempty (K ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))
    (T : Sylow 2 K) :
    Nonempty (T ≃* Multiplicative (ZMod 2) × DihedralGroup 4) := by
  classical
  obtain ⟨e⟩ := hModel
  let U : Sylow 2 (Equiv.Perm (Fin 4)) := Sylow.nonempty.some
  obtain ⟨eU⟩ := Equiv.Perm.sylow_two_equiv_dihedral_four U
  let Q : Subgroup (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) :=
    (⊤ : Subgroup (Multiplicative (ZMod 2))).prod (U : Subgroup _)
  let eQ : Q ≃* Multiplicative (ZMod 2) × DihedralGroup 4 := by
    change ((⊤ : Subgroup (Multiplicative (ZMod 2))).prod
      (U : Subgroup (Equiv.Perm (Fin 4)))) ≃* _
    exact ((⊤ : Subgroup (Multiplicative (ZMod 2))).prodEquiv
      (U : Subgroup (Equiv.Perm (Fin 4)))).trans
      ((Subgroup.topEquiv : (⊤ : Subgroup (Multiplicative (ZMod 2))) ≃*
        Multiplicative (ZMod 2)).prodCongr eU)
  have hQcard : Nat.card Q = 16 := by
    rw [Nat.card_congr eQ.toEquiv, Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card, DihedralGroup.card]
  have hModelCard : Nat.card (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) = 48 := by
    norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  let V : Sylow 2 (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) := Sylow.ofCard Q (by
    rw [hQcard, hModelCard]
    rw [show 48 = 2 ^ 4 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization])
  let W := T.mapSurjective (f := e.toMonoidHom) e.surjective
  let eT : T ≃* W := e.subgroupMap (T : Subgroup K)
  exact ⟨(eT.trans (W.equiv V)).trans eQ⟩

end CyclicTwoSymmetricFour
