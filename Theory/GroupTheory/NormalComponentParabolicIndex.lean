module
public import Theory.GroupTheory.SylowNormalIntersectionIndex
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# Parabolic degrees in a normal Sylow supplement

Let G=KS with K normal and S Sylow two. Restricting S to K and then
factoring by O₂(K) preserves its index. If A contains S and A/O₂(A) is S₃,
then [G:A] is one third of the odd part of |K/O₂(K)|. The formula uses the
actual subgroup intersection and the literal two-core quotient.

This determines the coset permutation degrees in Aschbacher–Smith 13.4.7,
printed pp.900–901, without an automorphism-extension classification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Exact degree of a parabolic in a normal Sylow supplement. -/
theorem normal_component_parabolic_index (K : Subgroup G) [K.Normal]
    (S : Sylow 2 G) (hgen : K ⊔ (S : Subgroup G) = ⊤)
    (A : Subgroup G) (hSA : (S : Subgroup G) ≤ A)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) :
    A.index * 3 * 2 ^ (Nat.card (K ⧸ pCore 2 K)).factorization 2 =
      Nat.card (K ⧸ pCore 2 K) := by
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal K
  have hi : R.index = S.index := by
    have hh := normal_intersection_relIndex (S : Subgroup G) ⊤ K le_top
      (by rw [hgen])
    simpa only [←hR,top_subgroupOf,relIndex_top_right] using hh
  let q := QuotientGroup.mk' (pCore 2 K)
  let U := R.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 K))
  have hU : U.index = S.index := (R.index_map_of_two_kernel q
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)).trans hi
  have hcount := (U : Subgroup (K ⧸ pCore 2 K)).index_mul_card
  rw [U.card_eq_multiplicity,hU] at hcount
  have hrel := (S : Subgroup G).relIndex_mul_index hSA
  have hthree : (S : Subgroup G).relIndex A = 3 :=
    SymmetricThreeTwoCore.sylow_index_three eA (S.subtype hSA)
  rw [hthree] at hrel
  rw [←hrel,Nat.mul_comm 3 A.index] at hcount
  exact hcount
end Subgroup
