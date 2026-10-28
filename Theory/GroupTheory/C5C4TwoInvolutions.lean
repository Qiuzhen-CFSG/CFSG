module

public import Theory.GroupTheory.C5C4ElementaryTwoSubgroup
public import Theory.ElementaryAbelian.Join
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Distinct involution subgroups in C5 semidirect C4

For any action of C4 on C5, two distinct subgroups of order two generate a
subgroup containing the normal C5 factor. No faithfulness assumption on
the action is needed.

If the two subgroups centralized one another, their join would be elementary
abelian of exponent two. The projection bound for elementary two-subgroups
of C5 semidirect C4 would force that join to equal both subgroups. Thus their
commutator is nontrivial. Since the right quotient is abelian, the commutator
lies in the normal factor of prime order five and consequently equals it.

This source-neutral fact supplies the involution transfer in Stellmacher's
proof of (10.1)(20), printed page 65, using native Multiplicative/ZMod groups.
-/

namespace SemidirectProduct

public theorem normal_five_le_sup_of_distinct_two_subgroups
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (A B : Subgroup (SemidirectProduct (Multiplicative (ZMod 5))
      (Multiplicative (ZMod 4)) φ))
    (hA : Nat.card A = 2) (hB : Nat.card B = 2) (hne : A ≠ B) :
    (inl : Multiplicative (ZMod 5) →*
      SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ).range ≤
        A ⊔ B := by
  let _ : Finite (SemidirectProduct (Multiplicative (ZMod 5))
      (Multiplicative (ZMod 4)) φ) :=
    Finite.of_equiv (Multiplicative (ZMod 5) × Multiplicative (ZMod 4)) equivProd.symm
  let _ : IsCyclic A := isCyclic_of_prime_card hA
  let _ : IsCyclic B := isCyclic_of_prime_card hB
  let _ : IsElementaryAbelian 2 A := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := by rw [IsCyclic.exponent_eq_card, hA]
  }
  let _ : IsElementaryAbelian 2 B := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := by rw [IsCyclic.exponent_eq_card, hB]
  }
  have hcomm : ⁅A, B⁆ ≠ ⊥ := by
    intro hzero
    have hcentral : B ≤ Subgroup.centralizer (A : Set _) :=
      Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hzero)
    have helem : IsElementaryAbelian 2 ↥(A ⊔ B) :=
      IsElementaryAbelian.sup_of_le_centralizer hcentral
    have hcard : Nat.card ↥(A ⊔ B) ≤ 2 :=
      elementary_two_subgroup_card_le_two φ (A ⊔ B) helem
    have hAsup : A = A ⊔ B :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by simpa [hA] using hcard)
    have hBsup : B = A ⊔ B :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by simpa [hB] using hcard)
    exact hne (hAsup.trans hBsup.symm)
  let F : Subgroup (SemidirectProduct (Multiplicative (ZMod 5))
      (Multiplicative (ZMod 4)) φ) := inl.range
  have hFcard : Nat.card F = 5 := by
    rw [show F = inl.range from rfl, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective inl_injective, Subgroup.card_top]
    norm_num
  have hcommF : ⁅A, B⁆ ≤ F := by
    change ⁅A, B⁆ ≤ inl.range
    rw [range_inl_eq_ker_rightHom]
    apply Subgroup.commutator_le.mpr
    intro a _ha b _hb
    rw [MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hcommcard : Nat.card ↥⁅A, B⁆ = 5 := by
    have hdvd : Nat.card ↥⁅A, B⁆ ∣ 5 := by
      simpa only [hFcard] using Subgroup.card_dvd_of_le hcommF
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hdvd with hone | hfive
    · exact False.elim (hcomm (Subgroup.card_eq_one.mp hone))
    · exact hfive
  have hcomm_eq : ⁅A, B⁆ = F :=
    Subgroup.eq_of_le_of_card_ge hcommF (by rw [hcommcard, hFcard])
  change F ≤ A ⊔ B
  rw [← hcomm_eq]
  exact Subgroup.commutator_le_sup A B

end SemidirectProduct
