module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Linarith

/-!
# Centralizers of four-groups containing a cyclic-core inverter

Let an abelian subgroup A of order four lie in T. If one element of A
inverts a cyclic subgroup H with relative index at most four in T, then
C_T(A) is abelian. Its intersection with H is cyclic of exponent at most
two, so C_T(A) has order at most eight. Since A lies in its center, the
quotient by its center has order at most two and is cyclic.

No normality of H and no two-group assumption on T are needed. Relative
index means the index of H intersect T in T. This supplies the group
algebra for the odd-unitary outer-actor application in Aschbacher--Smith,
E.1.14(7), printed p.214; it does not assert the required model geometry.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- An inverter of a cyclic subgroup of relative index at most four makes
the centralizer of an abelian four-group commutative. -/
theorem four_actor_centralizer_isMulCommutative_of_inverts_cyclic
    (T H A : Subgroup G) [IsCyclic H] [IsMulCommutative A]
    (hAT : A ≤ T) (hfour : Nat.card A = 4) (hindex : H.relIndex T ≤ 4)
    {t : G} (htA : t ∈ A)
    (hinv : ∀ x ∈ H, t * x * t⁻¹ = x⁻¹) :
    IsMulCommutative (T ⊓ centralizer (A : Set G) : Subgroup G) := by
  let R := T ⊓ centralizer (A : Set G)
  let I := R ⊓ H
  let : IsCyclic I := isCyclic_of_le (show I ≤ H from inf_le_right)
  have hI : Nat.card I ≤ 2 := by
    apply Nat.le_of_dvd (by decide : 0 < 2)
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    apply Subtype.ext
    have hc : t * (x : G) = (x : G) * t :=
      mem_centralizer_iff.mp x.property.1.2 t htA
    have he : (x : G) = (x : G)⁻¹ := by
      calc
        (x : G) = t * (x : G) * t⁻¹ := by rw [hc, mul_inv_cancel_right]
        _ = (x : G)⁻¹ := hinv x x.property.2
    change (x : G) ^ 2 = 1
    simpa only [pow_two] using (mul_eq_one_iff_eq_inv.mpr he)
  have hIR : I.relIndex R ≤ 4 := by
    rw [show I = R ⊓ H from rfl, inf_relIndex_left]
    exact (relIndex_le_of_le_right (show R ≤ T from inf_le_left)
      (H.subgroupOf T).index_ne_zero_of_finite).trans hindex
  have hR : Nat.card R ≤ 8 := by
    have hm := (I.subgroupOf R).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show I ≤ R from inf_le_left)).toEquiv] at hm
    change Nat.card I * I.relIndex R = Nat.card R at hm
    nlinarith
  have hAR : A ≤ R := le_inf hAT (le_centralizer A)
  have hAC : A.subgroupOf R ≤ center R := by
    intro a ha
    rw [mem_center_iff]
    intro r
    apply Subtype.ext
    exact mem_centralizer_iff.mp r.property.2 a ha |>.symm
  have hcenter : 4 ≤ Nat.card (center R) := by
    have he : Nat.card (A.subgroupOf R) = 4 :=
      (Nat.card_congr (subgroupOfEquivOfLe hAR).toEquiv).trans hfour
    exact he ▸ card_le_of_le hAC
  have hquot : Nat.card (R ⧸ center R) ≤ 2 := by
    have hm := (center R).card_mul_index
    change Nat.card (center R) * Nat.card (R ⧸ center R) = Nat.card R at hm
    nlinarith
  have hpos : 0 < Nat.card (R ⧸ center R) := Nat.card_pos
  have hdvd : Nat.card (R ⧸ center R) ∣ 2 := by
    have hcases : Nat.card (R ⧸ center R) = 1 ∨ Nat.card (R ⧸ center R) = 2 := by omega
    rcases hcases with h | h <;> simp [h]
  let : IsCyclic (R ⧸ center R) := isCyclic_of_card_dvd_prime (p := 2) hdvd
  exact isMulCommutative_of_isCyclic_quotient_center_self R
end Subgroup
