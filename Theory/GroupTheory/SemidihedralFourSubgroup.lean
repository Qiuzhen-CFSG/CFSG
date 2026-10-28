module
public import Theory.GroupTheory.SemidihedralCenter
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
public import Theory.ElementaryAbelian.Basic

/-!
# The canonical four-subgroup in a semidihedral presentation

The half-order power of the cyclic generator and the involutory generator
generate an elementary four-group. The center calculation makes them commute;
they are distinct because the two original generators do not commute.
Mapping this subgroup along an inclusion supplies an actual ambient four-group.

Source: the semidihedral presentation and center calculation in
Alperin–Brauer–Gorenstein, Chapter II, §1, Lemma 1
(`refs/latex/alperin-brauer-gorenstein.tex`).
-/

namespace Semidihedral

/-- The canonical four-group of the explicit semidihedral presentation. -/
public theorem canonical_four
    {H : Type*} [Group H] {n : ℕ} (hn : 4 ≤ n) (a b : H)
    (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : Subgroup.closure ({a, b} : Set H) = ⊤) :
    IsElementaryAbelian 2 (Subgroup.closure ({a ^ (2 ^ (n - 2)), b} : Set H)) ∧
      Nat.card (Subgroup.closure ({a ^ (2 ^ (n - 2)), b} : Set H)) = 4 := by
  let z := a ^ (2 ^ (n - 2))
  have hz : orderOf z = 2 := by
    dsimp [z]
    rw [orderOf_pow_of_dvd (by positivity)
      (by rw [ha]; exact pow_dvd_pow 2 (by omega)), ha]
    rw [show n - 1 = n - 2 + 1 by omega, pow_succ,
      Nat.mul_div_right _ (by positivity)]
  have hzZ : z ∈ Subgroup.center H := by
    rw [center_eq hn a b ha hb hconj hgen]
    exact Subgroup.mem_zpowers z
  have hzb : z ≠ b := by
    intro heq
    apply generators_not_commute hn ha hconj
    rw [← heq]
    exact Commute.self_pow a _
  let : IsKleinFour (Subgroup.closure ({z, b} : Set H)) :=
    Subgroup.isKleinFour_closure_pair_of_orderOf z b hz hb hzb
      (Subgroup.mem_center_iff.mp hzZ b).symm
  exact ⟨{ toIsMulCommutative := IsKleinFour.isMulCommutative
           exponent_dvd_p := by simp }, IsKleinFour.card_four⟩

/-- An explicitly presented semidihedral subgroup contains an ambient four-group. -/
public theorem exists_four_le
    {G : Type*} [Group G] (Q : Subgroup G)
    {n : ℕ} (hn : 4 ≤ n) (a b : Q)
    (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : Subgroup.closure ({a, b} : Set Q) = ⊤) :
    ∃ V : Subgroup G, IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧ V ≤ Q := by
  let E := Subgroup.closure ({a ^ (2 ^ (n - 2)), b} : Set Q)
  obtain ⟨hEe, hE⟩ := canonical_four hn a b ha hb hconj hgen
  let : IsElementaryAbelian 2 E := hEe
  refine ⟨E.map Q.subtype, IsElementaryAbelian.map Q.subtype, ?_,
    Subgroup.map_subtype_le _⟩
  rwa [Subgroup.card_map_of_injective Q.subtype_injective]

end Semidihedral
