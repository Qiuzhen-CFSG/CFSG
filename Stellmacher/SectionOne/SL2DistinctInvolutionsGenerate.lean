module
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Mathlib.Tactic.IntervalCases

/-!
# Two involutions generate an SL₂(2) factor

Two distinct involutions in an `SL₂(2)` subgroup generate that subgroup.
Their cyclic subgroups have order two and are distinct. Their join lies in
the factor, whose order is six; Lagrange's theorem leaves no possible proper
join containing both order-two subgroups. The statement stays in the ambient
group so quotient-image involutions can be used directly.

This elementary group fact is used for the factor image in Stellmacher (9.4).
The factor identification and the chosen involutions come from the actual
local quotient action; the argument here adds no action hypothesis.
-/

namespace Stellmacher.SectionOne

universe u

/-- Distinct involutions generate an `SL₂(2)` subgroup they both belong to. -/
public theorem sl2_distinct_involutions_generate
    {K : Type u} [Group K] [Finite K]
    (D : Subgroup K) (hD : IsSL2Two D)
    (t u : K) (ht : t ∈ D) (hu : u ∈ D)
    (ht2 : IsInvolution t) (hu2 : IsInvolution u) (hne : t ≠ u) :
    D = Subgroup.zpowers t ⊔ Subgroup.zpowers u := by
  let Q := Subgroup.zpowers t
  let R := Subgroup.zpowers u
  have hQcard : Nat.card Q = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ht2.2 ht2.1]
  have hRcard : Nat.card R = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hu2.2 hu2.1]
  have hQR : Q ≠ R := by
    intro he
    have htR : t ∈ R := he ▸ Subgroup.mem_zpowers t
    obtain ⟨r, hr, huniq⟩ := (Nat.card_eq_two_iff' (1 : R)).mp hRcard
    have htne : (⟨t, htR⟩ : R) ≠ 1 := by
      intro h
      exact ht2.1 (congrArg Subtype.val h)
    have hune : (⟨u, Subgroup.mem_zpowers u⟩ : R) ≠ 1 := by
      intro h
      exact hu2.1 (congrArg Subtype.val h)
    exact hne (congrArg Subtype.val ((huniq _ htne).trans (huniq _ hune).symm))
  let J := Q ⊔ R
  have hJD : J ≤ D := sup_le ((Subgroup.zpowers_le).2 ht) ((Subgroup.zpowers_le).2 hu)
  have hDcard : Nat.card D = 6 :=
    RankOneThreeGroupAssembly.isSL2Two_card hD
  have hdiv : Nat.card J ∣ 6 := hDcard ▸ Subgroup.card_dvd_of_le hJD
  have htwo : 2 ∣ Nat.card J :=
    hQcard ▸ Subgroup.card_dvd_of_le (le_sup_left : Q ≤ J)
  have hbound : Nat.card J ≤ 6 := Nat.le_of_dvd (by decide) hdiv
  have hneq : Nat.card J ≠ 2 := by
    intro hh
    have hQJ := Subgroup.eq_of_le_of_card_ge (le_sup_left : Q ≤ J) (by
      rw [hQcard, hh])
    have hRJ := Subgroup.eq_of_le_of_card_ge (le_sup_right : R ≤ J) (by
      rw [hRcard, hh])
    exact hQR (hQJ.trans hRJ.symm)
  have hJcard : Nat.card J = 6 := by
    interval_cases hn : Nat.card J <;> norm_num at *
  exact (Subgroup.eq_of_le_of_card_ge hJD (by omega)).symm

end Stellmacher.SectionOne
