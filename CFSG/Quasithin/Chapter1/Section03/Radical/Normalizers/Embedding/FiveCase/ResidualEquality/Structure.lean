module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.FiveCase.ResidualEquality.Orders

/-!
# The order and odd Fitting primes in the five case

A.3.6 forces the square of each Fitting prime to divide the group order:
its prime core has a rank-two homocyclic or extraspecial shape. Among the
odd divisors of |PSL₃(5)| = 372000, only five occurs more than once.
The remaining SL₂(5) quotient has order 120, so the Fitting subgroup has
order 25 and the whole group has order 3000.

All four alternatives and the common clauses of A.3.6 are retained. In
particular, the five-divisibility hypothesis excludes the quasisimple
alternatives using their actual Fitting subgroups.

Source: Aschbacher–Smith, A.3.6, printed pp.43–45, and the proof of
1.3.8, printed p.513, combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase.ResidualEquality
open Section02 Section02.LocalModels
universe u
variable {E : Type u} [Group E] [Finite E] {D : Subgroup E}

private theorem odd_prime_of_square_dvd {q : ℕ} (hq : q.Prime) (ho : Odd q)
    (hd : q ^ 2 ∣ 372000) : q = 5 := by
  have hqdiv := (dvd_pow_self q (by decide : 2 ≠ 0)).trans hd
  change q ∣ 2 ^ 5 * 3 * 5 ^ 3 * 31 at hqdiv
  simp only [hq.dvd_mul] at hqdiv
  rcases hqdiv with ((h2 | h3) | h5) | h31
  · have he := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2)
    subst q
    norm_num [Nat.odd_iff] at ho
  · have he := (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 3)).mp h3
    subst q
    norm_num at hd
  · exact (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 5)).mp (hq.dvd_of_dvd_pow h5)
  · have he := (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 31)).mp h31
    subst q
    norm_num at hd

private theorem square_dvd_core {A : Type*} [Group A] [Finite A]
    (h : A36Natural A ∨ A36Nilpotent A) {q : ℕ} [Fact q.Prime]
    (hd : q ∣ Nat.card (fittingSubgroup A)) : q ^ 2 ∣ Nat.card (pCore q A) := by
  obtain ⟨_, hshape⟩ := RadicalStructure.core_omega h hd
  have hs : q ^ 2 ∣ Nat.card (omega (pCore q A) (p := q) 1) := by
    rcases hshape with ⟨_, hc⟩ | ⟨_, hc, _⟩
    · rw [hc]
    · rw [hc]; exact pow_dvd_pow q (by decide)
  exact hs.trans (card_subgroup_dvd_card _)

private theorem not_quasisimple_of_generalized_eq_fitting {A : Type*}
    [Group A] [Finite A] (h : generalizedFitting A = fittingSubgroup A) :
    ¬ IsQuasisimple A := by
  intro hA
  let := hA
  have htop : (⊤ : Subgroup A) ≤ generalizedFitting A :=
    component_le_generalizedFitting A ⊤
      ⟨(inferInstance : (⊤ : Subgroup A).Normal).isSubnormal,
        IsQuasisimple.of_mulEquiv topEquiv.symm⟩
  have hfit : fittingSubgroup A = ⊤ := top_unique (h ▸ htop)
  let : Group.IsNilpotent A := Group.nilpotent_of_mulEquiv
    ((MulEquiv.subgroupCongr hfit).trans topEquiv)
  let : IsSimpleGroup (A ⧸ center A) := IsQuasisimple.simple
  let : Nontrivial A := Function.Surjective.nontrivial
    (QuotientGroup.mk'_surjective (center A))
  exact Group.IsPerfect.not_isSolvable A inferInstance

private theorem radical_of_five_dvd (h : A36Conclusion D)
    (h5 : 5 ∣ Nat.card (fittingSubgroup D)) : A36Natural D ∨ A36Nilpotent D := by
  apply RadicalStructure.nonsimple_radical h
  rcases h.2.2.2.1 with hh | hh
  · exact not_quasisimple_of_generalized_eq_fitting hh.1.symm
  · rcases hh.2.2 with he | he <;> rw [he] at h5 <;> norm_num at h5

private theorem radical_quotient_five {A : Type*} [Group A] [Finite A]
    (h : A36Natural A ∨ A36Nilpotent A)
    (h5 : 5 ∣ Nat.card (fittingSubgroup A)) :
    IsSL (A ⧸ fittingSubgroup A) 2 5 := by
  rcases h with h | h
  · obtain ⟨hF, r, hr, _, ha⟩ := h
    have hc := (RadicalStructure.natural_elementary ha).2
    have hd : 5 ∣ r ^ 2 := by simpa only [← hF, hc] using h5
    have hr5 : 5 = r := (Nat.prime_dvd_prime_iff_eq (by decide) hr).mp
      ((by decide : Nat.Prime 5).dvd_of_dvd_pow hd)
    subst r
    obtain ⟨F, _, _, hcF, v, ρ, _⟩ := ha
    exact ⟨F, inferInstance, inferInstance, hcF,
      ⟨(QuotientGroup.quotientMulEquivOfEq hF).symm.trans ρ⟩⟩
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h.2.2.1
    exact ⟨F, inferInstance, inferInstance, hF,
      ⟨(QuotientGroup.quotientMulEquivOfEq h.1).symm.trans e⟩⟩

theorem order_and_fitting_support_of_A36 (h : A36Conclusion D)
    (h5 : 5 ∣ Nat.card (fittingSubgroup D)) (hd : Nat.card D ∣ 372000) :
    Nat.card D = 3000 ∧ ∀ q : ℕ, q.Prime → Odd q →
      (q ∣ Nat.card (fittingSubgroup D) ↔ q = 5) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hr := radical_of_five_dvd h h5
  have hs : ∀ q : ℕ, q.Prime → Odd q → q ∣ Nat.card (fittingSubgroup D) → q = 5 := by
    intro q hq ho hqF
    let : Fact q.Prime := ⟨hq⟩
    exact odd_prime_of_square_dvd hq ho
      ((square_dvd_core hr hqF).trans ((card_subgroup_dvd_card _).trans hd))
  have hc : pCore 5 D = fittingSubgroup D :=
    (RadicalStructure.core_eq_generalizedFitting hr h.2 hs).trans
      (hr.elim And.left And.left)
  have hFpow : ∃ a : ℕ, Nat.card (fittingSubgroup D) = 5 ^ a := by
    rw [← hc]
    exact pCore_isPGroup.exists_card_eq
  have hq := isSL_two_card (radical_quotient_five hr h5)
  norm_num at hq
  have hcount := (fittingSubgroup D).card_mul_index
  rw [index_eq_card, hq] at hcount
  have hFdiv : Nat.card (fittingSubgroup D) ∣ 3100 := by
    have hm : Nat.card (fittingSubgroup D) * 120 ∣ 3100 * 120 := hcount ▸ hd
    exact (Nat.mul_dvd_mul_iff_right (by decide : 0 < 120)).mp hm
  obtain ⟨a, ha⟩ := hFpow
  have ha2 : a ≤ 2 := by
    by_contra hn
    have he : 3 ≤ a := by omega
    have hh : 125 ∣ 3100 := (pow_dvd_pow 5 he).trans (ha ▸ hFdiv)
    norm_num at hh
  have hle : Nat.card (fittingSubgroup D) ≤ 25 := by
    rw [ha]
    exact Nat.pow_le_pow_right (by decide) ha2
  have hdiv25 : 25 ∣ Nat.card (fittingSubgroup D) := hc ▸ square_dvd_core hr h5
  have hF : Nat.card (fittingSubgroup D) = 25 :=
    le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdiv25)
  refine ⟨?_, fun q hq ho => ⟨hs q hq ho, ?_⟩⟩
  · rw [hF] at hcount
    exact hcount.symm
  · rintro rfl
    exact h5
end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase.ResidualEquality
