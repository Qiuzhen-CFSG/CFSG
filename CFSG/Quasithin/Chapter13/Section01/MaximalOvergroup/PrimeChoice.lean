module

public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.Source

/-!
# Choosing the actual odd radical in the 13.1 counterexample

A.3.6 makes the quotient by the Fitting subgroup quasisimple. Hence the
Fitting subgroup of a nonquasisimple local quotient is nontrivial. It has
odd order, so choose an odd prime divisor and transport it through the
actual local-quotient equivalence. The radical theorem then gives p > 3
and its precise elementary or extraspecial quotient. This removes the
prime-choice premise from the maximal-overgroup construction.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
13.1.4(3) and the choice of the family X in 13.1.7, pp.867--868.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.Section02.Adequate

namespace CFSG.Quasithin.Chapter13.Section01
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem fitting_map_le {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom ≤ fittingSubgroup B := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  rintro N ⟨hN, hnil⟩
  apply map_le_iff_le_comap.mp
  let := hnil
  exact le_sSup ⟨hN.map _ e.surjective, Group.nilpotent_of_mulEquiv (e.subgroupMap N)⟩

private theorem fitting_prime_transport {A B : Type*} [Group A] [Group B] [Finite B]
    (e : A ≃* B) {p : ℕ} (hd : p ∣ Nat.card (fittingSubgroup A)) :
    p ∣ Nat.card (fittingSubgroup B) := by
  rw [Nat.card_congr (e.subgroupMap (fittingSubgroup A)).toEquiv] at hd
  exact hd.trans (card_dvd_of_le (fitting_map_le e))

private theorem common_odd_prime {A : Type*} [Group A] [Finite A]
    (h : A36Common A) (hn : ¬ IsQuasisimple A) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ Nat.card (fittingSubgroup A) := by
  have hne : Nat.card (fittingSubgroup A) ≠ 1 := by
    intro he
    have hb : fittingSubgroup A = ⊥ := (card_le_one_iff_eq_bot _).mp he.le
    let := h.2.1
    exact hn (IsQuasisimple.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot))
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd hne
  refine ⟨p, hp, ?_, hd⟩
  rcases hp.eq_two_or_odd' with rfl | ho
  · have hc := pPrimeCore_coprime_card (p := 2) (G := A)
    rw [← h.1] at hc
    have hh := Nat.dvd_gcd (dvd_refl 2) hd
    rw [hc] at hh
    norm_num at hh
  · exact ho

/-- The source nonquasisimple component supplies an actual prime p > 3 and
its actual canonical radical; no prime or model marking is an extra input. -/
theorem exists_odd_radical_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ C : Subgroup D, C.IsCComponent → A36Conclusion C)
    {T : Sylow 2 G} {L₀ : Subgroup G} (hL : L₀ ∈ nonquasisimpleFaithful T) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 < p ∧
      p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)) ∧
      XiOddQuotient p (XiQuotient (XiP p L₀)) ∧ XiP p L₀ ≠ ⊥ := by
  have hl := ((mem_faithfulLocalComponents_iff T L₀).mp hL.1).1
  have hQ := uniqueness_local_quotient_sqtk hG hl.2.2
  let e := radicalLocalQuotientEquiv hl
  have hc := proposition_1_2_1_four_earlier_conclusion hA36 hQ hl.1
  have hn : ¬ IsQuasisimple (radicalLocalImage T L₀) := by
    intro h
    let := h
    exact hL.2 (IsQuasisimple.of_mulEquiv e.symm)
  obtain ⟨p, hp, ho, hd⟩ := common_odd_prime hc.2 hn
  have hd' : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)) :=
    fitting_prime_transport e.symm hd
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hp3, hodd⟩ := XiP_oddQuotient_of_A36 hA36 hl hQ hL.2 ho hd'
  exact ⟨p, hp, ho, hp3, hd', hodd, XiP_ne_bot_of_oddQuotient hp L₀ hodd⟩

/-- The initial maximal counterexample choice of 13.1.7, with its odd prime
constructed and its two Sylow-normalizer hypotheses discharged. The
remaining normality assertion is the earlier 13.1.4 embedding exclusion. -/
theorem exists_maximal_source_counterexample
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ C : Subgroup D, C.IsCComponent → A36Conclusion C)
    (hA38 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ C : Subgroup D, C.IsCComponent → C.Normal ∨ IsQuasisimple C)
    (hA410 : A410EarlierResult G)
    {T : Sylow 2 G} {L₀ : Subgroup G} (hL : L₀ ∈ nonquasisimpleFaithful T)
    (hN : ∀ p : ℕ, p.Prime → Odd p →
      p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)) →
      ∀ K ∈ L G T, L₀ ≤ K → ((XiP p L₀).subgroupOf K).Normal) :
    ∃ K ∈ LStar G T, L₀ ≤ K ∧ K ∈ nonquasisimpleFaithful T ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 < p ∧
        p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)) ∧
        ((XiP p L₀).subgroupOf K).Normal ∧ XiP p L₀ ≠ ⊥ := by
  obtain ⟨p, hp, ho, hp3, hd, _, hne⟩ := exists_odd_radical_source hG hA36 hL
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hK, hLK, hn, hTK, hNX⟩ :=
    exists_maximal_nonquasisimple_overgroup hG hA36 hA38 hA410 hL ho hd (hN p hp ho hd)
  exact ⟨K, hK, hLK, hn, hTK, p, hp, ho, hp3, hd, hNX, hne⟩

end CFSG.Quasithin.Chapter13.Section01
