module
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.Statements
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.QuotientCoordinates
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.PrimeRankElementary

/-!
# The rank-two quotient in the original component-intersection hypothesis

When m₃(Y₊)=2, the S₃ quotient alternative of15.3.11(5) is impossible:
quotienting by a two-group preserves three-rank, while S₃ has three-rank
at most one. Thus the literal Y₊/O₂(Y₊) is E₉ or extraspecial of order27
and exponent3. These facts supply the odd-rank and inner-splitting inputs
of Aschbacher--Smith15.3.12, printed pp.1124--1125.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.ComponentIntersection
open OutsideStructure
variable {G : Type*} [Group G] [Finite G]

private theorem symmetricThree_rank_le_one : primeRank 3 (Equiv.Perm (Fin 3)) ≤ 1 := by
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let : IsElementaryAbelian 3 E := hE
  have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hd : Nat.card E ∣ 3*2 := by simpa only [hc] using E.card_subgroup_dvd_card
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 3 E).exists_card_eq
  have hp : Nat.Coprime (Nat.card E) 2 := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_left n
  exact Nat.le_of_dvd (by decide) (hp.dvd_mul_right.mp hd)

theorem rank_two_case_of_three_rank_two (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (h : RankTwoCase d I ∨ RankOneCase d I)
    (hr : primeRank 3 d.Yplus = 2) : RankTwoCase d I := by
  rcases h with h | h
  · exact h
  obtain ⟨e⟩ := h.2.1
  have hs : primeRank 3 ↥(d.Yplus ⊔ d.S) ≤ 1 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 ↥(d.Yplus ⊔ d.S))
      pCore_isPGroup,primeRank_congr 3 e]
    exact symmetricThree_rank_le_one
  have hl := (primeRank_mono 3 (show d.Yplus ≤ d.Yplus ⊔ d.S from le_sup_left)).trans hs
  omega

omit [Finite G] in
theorem cubic_quotient_facts (Y : Subgroup G) (h : CubicQuotient (TwoCoreQuotient Y)) :
    IsPGroup 3 (TwoCoreQuotient Y) ∧ Monoid.exponent (TwoCoreQuotient Y) ∣ 3 ∧
      (Nonempty (TwoCoreQuotient Y ≃* ElementaryNine) ∨
        (IsExtraspecial 3 (TwoCoreQuotient Y) ∧ Nat.card (TwoCoreQuotient Y) = 27)) := by
  rcases h with h | h
  · obtain ⟨e⟩ := h
    have hc : Nat.card (TwoCoreQuotient Y) = 3^2 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Fin 2 → ZMod 3) = 3^2
      simp only [Nat.card_fun,Nat.card_zmod,Nat.card_fin]
    refine ⟨IsPGroup.of_card hc,Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_,Or.inl ⟨e⟩⟩
    intro x
    apply e.injective
    rw [map_pow,map_one]
    apply Multiplicative.toAdd.injective
    change 3 • (e x).toAdd = 0
    funext i
    exact (by decide : ∀ z : ZMod 3, 3 • z = 0) _
  · obtain ⟨hx,hc,he⟩ := h
    exact ⟨IsPGroup.of_card (n := 3) hc,
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr he,Or.inr ⟨hx,hc⟩⟩

end CFSG.Quasithin.Chapter15.Section03.ComponentIntersection
