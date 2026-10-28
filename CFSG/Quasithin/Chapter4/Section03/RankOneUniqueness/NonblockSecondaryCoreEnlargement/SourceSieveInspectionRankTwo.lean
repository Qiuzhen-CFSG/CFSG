module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveInspectionOddCentralizer
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveTriality
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Complete
public import Theory.SpecificGroups.G2.BinaryResidualCover
public import Theory.SpecificGroups.Tits.ThreeRankLowerBound
public import Theory.NumberTheory.BinaryMinusPrimeRestriction

/-!
# Binary rank-two rows on the literal inner component

The odd-primary covering theorems make the full triality and Ree quotients
centerless, so their already proved source-action exclusions apply to the
inner-image catalogue. The symplectic cover is likewise identified with the
actual four-space model. In odd source degree an original torus prime has
odd binary order; the symplectic order formula forces it into the split
torus, contradicting the source split-prime exclusion. The cubic source
argument handles even degree.

The small symplectic and G₂ derived rows are transported to A₆ and PSU₃(3).
The Tits order forces source degree two, where its cubic rank contradicts
the source prime restriction. PSL₃(2) fails the original secondary-section
order. Thus only larger binary PSL₃, odd-source-degree G₂, and degree-five
J₄ remain. All models are actual equivalences of the original inner image;
central covers are removed only by their proved covering results.

Source: Aschbacher--Smith 4.3.12--16, printed pp.617--618; A.2.3--4 and
A.3.6, printed pp.32--33 and 43--45. The imported concrete calculations
retain their original source attribution and licenses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

private def fullInnerEquiv (s : SecondaryActionData c n)
    (hz : center (s.component ⧸ pCore 2 s.component) = ⊥) :
    (s.component ⧸ pCore 2 s.component) ≃* SecondaryActionData.componentImage s :=
  QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans
      (SecondaryActionData.sieveCentralQuotientEquiv s))

private theorem center_bot_of_two (s : SecondaryActionData c n)
    (hz : IsPGroup 2 (center (s.component ⧸ pCore 2 s.component))) :
    center (s.component ⧸ pCore 2 s.component) = ⊥ := by
  apply bot_unique
  rw [←pCore_quotient_pCore_eq_bot 2]
  exact le_sSup ⟨inferInstance,hz⟩

/-- The actual triality inner marking lifts across the full two-core quotient. -/
theorem SecondaryActionData.not_triality_inner (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n) {f : ℕ} (hf : 0<f)
    (hm : Triality.Standard.IsTrialityGroupAt (2^f) (SecondaryActionData.componentImage s)) : False := by
  let := s.quasisimple
  have hz := center_bot_of_two s
    (Triality.InnerDisplacement.PrimeToTwoCovers.center_isTwoGroup f hf
      (hm.of_mulEquiv (SecondaryActionData.sieveCentralQuotientEquiv s)))
  exact SecondaryActionData.not_triality s D h hn hf (hm.of_mulEquiv (fullInnerEquiv s hz))

/-- The Ree odd-primary cover theorem supplies the literal full-quotient marking. -/
theorem SecondaryActionData.not_ree_inner (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n) {m : ℕ} (hm : 1≤m)
    (e : SecondaryActionData.componentImage s ≃* ReeF4.Model m) : False := by
  let := s.quasisimple
  have hz := center_bot_of_two s
    (ReeF4.CentralCovers.OddPrimary.center_isPGroup_of_quotient_equiv m hm
      ((SecondaryActionData.sieveCentralQuotientEquiv s).trans e))
  let d := ReeF4.canonicalLocalBlockInput m
  exact SecondaryActionData.not_ree s D h hn hz hm
    ⟨d,⟨((fullInnerEquiv s hz).trans e).trans d.modelEquiv.symm⟩⟩

private theorem split_of_odd_binary_prime {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ho : Odd n) (hd : p ∣ 2^n-1)
    (hcard : p ∣ (2^f)^4 * ((2^f)^2-1) * ((2^f)^4-1)) : p ∣ 2^f-1 := by
  have cast_eq {a : ℕ} : (2 : ZMod p)^a=1 ↔ p ∣ 2^a-1 := by
    have hpos : 1 ≤ 2^a := Nat.one_le_pow _ _ (by decide)
    have he : (2 : ZMod p)^a-1 = ((2^a-1 : ℕ) : ZMod p) := by
      rw [Nat.cast_sub hpos,Nat.cast_pow]
      norm_num
    rw [←sub_eq_zero,he,ZMod.natCast_eq_zero_iff]
  have hnot : ¬p ∣ (2^f)^4 := fun hh => hp2
    ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow hh)))
  have hd4 : p ∣ (2^f)^4-1 := by
    rcases hp.dvd_mul.mp hcard with hh | hh
    · rcases hp.dvd_mul.mp hh with hh | hh
      · exact (hnot hh).elim
      · exact hh.trans (Nat.pow_sub_one_dvd_pow_sub_one (2^f) (by decide : 2 ∣ 4))
    · exact hh
  have hnorder : orderOf (2 : ZMod p) ∣ n := orderOf_dvd_of_pow_eq_one (cast_eq.mpr hd)
  have hforder : orderOf (2 : ZMod p) ∣ 4*f := by
    apply orderOf_dvd_of_pow_eq_one
    apply cast_eq.mpr
    simpa only [←pow_mul,Nat.mul_comm f 4] using hd4
  have hc : Nat.Coprime (orderOf (2 : ZMod p)) 4 :=
    (ho.of_dvd_nat hnorder).coprime_two_right.pow_right 2
  exact cast_eq.mp (orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_of_dvd_mul_left hforder))

/-- Every symplectic four-space row is excluded in both source-degree parities. -/
theorem SecondaryActionData.not_symplectic_inner (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n) {f : ℕ} (hf : 2≤f)
    (hm : ClassicalGroup.IsPSp (SecondaryActionData.componentImage s) 2 (2^f)) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := s.quasisimple
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let a := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
  obtain ⟨b,_⟩ := Theory.SpecificGroups.SymplecticFour.CentralCovers.Even.exists_whole_model
    hF (by omega : 1<f) ((SecondaryActionData.sieveCentralQuotientEquiv s).trans a)
  have hmfull : ClassicalGroup.IsPSp (s.component ⧸ pCore 2 s.component) 2 (2^f) :=
    ⟨F,inferInstance,inferInstance,hF,
      ⟨b.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv⟩⟩
  rcases Nat.even_or_odd n with he | ho
  · exact SecondaryActionData.not_symplectic_of_three_dvd s D h
      ((Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr he) hf hmfull
  · have htwo : 4 ≤ 2^n := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega : 2≤n)
    obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (by omega : 2^n-1≠1)
    have hop := Nat.BinarySignedTorus.odd_of_dvd_sub (by omega : 0<n) hd
    have hp2 : p≠2 := by
      rintro rfl
      exact hop.not_two_dvd_nat (dvd_refl 2)
    have hdiv : p ∣ Nat.card (SecondaryActionData.componentImage s) := by
      apply dvd_trans _ (SecondaryActionData.secondary_order_dvd_inner s)
      apply dvd_mul_of_dvd_right
      exact hd.trans (by simpa only [pow_one] using
        Nat.pow_sub_one_dvd_pow_sub_one (2^n) (by decide : 1 ∣ 2))
    rw [Nat.card_congr a.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,hF] at hdiv
    exact SecondaryActionData.not_symplectic_of_common_prime s D h hp hop
      (by omega : 1<f) hd (split_of_odd_binary_prime hp hp2 ho hd hdiv) hmfull

/-- The binary symplectic derived group is the already excluded actual A₆ carrier. -/
theorem SecondaryActionData.not_small_symplectic_inner (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n)
    (e : SecondaryActionData.componentImage s ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) : False :=
  SecondaryActionData.not_alternating_inner s hn D h (by decide : 6≤8)
    (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)

/-- The binary G₂ derived group is the already excluded actual PSU₃(3) carrier. -/
theorem SecondaryActionData.not_small_g2_inner (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n) (hg : SecondaryActionData.ActionGeneration s)
    (e : SecondaryActionData.componentImage s ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  apply SecondaryActionData.not_odd_ternary_inner_of_generation s hn hg D h
    (by decide : Nat.Prime 3) (by decide : Odd 3)
  apply Or.inr
  refine ⟨FiniteField.Nine,inferInstance,inferInstance,
    Atlas.G2.BinaryResidualCover.unitaryForm,FiniteField.Nine.natCard,?_,
    ⟨e.trans Atlas.G2.BinaryResidualCover.unitaryEquiv.symm⟩⟩
  exact FiniteField.Nine.star_eq_cube

/-- The Tits order forces the cubic source case, contrary to its actual three-rank. -/
theorem SecondaryActionData.not_tits_inner (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n) (e : SecondaryActionData.componentImage s ≃* Tits.ParrottGroup) : False := by
  have hd := SecondaryActionData.secondary_order_dvd_inner s
  rw [Nat.card_congr e.toEquiv,Tits.parrottGroup_card] at hd
  have hn12 : n<12 := by
    by_contra! hh
    have htwo := (Nat.pow_dvd_pow 2 hh).trans ((dvd_mul_right _ _).trans hd)
    norm_num at htwo
  have hn2 : n=2 := by
    interval_cases n <;> first | rfl | norm_num at hd
  have h3 : 3∣2^n-1 := by rw [hn2]; decide
  have hz := SecondaryActionData.componentQuotient_center_eq_bot_of_three_dvd s D h h3
  let a := (fullInnerEquiv s hz).trans e
  have hu := SecondaryActionData.component_primeRank_eq_one_of_small_rank_two s D h
    Nat.prime_three (by decide) h3 (Or.inr (Or.inr ⟨a⟩))
  have hl : 2≤primeRank 3 s.component := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup,
      primeRank_congr 3 (a.trans Tits.parrottFiniteImageEquiv)]
    exact Tits.ThreeRank.rank_two_le
  omega

/-- The smallest binary linear row has no original nonbinary PSL₂ section. -/
theorem SecondaryActionData.not_binary_three_two_inner (s : SecondaryActionData c n)
    (hn : 1<n)
    (hm : ClassicalGroup.IsPSL (SecondaryActionData.componentImage s) 3 2) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hd := SecondaryActionData.secondary_order_dvd_inner s
  rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF] at hd
  norm_num at hd
  have hn4 : n<4 := by
    by_contra! hh
    have htwo := (Nat.pow_dvd_pow 2 hh).trans ((dvd_mul_right _ _).trans hd)
    norm_num at htwo
  interval_cases n <;> norm_num at hd

/-- The existing cubic exclusion applies to a G₂ inner marking in even
source degree, since the source theorem then makes the full center trivial. -/
theorem SecondaryActionData.g2_inner_source_degree_odd (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {f : ℕ} (hf : 2≤f)
    (hm : ClassificationModels.IsG2At (SecondaryActionData.componentImage s) (2^f)) : Odd n := by
  rcases Nat.even_or_odd n with he | ho
  · have hd := (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr he
    have hz := SecondaryActionData.componentQuotient_center_eq_bot_of_three_dvd s D h hd
    exact (SecondaryActionData.not_g2_of_three_dvd s D h hd hf
      (hm.of_mulEquiv (fullInnerEquiv s hz))).elim
  · exact ho

/-- All remaining binary rows are PSL₃ or G₂ over fields larger than two. -/
theorem SecondaryActionData.inspection_remaining_rows_after_rank_two
    (s : SecondaryActionData c n) (hn : 1<n) (hg : SecondaryActionData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (∃ f : ℕ, 2≤f ∧ ClassicalGroup.IsPSL (SecondaryActionData.componentImage s) 3 (2^f)) ∨
      (Odd n ∧ ∃ f : ℕ, 2≤f ∧ ClassificationModels.IsG2At (SecondaryActionData.componentImage s) (2^f)) ∨
      (n=5 ∧ Nonempty (SecondaryActionData.componentImage s ≃* Janko4.Model)) := by
  rcases SecondaryActionData.inspection_remaining_rows_after_odd_ternary s hn hg D h with
    ⟨f,hm⟩ | hm
  · cases hm with
    | linear hf hm =>
      by_cases hf1 : f=1
      · exact (SecondaryActionData.not_binary_three_two_inner s hn (by simpa [hf1] using hm)).elim
      · exact Or.inl ⟨f,by omega,hm⟩
    | symplectic hf hm => exact (SecondaryActionData.not_symplectic_inner s D h hn hf hm).elim
    | g2 hf hm => exact Or.inr (Or.inl
        ⟨SecondaryActionData.g2_inner_source_degree_odd s D h hf hm,f,hf,hm⟩)
    | triality hf hm => exact (SecondaryActionData.not_triality_inner s D h hn hf hm).elim
    | ree_f4 m hm _ he => exact (SecondaryActionData.not_ree_inner s D h hn hm he.some).elim
    | symplectic_derived _ he => exact (SecondaryActionData.not_small_symplectic_inner s D h hn he.some).elim
    | g2_derived _ he => exact (SecondaryActionData.not_small_g2_inner s D h hn hg he.some).elim
    | tits _ he => exact (SecondaryActionData.not_tits_inner s D h hn he.some).elim
  · exact Or.inr (Or.inr hm)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
