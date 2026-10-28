module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceTrialitySplit
public import Theory.SpecificGroups.Triality.OddDegreeFieldActors

/-!
# The nonsplit triality exclusion on the corrected source action

The previously proved split-prime exclusion makes the source and triality
degrees coprime. In odd source degree the genuine carrier order leaves seven
as the common prime. A fixed copy of the binary triality seven-plane forces
rank two in the component. The original normal-quotient action then supplies
an outer seven-actor in a rank-two action image, contradicting the proved
coefficient fixed-plane calculation in that same image.

Together with the cubic exclusion this eliminates triality in both parities.
The noncubic source primes consequently all have rank one, and the existing
cubic argument gives the full rank-or-diagonal-actor clause of 4.3.12(2).
Only that cubic argument needs the explicit whole-radical generation input.
The later proper two-local inspection of 4.3.16 remains a separate obligation.
No legacy radical-torus movement or replacement quotient is used.

Source: Aschbacher--Smith A.3.18, pp.51--53, and 4.3.12--16, pp.617--618.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Chapter1.Section02.LocalModels
open ChapterA.Section03.OddPrime.SourceModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

private theorem three_dvd_of_seven_dvd (hd : 7∣2^n-1) : 3∣n := by
  have hh := (ZMod.natCast_eq_zero_iff _ 7).mpr hd
  have hpos : 1 ≤ 2^n := Nat.one_le_pow _ _ (by decide)
  push_cast [Nat.cast_sub hpos] at hh
  have hh' := orderOf_dvd_of_pow_eq_one (sub_eq_zero.mp hh)
  have he : orderOf (2 : ZMod 7)=3 := by
    let : Fact (Nat.Prime 3) := ⟨by decide⟩
    exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  rwa [he] at hh'

/-- The nonsplit seven-actor exclusion uses the actual component action image. -/
theorem SecondarySourceData.not_triality_of_odd_degree (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n) (ho : Odd n) {f : ℕ} (hf : 0<f) :
    ¬ Triality.Standard.IsTrialityGroupAt (2^f) (s.component ⧸ pCore 2 s.component) := by
  intro hm
  have hc := SecondarySourceData.triality_degrees_coprime s D h hn hf hm
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ f hf).mp hm
  have htwo : 4 ≤ 2^n := (by norm_num : 4=2^2) ▸ Nat.pow_le_pow_right (by decide) hn
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (by omega : 2^n-1≠1)
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p≠2 := by
    rintro rfl
    have hh := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega : n≠0))
    have hh' := Nat.mod_eq_zero_of_dvd hd
    omega
  have hop : Odd p := hp.odd_of_ne_two hp2
  have hr : 1 ≤ primeRank p (Triality.Standard.BinaryCarrier f hf) := by
    rw [←primeRank_congr p e,primeRank_quotient_eq_of_isTwoGroup p hop _ pCore_isPGroup]
    rcases SecondarySourceData.component_primeRank_one_or_two s D h hp hop hd with hh | hh <;> omega
  have hcard : p ∣ Nat.card (Triality.Standard.BinaryCarrier f hf) := by
    by_contra hh
    have hh' := PrimeRank.eq_zero_iff_not_dvd_card.mpr hh
    omega
  have hp7 := Triality.Standard.OddDegreeFieldActors.prime_eq_seven hf hp hp2 ho hc hd hcard
  subst p
  have hn3 : 3∣n := three_dvd_of_seven_dvd hd
  have hf3 : ¬3∣f := by
    intro h3
    have he := Nat.dvd_gcd hn3 h3
    rw [hc.gcd_eq_one] at he
    norm_num at he
  have hr2 : 2 ≤ primeRank 7 s.component := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 7 (by decide) (pCore 2 s.component) pCore_isPGroup,
      primeRank_congr 7 e]
    obtain ⟨E,hE,hcard,_⟩ := Triality.Standard.OddDegreeFieldActors.exists_fixed_seven_plane
      f hf hf3 1 (one_pow 7)
    let := hE
    exact IsElementaryAbelian.primeRank_ge_of_card E hcard
  let := s.quasisimple
  let : IsQuasisimple (Triality.Standard.BinaryCarrier f hf) := IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup (Triality.Standard.BinaryCarrier f hf) := by
    let : IsSimpleGroup (Triality.Standard.BinaryCarrier f hf ⧸
      center (Triality.Standard.BinaryCarrier f hf)) := IsQuasisimple.simple
    exact ((QuotientGroup.quotientMulEquivOfEq
      (Triality.Standard.binaryCarrier_center_eq_bot f hf)).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  obtain ⟨x,_,_,ha,hi,hinner,hbound⟩ :=
    SecondarySourceData.model_prime_actor_of_rank_two s D h hp hop hd hr2 e
  exact hi (Triality.Standard.OddDegreeFieldActors.seven_actor_inner f hf hf3
    _ hinner hbound _ ⟨x,rfl⟩ ha)

/-- Both source-degree parities exclude the full genuine triality quotient. -/
theorem SecondarySourceData.not_triality (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n) {f : ℕ} (hf : 0<f) :
    ¬ Triality.Standard.IsTrialityGroupAt (2^f) (s.component ⧸ pCore 2 s.component) := by
  rcases Nat.even_or_odd n with he | ho
  · exact SecondarySourceData.not_triality_of_three_dvd s D h
      ((Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr he) hf
  · exact SecondarySourceData.not_triality_of_odd_degree s D h hn ho hf

/-- All noncubic source-torus primes have component rank one. -/
theorem SecondarySourceData.noncubic_prime_rank_one (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n) {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p∣2^n-1)
    (hp3 : p≠3) : primeRank p s.component=1 := by
  rcases SecondarySourceData.component_primeRank_one_or_two s D h hp ho hd with hr | hr
  · exact hr
  · obtain ⟨_,_,f,hf,_,hm⟩ := SecondarySourceData.noncubic_rank_two_triality s D h hn hp ho hd hp3 hr.ge
    exact (SecondarySourceData.not_triality s D h hn hf hm).elim

/-- The complete source prime restriction, with the diagonal actor on the
literal normal-quotient action and generation explicit only for the cubic row. -/
theorem SecondarySourceData.prime_rank_or_diagonal (s : SecondarySourceData c n)
    (hg : SecondarySourceData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n) {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p∣2^n-1) :
    primeRank p s.component=1 ∨
      (p=3 ∧ ∃ (unitary : Bool) (q : ℕ), SignedCongruence unitary q ∧
        IsPSLSign (s.component ⧸ pCore 2 s.component) unitary 3 q ∧
        ∃ x : rootNormalizer c, (x : G) ∈ s.torus ∧ orderOf x=3 ∧
          IsProjectiveDiagonalSign (s.component ⧸ pCore 2 s.component) unitary q (s.action x) ∧
          s.action x ∉ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component)) := by
  by_cases hp3 : p=3
  · subst p
    rcases SecondarySourceData.component_primeRank_one_or_two s D h hp ho hd with hr | hr
    · exact Or.inl hr
    · exact Or.inr ⟨rfl,SecondarySourceData.cubic_rank_two_diagonal_actor s hg D h hd hr.ge⟩
  · exact Or.inl (SecondarySourceData.noncubic_prime_rank_one s D h hn hp ho hd hp3)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
