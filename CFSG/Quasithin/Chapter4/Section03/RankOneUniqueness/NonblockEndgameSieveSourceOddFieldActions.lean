module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceFrontier
public import Theory.SpecificGroups.ReeF4.OddDegreeFieldActors
public import Theory.SpecificGroups.ReeF4.LocalPrimeRank

/-!
# Ree exclusion on the corrected secondary quotient action

In odd source degree, every source-torus prime dividing the actual Ree order
is a split prime. The concrete split torus has rank two, so the original
normal-quotient action supplies an outer prime actor and an action image of
rank at most two. Inner-field coverage extracts a field representative in
that same image. Its fixed split torus forces rank three, a contradiction.
The checked cubic argument already excludes even source degree.

Consequently the noncubic rank-two frontier consists only of genuine
triality quotients in odd source degree, with the same prime dividing their
base field degree. The triality field-action exclusion and the subsequent
proper two-local inspection remain to be proved. No radical-torus movement
or additional generation premise is used by this module.

Source: Aschbacher--Smith, A.3.18, printed pp.51--53, and 4.3.12(2), p.617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- In odd source degree, the original torus prime is split in every Ree marking.
The extracted field representative in the same action image then forces rank three. -/
theorem SecondarySourceData.not_ree_of_odd_degree (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n) (ho : Odd n) (hz : center (s.component ⧸ pCore 2 s.component)=⊥)
    {m : ℕ} (hm : 1≤m) : ¬ IsReeF4At (s.component ⧸ pCore 2 s.component) m := by
  rintro ⟨d,⟨e⟩⟩
  have htwo : 4 ≤ 2^n := (by norm_num : 4=2^2) ▸ Nat.pow_le_pow_right (by decide) hn
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (by omega : 2^n-1≠1)
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p≠2 := by
    rintro rfl
    have hh := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega : n≠0))
    have hh' := Nat.mod_eq_zero_of_dvd hd
    omega
  have hop : Odd p := hp.odd_of_ne_two hp2
  have hr : 1 ≤ primeRank p (ReeF4.Model m) := by
    rw [←primeRank_congr p (e.trans d.modelEquiv),
      primeRank_quotient_eq_of_isTwoGroup p hop _ pCore_isPGroup]
    rcases SecondarySourceData.component_primeRank_one_or_two s D h hp hop hd with hh | hh <;> omega
  have hcard : p ∣ Nat.card (ReeF4.Model m) := by
    by_contra hh
    have hh' := PrimeRank.eq_zero_iff_not_dvd_card.mpr hh
    omega
  have hsplit := ReeF4.OddDegreeFieldActors.split_of_odd_binary_prime hp2 ho hd hcard
  have hr2 : 2 ≤ primeRank p s.component := by
    rw [←primeRank_quotient_eq_of_isTwoGroup p hop (pCore 2 s.component) pCore_isPGroup,
      primeRank_congr p (e.trans d.modelEquiv)]
    exact ReeF4.LocalPrimeRank.split_prime_rank m hsplit
  let := s.quasisimple
  let : IsSimpleGroup (s.component ⧸ pCore 2 s.component) := by
    let : IsSimpleGroup ((s.component ⧸ pCore 2 s.component) ⧸
      center (s.component ⧸ pCore 2 s.component)) := IsQuasisimple.simple
    exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  let : IsSimpleGroup d.fixedGroup := e.isSimpleGroup_congr.mp inferInstance
  let : Group.IsPerfect d.fixedGroup := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  obtain ⟨x,hxt,hx,ha,hi,hinner,hbound⟩ :=
    SecondarySourceData.model_prime_actor_of_rank_two s D h hp hop hd hr2 e
  exact hi (ReeF4.OddDegreeFieldActors.prime_actor_inner_of_split hm d hsplit
    _ hinner hbound _ ⟨x,rfl⟩ ha)

/-- Both parities exclude the full Ree quotient, retaining its supplied matrix marking. -/
theorem SecondarySourceData.not_ree (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n) (hz : center (s.component ⧸ pCore 2 s.component)=⊥)
    {m : ℕ} (hm : 1≤m) : ¬ IsReeF4At (s.component ⧸ pCore 2 s.component) m := by
  rcases Nat.even_or_odd n with he | ho
  · exact SecondarySourceData.not_ree_of_three_dvd_of_center_bot s D h
      ((Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr he) hz hm
  · exact SecondarySourceData.not_ree_of_odd_degree s D h hn ho hz hm

/-- After the Ree field exclusion, noncubic rank two can only be triality, in
odd source degree, with a base field degree divisible by the same source prime. -/
theorem SecondarySourceData.noncubic_rank_two_triality (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n) {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2^n-1)
    (hp3 : p≠3) (hr : 2 ≤ primeRank p s.component) :
    Odd n ∧ center (s.component ⧸ pCore 2 s.component)=⊥ ∧
      ∃ f : ℕ, 1≤f ∧ p ∣ f ∧ Triality.Standard.IsTrialityGroupAt (2^f)
        (s.component ⧸ pCore 2 s.component) := by
  have hnodd : Odd n := by
    rcases Nat.even_or_odd n with he | he
    · have hh := SecondarySourceData.noncubic_rank_one_of_three_dvd s D h
        ((Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr he) hp ho hd hp3
      omega
    · exact he
  obtain ⟨hz,hmodels⟩ := SecondarySourceData.noncubic_rank_two_field_divisibility s D h hp ho hd hp3 hr
  refine ⟨hnodd,hz,?_⟩
  rcases hmodels with hh | ⟨m,hm,_,hm'⟩
  · exact hh
  · exact (SecondarySourceData.not_ree s D h hn hz hm hm').elim

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
