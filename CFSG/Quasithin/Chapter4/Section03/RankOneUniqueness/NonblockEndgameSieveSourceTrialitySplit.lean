module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceOddFieldActions
public import Theory.SpecificGroups.Triality.SplitPrimeFieldActors

/-!
# Split triality primes in the corrected source sieve

The actual binary triality torus has rank two at every split prime. The
original source torus therefore supplies an outer actor of that prime order
on the literal component quotient, in an action image of rank at most two.
The coefficient representative retained in the same image fixes a torus
square and forces rank three, excluding the model at any common split prime.
Consequently the source degree and the triality base degree are coprime.

The resulting noncubic rank-two frontier retains only nonsplit triality
primes in odd source degree. It does not assert their fixed-rank exclusion
or the subsequent proper two-local inspection. All full-quotient markings,
small fields and corrected source-record conventions are preserved.

Source: Aschbacher--Smith A.3.18, printed pp.51--53, and 4.3.12(2), p.617.
-/

public section
open Subgroup Theory.GroupTheory
noncomputable section
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- A prime common to the original torus and the split triality torus is
impossible: its coefficient representative fixes an elementary square in the
same transported normal-quotient action image. -/
theorem SecondarySourceData.not_triality_of_split_prime (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p f : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2^n-1)
    (hf : 0<f) (hsplit : p ∣ 2^f-1) :
    ¬ Triality.Standard.IsTrialityGroupAt (2^f) (s.component ⧸ pCore 2 s.component) := by
  intro hm
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ f hf).mp hm
  have hr : 2 ≤ primeRank p s.component := by
    rw [←primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 s.component) pCore_isPGroup,
      primeRank_congr p e]
    exact Triality.Standard.SplitPrimeFieldActors.split_prime_rank
      (Triality.Standard.binaryParameters f hf) rfl hsplit
  let := s.quasisimple
  let : IsQuasisimple (Triality.Standard.BinaryCarrier f hf) := IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup (Triality.Standard.BinaryCarrier f hf) := by
    let : IsSimpleGroup (Triality.Standard.BinaryCarrier f hf ⧸
      center (Triality.Standard.BinaryCarrier f hf)) := IsQuasisimple.simple
    exact ((QuotientGroup.quotientMulEquivOfEq
      (Triality.Standard.binaryCarrier_center_eq_bot f hf)).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  obtain ⟨x,_,_,ha,hi,hinner,hbound⟩ :=
    SecondarySourceData.model_prime_actor_of_rank_two s D h hp ho hd hr e
  exact hi (Triality.Standard.SplitPrimeFieldActors.prime_actor_inner_of_split
    f hf hsplit _ hinner hbound _ ⟨x,rfl⟩ ha)

/-- Every actual triality marking has base degree coprime to the source degree.
A common divisor above one supplies a prime of both split tori, already
excluded on the literal quotient action. -/
theorem SecondarySourceData.triality_degrees_coprime (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n) {f : ℕ} (hf : 0<f)
    (hm : Triality.Standard.IsTrialityGroupAt (2^f) (s.component ⧸ pCore 2 s.component)) :
    Nat.Coprime n f := by
  change Nat.gcd n f=1
  by_contra he
  have hgpos : 0 < Nat.gcd n f := Nat.gcd_pos_of_pos_left f (by omega)
  have htwo : 4 ≤ 2^(Nat.gcd n f) :=
    (by norm_num : 4=2^2) ▸ Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (by omega : 2^(Nat.gcd n f)-1≠1)
  have hdn : p ∣ 2^n-1 := hd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (Nat.gcd_dvd_left n f))
  have hdf : p ∣ 2^f-1 := hd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (Nat.gcd_dvd_right n f))
  have hp2 : p≠2 := by
    rintro rfl
    have hh := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega : n≠0))
    have hh' := Nat.mod_eq_zero_of_dvd hdn
    have hpos : 0 < 2^n := pow_pos (by decide) n
    omega
  exact SecondarySourceData.not_triality_of_split_prime s D h hp (hp.odd_of_ne_two hp2)
    hdn hf hdf hm

/-- The remaining noncubic rank-two triality row has coprime source and base
degrees. Its original prime divides the base degree but is not split there. -/
theorem SecondarySourceData.noncubic_rank_two_triality_nonsplit
    (s : SecondarySourceData c n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1<n) {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2^n-1)
    (hp3 : p≠3) (hr : 2 ≤ primeRank p s.component) :
    Odd n ∧ center (s.component ⧸ pCore 2 s.component)=⊥ ∧
      ∃ f : ℕ, 1≤f ∧ p ∣ f ∧ Nat.Coprime n f ∧ ¬ p ∣ 2^f-1 ∧
        Triality.Standard.IsTrialityGroupAt (2^f) (s.component ⧸ pCore 2 s.component) := by
  obtain ⟨hodd,hz,f,hf,hpf,hm⟩ :=
    SecondarySourceData.noncubic_rank_two_triality s D h hn hp ho hd hp3 hr
  exact ⟨hodd,hz,f,hf,hpf,SecondarySourceData.triality_degrees_coprime s D h hn hf hm,
    fun hs => SecondarySourceData.not_triality_of_split_prime s D h hp ho hd hf hs hm,hm⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
