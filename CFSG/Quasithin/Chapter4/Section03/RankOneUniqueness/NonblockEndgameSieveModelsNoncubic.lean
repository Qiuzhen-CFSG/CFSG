module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveModelsPrimeRemainder
public import Theory.SpecificGroups.PSL3.BinaryNoncubicComponents
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.SpecificGroups.Suzuki.OddSubgroups

/-!
# Noncubic torus primes in the full secondary component quotient

For a source torus prime p other than three, a binary PSL₃ central model
forces component rank one. Nonsplit Sylow subgroups are cyclic; in the
split case the fixed-field actor calculation absorbs all ambient p-elements
into the reduced component, contradicting the literal outside torus actor.
Coprimality of the covering center suffices, so this also excludes binary
SL₃ covers. For odd-prime ternary models the sixth-power inner automorphism
bound transfers through the center and excludes their special covers too.

The final dispatch applies these restrictions to the full quotient
K_Z/O₂(K_Z), retaining its actual center and model isomorphisms. It leaves
only the specified binary unitary, symplectic, G₂, triality and Ree models,
or a binary special-unitary three-cover, at noncubic rank two.

These are applications toward the prime-rank clause of original 4.3.12(2),
not the full source alternatives. The remaining model restrictions, cubic
diagonal action and 4.3.16 local inspection remain with
qt-d-1222-nonblock-endgame-sieve. The final contradiction owner is
qt-d-1222-rankone-uniqueness-nonblock, which supplies the source MSData and
SecondaryData.
Source: Aschbacher–Smith A.3.18, printed pp.51–53, and original 4.3.12(2),
printed p.617.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
noncomputable section
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Chapter1.Section02.LocalModels

private def centralQuotientEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ center A) ≃* B ⧸ center B :=
  QuotientGroup.congr _ _ e (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (centerCongr e ⟨y, hy⟩).property
    · intro hx
      exact ⟨e.symm x, (centerCongr e.symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- A binary projective central model forces rank one at a noncubic torus prime. -/
theorem SecondaryData.component_primeRank_eq_one_of_noncubic_binary_linear_central_model
    (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p f : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hp3 : p ≠ 3) (hf : 0 < f)
    (hm : ClassicalGroup.IsPSL
      ((s.component ⧸ pCore 2 s.component) ⧸ center (s.component ⧸ pCore 2 s.component))
      3 (2 ^ f)) : primeRank p s.component = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  rcases SecondaryData.component_primeRank_one_or_two s D h hp ho hd with hr | hr
  · exact hr
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  have hlarge : 3 < p := by have hh := hp.two_le; omega
  let a := SecondaryData.twoCoreComponentEquiv s
  have hz : Nat.Coprime p (Nat.card (center (SecondaryData.twoCoreComponent s))) := by
    rw [Nat.card_congr (centerCongr a).toEquiv]
    exact SecondaryData.componentQuotient_center_coprime_of_torus_prime s D h hp ho hd
  have hrI : 2 ≤ primeRank p (SecondaryData.twoCoreComponent s) := by
    rw [primeRank_congr p a,
      primeRank_quotient_eq_of_isTwoGroup p ho _ pCore_isPGroup, hr]
  have he := Matrix.PSL3.binary_noncubic_component_eq_primeClosure_and_residual
    (SecondaryData.twoCoreComponent_isComponent s) hp hlarge hf hF hz hrI
    ((SecondaryData.twoCoreRoot_sqtk s D h).stronglyQuasithin p hp ho)
    ((centralQuotientEquiv a).trans e)
  exact ((SecondaryData.twoCoreComponent_ne_prime_closures s hp ho hd).2 he.2).elim

/-- The full binary projective quotient satisfies the noncubic rank restriction. -/
theorem SecondaryData.component_primeRank_eq_one_of_noncubic_binary_linear
    (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p f : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hp3 : p ≠ 3) (hf : 0 < f)
    (hm : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 (2 ^ f)) :
    primeRank p s.component = 1 := by
  apply SecondaryData.component_primeRank_eq_one_of_noncubic_binary_linear_central_model
    s D h hp ho hd hp3 hf
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let a := ((QuotientGroup.quotientMulEquivOfEq
    (Group.IsPerfect.center_quotient_center_eq_bot SL(3,F))).trans QuotientGroup.quotientBot)
  exact ⟨F, inferInstance, inferInstance, hF, ⟨(centralQuotientEquiv e).trans a⟩⟩

/-- The restriction also holds for the full special-linear covering quotient. -/
theorem SecondaryData.component_primeRank_eq_one_of_noncubic_binary_special_linear
    (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p f : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hp3 : p ≠ 3) (hf : 0 < f)
    (hm : IsSL (s.component ⧸ pCore 2 s.component) 3 (2 ^ f)) :
    primeRank p s.component = 1 := by
  apply SecondaryData.component_primeRank_eq_one_of_noncubic_binary_linear_central_model
    s D h hp ho hd hp3 hf
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  exact ⟨F, inferInstance, inferInstance, hF, ⟨centralQuotientEquiv e⟩⟩

private theorem coprime_six {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3) :
    Nat.Coprime p 6 := by
  have h2 : Nat.Coprime p 2 := Nat.coprime_two_right.mpr ho
  have h3 : Nat.Coprime p 3 := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    exact hp3 ((Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_left hp.ne_one))
  exact h2.mul_right h3

/-- The sixth-power outer bound excludes rank two for odd-prime central models. -/
theorem SecondaryData.component_primeRank_eq_one_of_noncubic_odd_ternary_central_model
    (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p r : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) (hp3 : p ≠ 3)
    (hr : r.Prime) (hro : Odd r)
    (hm : ClassicalGroup.IsPSL
        ((s.component ⧸ pCore 2 s.component) ⧸ center (s.component ⧸ pCore 2 s.component)) 3 r ∨
      ClassicalGroup.IsPSU
        ((s.component ⧸ pCore 2 s.component) ⧸ center (s.component ⧸ pCore 2 s.component)) 3 r) :
    primeRank p s.component = 1 := by
  let := s.quasisimple
  apply SecondaryData.component_primeRank_eq_one_of_inner_power s D h hp ho hd
    (SecondaryData.componentQuotient_center_coprime_of_torus_prime s D h hp ho hd)
    (coprime_six hp ho hp3)
  intro a
  rcases hm with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨F, _, _, J, hF, hc, ⟨e⟩⟩
  · let : IsSimpleGroup PSL(3,F) := e.isSimpleGroup_congr.mp IsQuasisimple.simple
    let : Group.IsPerfect PSL(3,F) := Group.IsPerfect.ofSurjective
      (f := e.toMonoidHom.comp (QuotientGroup.mk' (center _)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
    have hh := Matrix.PSL3.odd_prime_sixth_power_inner
      (Group.IsPerfect.not_isSolvable PSL(3,F)) hr hro hF (MulAut.centralQuotientAction e a)
    rw [← map_pow] at hh
    obtain ⟨b, hb⟩ := hh
    obtain ⟨x, hx⟩ := (MulAut.centralQuotientAction_inner_iff e (a ^ 6)).mp ⟨b, hb.symm⟩
    exact ⟨x, hx.symm⟩
  · let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      e.isSimpleGroup_congr.mp IsQuasisimple.simple
    have hh := J.odd_prime_sixth_power_inner hr hro hF hc (MulAut.centralQuotientAction e a)
    rw [← map_pow] at hh
    obtain ⟨b, hb⟩ := hh
    obtain ⟨x, hx⟩ := (MulAut.centralQuotientAction_inner_iff e (a ^ 6)).mp ⟨b, hb.symm⟩
    exact ⟨x, hx.symm⟩

/-- Both odd-prime special ternary covers have rank one at noncubic torus primes. -/
theorem SecondaryData.component_primeRank_eq_one_of_noncubic_odd_special_ternary
    (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p r : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) (hp3 : p ≠ 3)
    (hr : r.Prime) (hro : Odd r) {unitary : Bool}
    (hm : IsSLSign (s.component ⧸ pCore 2 s.component) unitary 3 r) :
    primeRank p s.component = 1 := by
  apply SecondaryData.component_primeRank_eq_one_of_noncubic_odd_ternary_central_model
    s D h hp ho hd hp3 hr hro
  cases unitary with
  | false =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    exact Or.inl ⟨F, inferInstance, inferInstance, hF, ⟨centralQuotientEquiv e⟩⟩
  | true =>
    obtain ⟨F, _, _, J, hF, hc, ⟨e⟩⟩ := hm
    let : Fact r.Prime := ⟨hr⟩
    have hfixed : Nat.card {x : F // J.conj x = x} = r := by
      simpa only [pow_one] using
        FiniteField.card_fixed_of_quadratic_frobenius J.conj r 1 (by decide)
          (by simpa only [pow_one] using hF) (by simpa only [pow_one] using hc)
    have hlarge : 2 < r := by
      have hn : r ≠ 2 := by rintro rfl; norm_num at hro
      have ht := hr.two_le
      omega
    let := J.projective_isPerfect_of_fixed_card hlarge hF hfixed
    let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      BenderSuzuki.External.huppert_II_10_13 J r hlarge hF hfixed
    have hz : center (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
      rcases (inferInstance : (center
        (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)).Normal).eq_bot_or_eq_top
        with hb | ht
      · exact hb
      · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht)).elim
    let a := (QuotientGroup.quotientMulEquivOfEq
      (J.specialToProjective_ker_eq_center hz).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective J.specialToProjective_surjective)
    exact Or.inr ⟨F, inferInstance, inferInstance, J, hF, hc,
      ⟨(centralQuotientEquiv e).trans a⟩⟩

/-- Away from three, rank two leaves only the unitary, symplectic, G₂,
triality and Ree binary families, or a binary special-unitary three-cover. -/
theorem SecondaryData.noncubic_rank_two_refined_models (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) (hp3 : p ≠ 3)
    (hr : 2 ≤ primeRank p s.component) :
    (center (s.component ⧸ pCore 2 s.component) = ⊥ ∧
      ((∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 (2 ^ f)) ∨
        (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp (s.component ⧸ pCore 2 s.component) 2 (2 ^ f)) ∨
        (∃ f : ℕ, 2 ≤ f ∧ ClassificationModels.IsG2At (s.component ⧸ pCore 2 s.component) (2 ^ f)) ∨
        (∃ f : ℕ, 1 ≤ f ∧ Triality.Standard.IsTrialityGroupAt (2 ^ f)
          (s.component ⧸ pCore 2 s.component)) ∨
        (∃ m : ℕ, 1 ≤ m ∧ IsReeF4At (s.component ⧸ pCore 2 s.component) m))) ∨
    (Nat.card (center (s.component ⧸ pCore 2 s.component)) = 3 ∧
      ∃ f : ℕ, 1 ≤ f ∧ Odd f ∧ IsSU (s.component ⧸ pCore 2 s.component) 3 (2 ^ f)) := by
  let : Fact p.Prime := ⟨hp⟩
  rcases SecondaryData.noncubic_rank_two_models s D h hp ho hd hp3 hr with
    ⟨hz, _, hm | hm⟩ | ⟨hz, unitary, q, hq, hm⟩
  · refine Or.inl ⟨hz, ?_⟩
    cases hm with
    | linear f hf hm =>
      have hb := odd_primeRank_le_one hm ho
      omega
    | unitary f hf hm => exact Or.inl ⟨f, hf, hm⟩
    | suzuki m hm he =>
      obtain ⟨e⟩ := he
      let : Fact p.Prime := ⟨hp⟩
      let P : Sylow p (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := default
      have hb := P.primeRank_le_one_of_isCyclic
        (BenderSuzuki.MatrixGroups.suzukiSylow_isCyclic_of_ne_two (by omega : 0 < m)
          (by rintro rfl; norm_num at ho) P)
      rw [← primeRank_congr p e,
        primeRank_quotient_eq_of_isTwoGroup p ho _ pCore_isPGroup] at hb
      omega
  · refine Or.inl ⟨hz, ?_⟩
    cases hm with
    | linear f hf hm =>
      have hr1 := SecondaryData.component_primeRank_eq_one_of_noncubic_binary_linear
        s D h hp ho hd hp3 (by omega) hm
      omega
    | symplectic f hf hm => exact Or.inr (Or.inl ⟨f, hf, hm⟩)
    | g2 f hf hm => exact Or.inr (Or.inr (Or.inl ⟨f, hf, hm⟩))
    | triality f hf hm => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, hm⟩)))
    | ree m hm he => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨m, hm, he⟩)))
    | symplectic_derived hm =>
      have hr1 := SecondaryData.component_primeRank_eq_one_of_small_rank_two
        s D h hp ho hd (Or.inl hm)
      omega
    | g2_derived hm =>
      have hr1 := SecondaryData.component_primeRank_eq_one_of_small_rank_two
        s D h hp ho hd (Or.inr (Or.inl hm))
      omega
    | tits hm =>
      have hr1 := SecondaryData.component_primeRank_eq_one_of_small_rank_two
        s D h hp ho hd (Or.inr (Or.inr hm))
      omega
  · rcases hq with ⟨f, hf, rfl, hmod⟩ | ⟨hqp, hqo⟩
    · cases unitary with
      | false =>
        have hr1 := SecondaryData.component_primeRank_eq_one_of_noncubic_binary_special_linear
          s D h hp ho hd hp3 (by omega) hm
        omega
      | true =>
        refine Or.inr ⟨hz, f, hf, ?_, hm⟩
        change 2 ^ f % 3 = 2 at hmod
        rw [Nat.BinaryTorusParity.two_pow_mod_three] at hmod
        split_ifs at hmod with he
        · contradiction
        · exact Nat.odd_iff.mpr (by omega)
    · have hr1 := SecondaryData.component_primeRank_eq_one_of_noncubic_odd_special_ternary
        s D h hp ho hd hp3 hqp hqo hm
      omega
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
