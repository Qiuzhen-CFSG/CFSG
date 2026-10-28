module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveModelsNoncubicLie
public import Theory.SpecificGroups.SU3.NoncubicFieldActors

/-!
This additive source variant uses `SecondaryActionData` and preserves the
full quotient and central-cover hypotheses without universal radical movement.

# Unitary restrictions at noncubic source torus primes

Apply the concrete PSU₃ field-actor calculation to the actual ordinary
component of the two-core quotient. Its center is prime to the source torus
prime. Rank two would make it equal the prime-to-p residual, contradicting
the source's literal outside order-p torus element. The canonical central
quotient of SU₃ gives the same argument for the full special-unitary cover.
The small SU₃(2) endpoint is handled directly by its noncubic prime rank.

Thus the full secondary component quotient has rank one at every noncubic
torus prime in both binary unitary rows. The refined rank-two dispatch
retains only center-free triality and Ree models, with their original
parameter ranges. This discharges the unitary branches of 4.3.12(2).
The remaining two rows, cubic diagonal clause and LocalImageData inspection
remain with qt-d-1222-nonblock-endgame-sieve; this is not SourceAlternatives.
MSData and SecondaryActionData remain inputs of the final contradiction owner,
qt-d-1222-rankone-uniqueness-nonblock.

Source: Aschbacher–Smith A.3.18, printed pp.51–53, and original
4.3.12–16, printed pp.617–618.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
noncomputable section
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Chapter1.Section02.LocalModels

private def unitaryCentralQuotientEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ center A) ≃* B ⧸ center B :=
  QuotientGroup.congr _ _ e (by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (centerCongr e ⟨y,hy⟩).property
    · intro hx
      exact ⟨e.symm x,(centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The full source component has rank one at noncubic torus primes with binary PSU₃ central model. -/
theorem SecondaryActionData.component_primeRank_eq_one_of_noncubic_binary_unitary_central_model
    (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p f : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2^n-1)
    (hp3 : p ≠ 3) (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSU
      ((s.component ⧸ pCore 2 s.component) ⧸ center (s.component ⧸ pCore 2 s.component))
      3 (2^f)) : primeRank p s.component = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  rcases SecondaryActionData.component_primeRank_one_or_two s D h hp ho hd with hr | hr
  · exact hr
  obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  have hlarge : 3 < p := by have hh := hp.two_le; omega
  let a := SecondaryActionData.twoCoreComponentEquiv s
  have hz : Nat.Coprime p (Nat.card (center (SecondaryActionData.twoCoreComponent s))) := by
    rw [Nat.card_congr (centerCongr a).toEquiv]
    exact SecondaryActionData.componentQuotient_center_coprime_of_torus_prime s D h hp ho hd
  have hrI : 2 ≤ primeRank p (SecondaryActionData.twoCoreComponent s) := by
    rw [primeRank_congr p a,primeRank_quotient_eq_of_isTwoGroup p ho _ pCore_isPGroup,hr]
  have he := HermitianForm.NoncubicFieldActors.component_eq_primeClosure_and_residual
    J hf hF hc (SecondaryActionData.twoCoreComponent_isComponent s) hlarge hz hrI
    ((SecondaryActionData.twoCoreRoot_sqtk s D h).stronglyQuasithin p hp ho)
    ((unitaryCentralQuotientEquiv a).trans e)
  exact ((SecondaryActionData.twoCoreComponent_ne_prime_closures s hp ho hd).2 he.2).elim

/-- The full projective quotient satisfies the noncubic unitary restriction. -/
theorem SecondaryActionData.component_primeRank_eq_one_of_noncubic_binary_unitary
    (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p f : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2^n-1)
    (hp3 : p ≠ 3) (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 (2^f)) :
    primeRank p s.component = 1 := by
  apply SecondaryActionData.component_primeRank_eq_one_of_noncubic_binary_unitary_central_model
    s D h hp ho hd hp3 hf
  obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
  let a := (QuotientGroup.quotientMulEquivOfEq
    (HermitianForm.EvenProjectiveComparison.center_eq_bot J (by omega) hF hc)).trans
      QuotientGroup.quotientBot
  exact ⟨F,inferInstance,inferInstance,J,hF,hc,⟨(unitaryCentralQuotientEquiv e).trans a⟩⟩

/-- The full special-unitary cover also has noncubic rank one, including the small-field endpoint. -/
theorem SecondaryActionData.component_primeRank_eq_one_of_noncubic_binary_special_unitary
    (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p f : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2^n-1)
    (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hm : IsSU (s.component ⧸ pCore 2 s.component) 3 (2^f)) :
    primeRank p s.component = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
  by_cases hlarge : 2 ≤ f
  · apply SecondaryActionData.component_primeRank_eq_one_of_noncubic_binary_unitary_central_model
      s D h hp ho hd hp3 hlarge
    have hz := HermitianForm.EvenProjectiveComparison.center_eq_bot J (by omega) hF hc
    let a := (QuotientGroup.quotientMulEquivOfEq (J.specialToProjective_ker_eq_center hz).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective J.specialToProjective_surjective)
    exact ⟨F,inferInstance,inferInstance,J,hF,hc,⟨(unitaryCentralQuotientEquiv e).trans a⟩⟩
  · have he : f=1 := by omega
    subst f
    rcases SecondaryActionData.component_primeRank_one_or_two s D h hp ho hd with hr | hr
    · exact hr
    have hp2 : p≠2 := by rintro rfl; norm_num at ho
    have hb := HermitianForm.NoncubicPrimeRank.special_rank_le_one J
      (by decide : 1 < 2) (by simpa only [pow_one] using hF)
      (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1 (by decide)
        (by simpa only [pow_one] using hF) (by simpa only [pow_one] using hc))
      ho hp3
      (by intro hd; exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd))
      (by intro hd; exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd))
    rw [←primeRank_congr p e,primeRank_quotient_eq_of_isTwoGroup p ho _ pCore_isPGroup,hr] at hb
    omega

/-- Noncubic rank two now retains only the center-free triality and Ree rows. -/
theorem SecondaryActionData.noncubic_rank_two_triality_or_ree (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2^n-1) (hp3 : p≠3)
    (hr : 2 ≤ primeRank p s.component) :
    center (s.component ⧸ pCore 2 s.component) = ⊥ ∧
      ((∃ f : ℕ, 1 ≤ f ∧ Triality.Standard.IsTrialityGroupAt (2^f)
        (s.component ⧸ pCore 2 s.component)) ∨
       (∃ m : ℕ, 1 ≤ m ∧ IsReeF4At (s.component ⧸ pCore 2 s.component) m)) := by
  rcases SecondaryActionData.noncubic_rank_two_remaining_models s D h hp ho hd hp3 hr with
    ⟨hz,hm | hm⟩ | ⟨_,f,hf,_,hm⟩
  · obtain ⟨f,hf,hm⟩ := hm
    have he := SecondaryActionData.component_primeRank_eq_one_of_noncubic_binary_unitary s D h hp ho hd hp3 hf hm
    omega
  · exact ⟨hz,hm⟩
  · have he := SecondaryActionData.component_primeRank_eq_one_of_noncubic_binary_special_unitary s D h hp ho hd hp3 hf hm
    omega
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
