module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveModelsFieldActors
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveCubicAction
public import Theory.SpecificGroups.SU3.OddPrimeDiagonal

/-!
# Cubic diagonal action on corrected source data

The checked model and full-rank actor calculations transfer to the corrected
record without radical movement. Binary-unitary exclusion uses the core
movement and the separately assumed whole-radical generation identity.
Every remaining cubic actor is diagonal outer on the actual full quotient.

This source version of 4.3.12(2)'s cubic branch retains generation explicitly.
The original source witness and generation producer, noncubic triality/Ree
exclusions, and four-row local inspection remain necessary for final assembly.
The legacy diagonal predicate is reused with its actual model isomorphisms.
Source: Aschbacher--Smith A.3.18, pp.51--53; 4.3.12--16, pp.617--618.
-/

public section
noncomputable section
open Subgroup Matrix BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- Core movement and explicit whole-radical generation exclude both binary
unitary carriers in every degree above one, independently of the source degree. -/
theorem SecondaryActionData.not_binary_unitary_model (s : SecondaryActionData c n)
    (hg : SecondaryActionData.ActionGeneration s) {f : ℕ} (hf : 1 < f) :
    ¬ (Chapter1.Section02.LocalModels.IsSU (s.component ⧸ pCore 2 s.component) 3 (2^f) ∨
      ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 (2^f)) := by
  let := s.normal
  let := s.quasisimple
  intro hm
  exact s.radical_action (SourceImages.unitary_radical_eq_bot c s.component hf hm s.torus
    s.secondary_le s.radical_le s.torus_le s.radical_normalizer
    (SourceImages.secondaryImage_ne_bot c s.component s.secondary_le s.secondary_model)
    s.core_moved hg)

/-- Cubic rank two leaves linear models and odd-prime unitary models on the full quotient. -/
theorem SecondaryActionData.cubic_rank_two_linear_or_odd_unitary (s : SecondaryActionData c n)
    (hg : SecondaryActionData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2^n-1) (hr : 2 ≤ primeRank 3 s.component) :
    ((∃ r : ℕ, r.Prime ∧ Odd r ∧
      (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 r ∨
        ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 r)) ∨
      (∃ f : ℕ, 2 ≤ f ∧ Even f ∧
        ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 (2^f))) := by
  rcases (SecondaryActionData.cubic_rank_two_ternary_models s D h hd hr).2 with
    hm | ⟨f,hf,_,hm⟩ | ⟨f,hf,he,hm,_⟩
  · exact Or.inl hm
  · exact (SecondaryActionData.not_binary_unitary_model s hg (by omega : 1<f) (Or.inr hm)).elim
  · exact Or.inr ⟨f,hf,he,hm⟩
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Theory.GroupTheory
open ChapterA.Section03.OddPrime.SourceModels
open Chapter1.Section02.LocalModels
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- Every original cubic torus actor is diagonal outer on an actual odd-prime unitary marking. -/
theorem SecondaryActionData.odd_unitary_cubic_torus_diagonal (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2^n-1) (hrank : 2 ≤ primeRank 3 s.component)
    {r : ℕ} (hr : r.Prime) (ho : Odd r)
    (hm : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 r)
    (x : rootNormalizer c) (hxt : (x : G)∈s.torus) (hx : orderOf x=3) :
    IsProjectiveDiagonalSign (s.component ⧸ pCore 2 s.component) true r (s.action x) ∧
      s.action x ∉ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) := by
  let := s.quasisimple
  have hz := SecondaryActionData.componentQuotient_center_eq_bot_of_three_dvd s D h hd
  let : IsSimpleGroup (s.component ⧸ pCore 2 s.component) := by
    let : IsSimpleGroup ((s.component ⧸ pCore 2 s.component) ⧸ center
      (s.component ⧸ pCore 2 s.component)) := IsQuasisimple.simple
    exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  refine ⟨?_,SecondaryActionData.torus_prime_action_not_inner_of_rank_two s D h Nat.prime_three
    (by decide) hd hrank x hxt hx⟩
  obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
  let : Fact r.Prime := ⟨hr⟩
  have hfixed : Nat.card {z : F // J.conj z=z} = r := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius J.conj r 1
      (by decide) (by simpa only [pow_one] using hF) (by simpa only [pow_one] using hc)
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨b⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J r hF hfixed
  let e₀ := e.trans b
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J₀) := e₀.isSimpleGroup_congr.mp inferInstance
  refine ⟨F,inferInstance,inferInstance,J₀,hF,hc,e₀,?_⟩
  apply J₀.cubic_mem_unitary_of_odd_prime rfl hr ho hF hfixed
  rw [←map_pow,←map_pow,show x^3=1 from hx ▸ pow_orderOf_eq_one x,map_one,map_one]

/-- The cubic branch of original 4.3.12(2), with a signed full quotient model and diagonal outer action for every order-three torus element. -/
theorem SecondaryActionData.cubic_rank_two_signed_diagonal_actions (s : SecondaryActionData c n)
    (hg : SecondaryActionData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2^n-1) (hrank : 2 ≤ primeRank 3 s.component) :
    ∃ (unitary : Bool) (q : ℕ), SignedCongruence unitary q ∧
      IsPSLSign (s.component ⧸ pCore 2 s.component) unitary 3 q ∧
      ∀ x : rootNormalizer c, (x : G)∈s.torus → orderOf x=3 →
        IsProjectiveDiagonalSign (s.component ⧸ pCore 2 s.component) unitary q (s.action x) ∧
          s.action x ∉ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) := by
  have hout := SecondaryActionData.torus_prime_action_not_inner_of_rank_two s D h Nat.prime_three
    (by decide) hd hrank
  rcases SecondaryActionData.cubic_rank_two_linear_or_odd_unitary s hg D h hd hrank with
    ⟨r,hr,ho,hm | hm⟩ | ⟨f,hf,he,hm⟩
  · refine ⟨false,r,SecondaryActionData.odd_linear_cubic_congruence s D h hd hrank hr ho hm,hm,?_⟩
    intro x hxt hx
    refine ⟨?_,hout x hxt hx⟩
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact ⟨F,inferInstance,inferInstance,hF,e,
      (SecondaryActionData.odd_linear_cubic_torus_diagonal s D h hd hrank hr ho hF e x hxt hx).1⟩
  · refine ⟨true,r,SecondaryActionData.odd_unitary_cubic_congruence s D h hd hrank hr ho hm,hm,?_⟩
    exact SecondaryActionData.odd_unitary_cubic_torus_diagonal s D h hd hrank hr ho hm
  · have hc : SignedCongruence false (2^f) := by
      change 2^f % 3=1
      rw [Nat.BinaryTorusParity.two_pow_mod_three,Nat.even_iff.mp he]
      rfl
    refine ⟨false,2^f,hc,hm,?_⟩
    intro x hxt hx
    refine ⟨?_,hout x hxt hx⟩
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact ⟨F,inferInstance,inferInstance,hF,e,
      (SecondaryActionData.binary_linear_cubic_torus_diagonal s D h hd hrank (by omega) hF e x hxt hx).1⟩

/-- Cauchy supplies the literal order-three subgroup generator required by original 4.3.12(2). -/
theorem SecondaryActionData.cubic_rank_two_diagonal_actor (s : SecondaryActionData c n)
    (hg : SecondaryActionData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2^n-1) (hrank : 2 ≤ primeRank 3 s.component) :
    ∃ (unitary : Bool) (q : ℕ), SignedCongruence unitary q ∧
      IsPSLSign (s.component ⧸ pCore 2 s.component) unitary 3 q ∧
      ∃ x : rootNormalizer c, (x : G)∈s.torus ∧ orderOf x=3 ∧
        IsProjectiveDiagonalSign (s.component ⧸ pCore 2 s.component) unitary q (s.action x) ∧
          s.action x ∉ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) := by
  obtain ⟨u,q,hq,hm,ha⟩ := SecondaryActionData.cubic_rank_two_signed_diagonal_actions s hg D h hd hrank
  obtain ⟨x,hxt,hx,_⟩ := SecondaryActionData.exists_outside_prime_actor s Nat.prime_three hd
  exact ⟨u,q,hq,hm,x,hxt,hx,ha x hxt hx⟩
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
