module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveModelsFieldActors
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveExclusionsUnitary
public import Theory.SpecificGroups.SU3.OddPrimeDiagonal

/-!
# The cubic diagonal-action branch of the nonblock sieve

The actual perfect secondary image normalizes the nontrivial moved radical
image. The binary unitary normalizer calculation excludes SU₃ and PSU₃ in
any field degree above one, without equating that degree to the source n.
Thus the cubic rank-two catalogue reduces to binary or odd-prime PSL₃ and
odd-prime PSU₃. The linear field-actor exclusion and the prime-field unitary
square calculation make every original order-three torus actor diagonal
outer. Every marking is an isomorphism of the full two-core quotient.

This proves the cubic branch of 4.3.12(2) under the literal SecondaryData
hypotheses. The noncubic triality/Ree rank exclusions and the LocalImageData
inspection yielding SourceAlternatives remain separate unproved steps of
the same sieve task. No source-model or diagonal-action callback is assumed.
Source: Aschbacher–Smith A.3.18, printed pp.51–53; original 4.3.12(2),
4.3.14–16, printed pp.617–619.
-/

public section
noncomputable section
open Subgroup Matrix BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The literal moved radical excludes both binary unitary carriers in every degree above one, independently of the source degree. -/
theorem SecondaryData.not_binary_unitary_model (s : SecondaryData c n)
    {f : ℕ} (hf : 1 < f) :
    ¬ (Chapter1.Section02.LocalModels.IsSU (s.component ⧸ pCore 2 s.component) 3 (2^f) ∨
      ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 (2^f)) := by
  let := SecondaryData.secondaryImage_perfect s
  let := s.quasisimple
  have hi : SecondaryData.secondaryImage s ≤ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) := by
    rw [show SecondaryData.secondaryImage s = (SecondaryData.secondaryProjection s).range.map MulAut.conj from
      SecondaryData.secondary_action_image s]
    exact map_le_range _ _
  intro hm
  apply (SecondaryData.radicalImage_two s).2
  rcases hm with hm | hm
  · exact special_unitary_moved_twoGroup_eq_bot hf hm _
      (SecondaryData.secondaryImage_ne_bot s) hi _ _ (SecondaryData.radicalImage_two s).1
      (SecondaryData.image_normalization s).1 (SecondaryData.radicalImage_moved s)
  · exact unitary_moved_twoGroup_eq_bot hf hm _
      (SecondaryData.secondaryImage_ne_bot s) hi _ _ (SecondaryData.radicalImage_two s).1
      (SecondaryData.image_normalization s).1 (SecondaryData.radicalImage_moved s)

/-- Cubic rank two leaves linear models and odd-prime unitary models on the full quotient. -/
theorem SecondaryData.cubic_rank_two_linear_or_odd_unitary (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2^n-1) (hr : 2 ≤ primeRank 3 s.component) :
    ((∃ r : ℕ, r.Prime ∧ Odd r ∧
      (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 r ∨
        ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 r)) ∨
      (∃ f : ℕ, 2 ≤ f ∧ Even f ∧
        ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 (2^f))) := by
  rcases (SecondaryData.cubic_rank_two_ternary_models s D h hd hr).2 with
    hm | ⟨f,hf,_,hm⟩ | ⟨f,hf,he,hm,_⟩
  · exact Or.inl hm
  · exact (SecondaryData.not_binary_unitary_model s (by omega : 1<f) (Or.inr hm)).elim
  · exact Or.inr ⟨f,hf,he,hm⟩
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Theory.GroupTheory
open ChapterA.Section03.OddPrime.SourceModels
open Chapter1.Section02.LocalModels
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- A projective diagonal action with an actual matrix marking of the full group. -/
@[expose] def IsProjectiveDiagonalSign (U : Type*) [Group U] (unitary : Bool) (q : ℕ)
    (a : MulAut U) : Prop :=
  if unitary then
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (J : HermitianForm 3 F),
      Nat.card F=q^2 ∧ (∀ z, J.conj z=z^q) ∧
      ∃ e : U ≃* ProjectiveSpecialUnitaryMatrixGroup J,
        MulAut.congr e a ∈ J.unitaryConjHom.range
  else
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F=q ∧
      ∃ e : U ≃* PSL(3,F), MulAut.congr e a ∈ Matrix.PSL3.OuterSolvable.innerDiagonal F

/-- Every original cubic torus actor is diagonal outer on an actual odd-prime unitary marking. -/
theorem SecondaryData.odd_unitary_cubic_torus_diagonal (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2^n-1) (hrank : 2 ≤ primeRank 3 s.component)
    {r : ℕ} (hr : r.Prime) (ho : Odd r)
    (hm : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 r)
    (x : rootNormalizer c) (hxt : (x : G)∈s.torus) (hx : orderOf x=3) :
    IsProjectiveDiagonalSign (s.component ⧸ pCore 2 s.component) true r (s.action x) ∧
      s.action x ∉ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) := by
  let := s.quasisimple
  have hz := SecondaryData.componentQuotient_center_eq_bot_of_three_dvd s D h hd
  let : IsSimpleGroup (s.component ⧸ pCore 2 s.component) := by
    let : IsSimpleGroup ((s.component ⧸ pCore 2 s.component) ⧸ center
      (s.component ⧸ pCore 2 s.component)) := IsQuasisimple.simple
    exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  refine ⟨?_,SecondaryData.torus_prime_action_not_inner_of_rank_two s D h Nat.prime_three
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
theorem SecondaryData.cubic_rank_two_signed_diagonal_actions (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2^n-1) (hrank : 2 ≤ primeRank 3 s.component) :
    ∃ (unitary : Bool) (q : ℕ), SignedCongruence unitary q ∧
      IsPSLSign (s.component ⧸ pCore 2 s.component) unitary 3 q ∧
      ∀ x : rootNormalizer c, (x : G)∈s.torus → orderOf x=3 →
        IsProjectiveDiagonalSign (s.component ⧸ pCore 2 s.component) unitary q (s.action x) ∧
          s.action x ∉ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) := by
  have hout := SecondaryData.torus_prime_action_not_inner_of_rank_two s D h Nat.prime_three
    (by decide) hd hrank
  rcases SecondaryData.cubic_rank_two_linear_or_odd_unitary s D h hd hrank with
    ⟨r,hr,ho,hm | hm⟩ | ⟨f,hf,he,hm⟩
  · refine ⟨false,r,SecondaryData.odd_linear_cubic_congruence s D h hd hrank hr ho hm,hm,?_⟩
    intro x hxt hx
    refine ⟨?_,hout x hxt hx⟩
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact ⟨F,inferInstance,inferInstance,hF,e,
      (SecondaryData.odd_linear_cubic_torus_diagonal s D h hd hrank hr ho hF e x hxt hx).1⟩
  · refine ⟨true,r,SecondaryData.odd_unitary_cubic_congruence s D h hd hrank hr ho hm,hm,?_⟩
    exact SecondaryData.odd_unitary_cubic_torus_diagonal s D h hd hrank hr ho hm
  · have hc : SignedCongruence false (2^f) := by
      change 2^f % 3=1
      rw [Nat.BinaryTorusParity.two_pow_mod_three,Nat.even_iff.mp he]
      rfl
    refine ⟨false,2^f,hc,hm,?_⟩
    intro x hxt hx
    refine ⟨?_,hout x hxt hx⟩
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact ⟨F,inferInstance,inferInstance,hF,e,
      (SecondaryData.binary_linear_cubic_torus_diagonal s D h hd hrank (by omega) hF e x hxt hx).1⟩

/-- Cauchy supplies the literal order-three subgroup generator required by original 4.3.12(2). -/
theorem SecondaryData.cubic_rank_two_diagonal_actor (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2^n-1) (hrank : 2 ≤ primeRank 3 s.component) :
    ∃ (unitary : Bool) (q : ℕ), SignedCongruence unitary q ∧
      IsPSLSign (s.component ⧸ pCore 2 s.component) unitary 3 q ∧
      ∃ x : rootNormalizer c, (x : G)∈s.torus ∧ orderOf x=3 ∧
        IsProjectiveDiagonalSign (s.component ⧸ pCore 2 s.component) unitary q (s.action x) ∧
          s.action x ∉ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) := by
  obtain ⟨u,q,hq,hm,ha⟩ := SecondaryData.cubic_rank_two_signed_diagonal_actions s D h hd hrank
  obtain ⟨x,hxt,hx,_⟩ := SecondaryData.exists_outside_prime_actor s Nat.prime_three hd
  exact ⟨u,q,hq,hm,x,hxt,hx,ha x hxt hx⟩
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
