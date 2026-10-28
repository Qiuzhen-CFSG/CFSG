module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sieve.Source
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.Mathieu
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoTwo
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.Rudvalis
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Application
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.LinearGroups.G2.EvenThreeRank
public import Theory.SpecificGroups.Classical.EvenRankTwoOddRank
public import Theory.SpecificGroups.Triality.ElementaryNine
public import Theory.SpecificGroups.ReeF4.CubicRank

public import Theory.GroupAction.CoprimeInnerPower
public import Theory.SpecificGroups.PSL3.OddPrimeOuterExponent
public import Theory.SpecificGroups.SU3.OddPrimeOuterExponent

/-!
# Coprime actors in the remaining simple component rows

The remaining binary rank-two models have three-rank at least two.
For the sporadic rows the full outer automorphism group is a two-group;
for the odd-prime linear and unitary groups of degree three its exponent
divides six. A coprime actor of order prime to six is therefore inner and
then trivial. All model comparisons use actual group equivalences.

The literal component-quotient application is in `Sieve.Noncentral`.
This eliminates the simple rows retained by `Sieve.Source`; it does not
exclude the nonsimple A.3.6 alternatives. Their discharge and the final
11.5.6 assembly remain with qt-d-1222-natural-closure-cartan.
Source: Aschbacher--Smith A.3.6, pp.43--45, and 11.5.6(3), pp.780--781.
-/

@[expose] public noncomputable section
open scoped MatrixGroups
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open CFSG.Quasithin.ClassificationModels
open CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear

private theorem rank_two_threeRank {Q : Type*} [Group Q] [Finite Q]
    (hm : RankTwoTheoremC Q)
    (hn : ∀ n : ℕ, 1 ≤ n → ¬ ClassicalGroup.IsPSL Q 3 (2^n)) :
    2 ≤ primeRank 3 Q := by
  cases hm with
  | linear n hpos he => exact (hn n hpos he).elim
  | symplectic n hpos he =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      rw [primeRank_congr 3 e]
      exact Theory.SpecificGroups.Classical.EvenRankTwoOddRank.symplectic
  | g2 n hpos he =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
      let : Fintype F := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow
        (by simpa only [Nat.card_eq_fintype_card] using hF)
      rw [primeRank_congr 3 e]
      exact Atlas.G2.EvenThreeRank.two_le_primeRank
  | triality n hpos he =>
      obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff Q n (by omega)).mp he
      obtain ⟨A,hA,hcard⟩ := Triality.Standard.exists_elementaryAbelian_three_card_nine n (by omega)
      let : IsElementaryAbelian 3 A := hA
      rw [primeRank_congr 3 e]
      exact IsElementaryAbelian.primeRank_ge_of_card A hcard
  | ree m hm he =>
      obtain ⟨d,⟨e⟩⟩ := he
      rw [primeRank_congr 3 e]
      exact ReeF4.CubicRank.fixedGroup d
  | symplectic_derived he =>
      obtain ⟨e⟩ := he
      rw [primeRank_congr 3 (e.trans
        Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)]
      exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  | g2_derived he =>
      obtain ⟨e⟩ := he
      rw [primeRank_congr 3 e]
      exact Atlas.G2.EvenThreeRank.two_le_primeRank_derived
  | tits he =>
      obtain ⟨e⟩ := he
      rw [primeRank_congr 3 (e.trans Tits.parrottFiniteImageEquiv)]
      exact Tits.ThreeRank.rank_two_le

private theorem sporadic_outer_two {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (name : SporadicName) (hne : name ≠ .j3) (e : Q ≃* name.Carrier) :
    IsPGroup 2 (MulAut.Outer Q) := by
  apply IsPGroup.of_equiv _ (MulAut.outerCongr e).symm
  cases name with
  | m11 => exact Sporadic.Mathieu.m11_outer_isPGroup_two
  | m12 =>
      exact m12_outer_isPGroup_two_of_sylow_aut
        Sporadic.Mathieu.M12SmallPair.SylowAutomorphismGroup.isPGroup_two
  | m22 =>
      exact m22_outer_isPGroup_two_of_coverage
        Sporadic.Mathieu.m22DesignAutToAut_surjective
  | m23 => exact Sporadic.Mathieu.m23_outer_isTwoGroup
  | m24 => exact Sporadic.Mathieu.M24OuterRestriction.outer_isPGroup_two
  | j2 => exact JankoTwo.outer_isPGroup_two
  | hs =>
      exact Sporadic.LeechRelated.HS.outer_isPGroup_two_of_pointStabilizer_map
        Sporadic.LeechRelated.HS.pointStabilizer_map
        Sporadic.LeechRelated.HS.normalizer_relIndex_dvd_two_pow
  | ru =>
      let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
      let : Subsingleton (MulAut.Outer Rudvalis.Model) := rudvalis_outer_subsingleton
      exact IsPGroup.of_subsingleton 2 (MulAut.Outer Rudvalis.Model)
  | j3 => exact (hne rfl).elim
  | he =>
      exact Subgroup.isPGroup_outer_of_normalizer Held.permutationGroup 2
        Held.Realization.normalizer_surjective Held.isPGroup_permutationNormalizerQuotient
  | j4 => exact Janko4.AdequateLocal.outer_isPGroup_two

/-- The odd-prime degree-three rows have no coprime actor of order prime to six. -/
theorem odd_prime_three_coprime_actor_eq_one {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q] [Group.IsPerfect Q]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hm : IsPSLSign Q unitary 3 p) (a : MulAut Q)
    (ha : Nat.Coprime (orderOf a) 6) (hc : Nat.Coprime (orderOf a) (Nat.card Q)) : a = 1 := by
  apply MulAut.eq_one_of_coprime_of_inner_power a ha hc
  cases unitary with
  | false =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : IsSimpleGroup PSL(3,F) := e.isSimpleGroup_congr.mp inferInstance
      let : Group.IsPerfect PSL(3,F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      have hh := Matrix.PSL3.odd_prime_sixth_power_inner
        (Group.IsPerfect.not_isSolvable PSL(3,F)) hp ho hF (MulAut.congr e a)
      rw [← map_pow, ← MulAut.map_innerSubgroup_congr e] at hh
      obtain ⟨b,hb,he⟩ := hh
      exact ((MulAut.congr e).injective he) ▸ hb
  | true =>
      obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
      let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
        e.isSimpleGroup_congr.mp inferInstance
      have hh := J.odd_prime_sixth_power_inner hp ho hF hconj (MulAut.congr e a)
      rw [← map_pow, ← MulAut.map_innerSubgroup_congr e] at hh
      obtain ⟨b,hb,he⟩ := hh
      exact ((MulAut.congr e).injective he) ▸ hb


/-- The remaining simple A.3.6 rows admit no nontrivial actor of order
prime to six and coprime to the group order under the actual three-rank bound. -/
theorem remaining_simple_coprime_actor_eq_one
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q] [Group.IsPerfect Q]
    (hm : RemainingSimpleModel Q) (hr : primeRank 3 Q ≤ 1)
    (a : MulAut Q) (ha : Nat.Coprime (orderOf a) 6)
    (hc : Nat.Coprime (orderOf a) (Nat.card Q)) : a = 1 := by
  have ho : Odd (orderOf a) := Nat.coprime_two_right.mp (ha.of_dvd_right (by decide))
  cases hm with
  | three_odd p hp ho unitary he =>
      exact odd_prime_three_coprime_actor_eq_one hp ho unitary he a ha hc
  | rank_two hm hn =>
      have hh := rank_two_threeRank hm hn
      omega
  | sporadic name hn he =>
      exact MulAut.eq_one_of_odd_coprime_of_outer_two a ho hc
        (sporadic_outer_two name hn he.some)
  | janko_one he =>
      let : Subsingleton (MulAut.Outer Janko1.Model) := Janko1.OuterCertificate.outer_subsingleton
      exact MulAut.eq_one_of_odd_coprime_of_outer_two a ho hc
        ((IsPGroup.of_subsingleton 2 (MulAut.Outer Janko1.Model)).of_equiv
          (MulAut.outerCongr he.some).symm)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear
