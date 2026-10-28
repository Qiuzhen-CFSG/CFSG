module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.Bender
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.Contracts
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# Reselecting the seed in the half-Sylow normalizer argument

The normalizer conclusion depends only on L and T. Reselect the source module
using the original 10.1.1 choice: the centralizing-Thompson branch is already
proved, and the rank-one row follows from Bender Borel uniqueness. Only the
binary-three natural row remains, with its actual module action and full/local
module equality retained. No classification is imposed on an arbitrary seed.

The selected-module producer belongs to qt-d-10-nona5-point-selection. The
binary-three normalizer proof and unconditional assembly remain with
qt-d-10-nona5-half-sylow-unique. These two inputs are explicit below; this
module does not assert the unconditional source theorem.
Source: Aschbacher--Smith 10.1.1--2 and 10.2.5, pp.741--742,747--748.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The source's rank-one module supplies the actual Bender quotient. -/
theorem stabilizer_normalizer_of_rankOneNatural
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hm : Selection.RankOneNatural D) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤ D.maximalLocal := by
  obtain ⟨n,hnn,e,_⟩ := hm
  let : NeZero n := ⟨by omega⟩
  apply stabilizer_normalizer_of_bender D hn
  exact .linear n (by omega) ⟨GaloisField 2 n, inferInstance, inferInstance,
    GaloisField.card 2 n (by omega),
    ⟨e.trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 n))⟩⟩

/-- The source choice reduces the normalizer contract to its binary-three row.
The seed of the requested D is replaced only internally. -/
theorem stabilizerNormalizerAt_of_moduleChoice
    (hchoice : Selection.ModuleChoiceAt T)
    (hthree : ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      D.IsMinimalFullModule → D.fullModule = D.moduleSubgroup →
      ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
      ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
      Selection.BinaryThreeNatural D →
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) →
      normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤ D.maximalLocal) :
    StabilizerNormalizerAt T := by
  intro hmany L D hn hna
  obtain ⟨E,hE,t,ht,htn,hcross,hcases⟩ :=
    hchoice hmany L D.maximal D.faithful D.quasisimple hn hna
  by_cases hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (E.fullModule : Set G)
  · exact stabilizer_normalizer_of_thompson_centralizes E hJ
  obtain ⟨heq,hm⟩ := hcases.resolve_left hJ
  rcases hm with hr | h3
  · exact stabilizer_normalizer_of_rankOneNatural E hn hr
  · exact hthree L E hmany hE heq hn hna h3 hJ

/-- Apply the completed Bender normalizer branch to the actual uniqueness
consumer. The independent containing-pair contradiction remains explicit. -/
theorem halfSylowUnique_of_bender_and_pairExclusion
    (hpair : ContainingPairExclusionAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hm : ClassificationModels.IsBenderModel (L ⧸ pCore 2 L)) : HalfSylowUnique D := by
  intro H hH hhalf
  by_contra hne
  obtain ⟨t,K₁,K₂,C⟩ := exists_containingPair D
    (stabilizer_normalizer_of_bender D hn hm) hn hH hne hhalf
  exact hpair hmany L D hn hna H t K₁ K₂ C

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
