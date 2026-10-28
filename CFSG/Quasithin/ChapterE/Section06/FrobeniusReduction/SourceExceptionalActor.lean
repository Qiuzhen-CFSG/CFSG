module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceComponentExclusion
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalActor
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels.BlockExclusion

/-!
# Source applications with the distinguished-factor action discharged

The complementary centralizer acts through the actual distinguished factor.
This supplies the original enlargement action internally. In particular the
ordinary-seed counterexample exclusion now retains only genuine earlier local
inputs and the regular normal-closure decomposition; no single-summand action
or exceptional factor identification is assumed.

Source: Aschbacher–Smith, E.6.24–25 and Theorem E.6.3, printed pp.255–256.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
open Components LocalFactors LocalFactors.ExceptionalModels
open Hyperplanes Hyperplanes.ComponentBalance Hyperplanes.Enlargement
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {M V U X L : Subgroup G}

/-- Exclude the original ordinary-seed counterexample using the proved factor action. -/
theorem counterexample_ordinary_seed_excluded_of_source_action [IsElementaryAbelian 2 V]
    (hGLS : ChapterI.RankTwoSource.EarlierOrbitProjection K)
    (h : HypothesisE61 K T M V)
    (h311 : InvariantSubspaces.CommonNormalInput K T)
    (containment : EarlierLocalContainment K)
    (normalization : EarlierResidualNormalization K)
    (ho : OddCoreFree V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ J : Subgroup G,
      CentralizerComponent A J →
        (∃ n, BorelAlternative M V A J n) ∨
        (∃ n, SymplecticAlternative M V A J n) ∨ actionCorank V J ≤ 2)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hm : 2 < localM V) (hsmall : subgroupCorank V U < localM V)
    (hr : 1 < subgroupCorank V U)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (hL : CentralizerComponent U L)
    (hXL : X ≤ L) (hfixed : V ⊓ centralizer (L : Set G) = U)
    (hmodels :
      (X ≤ L ∧ L2BlockBorel L ((L ⊓ M).subgroupOf L) (subgroupCorank V U)) ∨
      (ComponentIn (centralizer (U : Set G)) L ∧
        BorelAlternative M V U L (subgroupCorank V U) ∧
        TorusAction M V L X (subgroupCorank V U) ∧
        V ≤ normalizer (L : Set G) ∧
        ∃ S : Sylow 2 L, (S : Subgroup L).map L.subtype =
          L ⊓ sylowCentralizer (T : Subgroup G) V) ∨
      (V ≤ normalizer (L : Set G) ∧
        TorusAction M V L X (subgroupCorank V U) ∧
        MaximalParabolic L (L ⊓ M) ∧ SymplecticRoot L ⁅V, X⁆ (subgroupCorank V U))) :
    False := by
  have hLC : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G)) :=
    ⟨hL.1, (ChapterI.Balance.ordinary_isTwoComponent hL.2).1⟩
  have hcount := CommutingLifts.factor_count_le_two_of_local_models
    h normalization hU hX hr D hLC hmodels
  obtain ⟨hs,hC,hmodel,hgen,hdim⟩ :=
    exceptional_two_factor_of_counterexample h h311 hU hX hm hsmall D hcount
  exact exceptional_two_factor_ordinary_seed_excluded hGLS h containment normalization
    ho h68 hU hX D hs hC hmodel hgen hdim (exceptional_distinguished_action h hU hX D hs hdim hmodel) hL hXL hfixed

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
