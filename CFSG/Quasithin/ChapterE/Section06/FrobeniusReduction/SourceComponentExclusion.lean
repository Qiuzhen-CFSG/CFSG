module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels.ComponentExclusion
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SourceBalance
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.FactorReduction
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts

/-!
# The ordinary-seed two-factor branch of E.6.25

Construct the literal enlarged C-component in C_G(V₂). The earlier I.3
orbit theorem and 1.2.4 identify it as an ordinary component when the
original seed is ordinary. The adequate E.6.8 model alternatives then give
the corank-three contradiction proved by the root-action calculation.
The counterexample application constructs the factor count from the local
models and derives the exceptional two-factor data from the dimension bound.

The original quotient maps, automizer and summands are retained. The genuine
earlier local containment, residual normalization, orbit projection,
odd-core elimination and E.6.8 model conclusions remain explicit here;
none of them asserts the two-factor exclusion proved below. Construction
of the O’Nan decomposition and the block-enlargement branch remain separate
inputs to the full E.6.25 assembly.

Source: Aschbacher–Smith, proof of E.6.25, printed pp.255–256, and
I.3.1, pp.414–415 (combined manuscript of 1 March 2004).
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

/-- The original exceptional two-factor construction cannot have an ordinary seed.
Only the independently produced earlier-source inputs are retained. -/
theorem exceptional_two_factor_ordinary_seed_excluded [IsElementaryAbelian 2 V]
    (hGLS : ChapterI.RankTwoSource.EarlierOrbitProjection K)
    (h : HypothesisE61 K T M V)
    (containment : EarlierLocalContainment K)
    (normalization : EarlierResidualNormalization K)
    (ho : OddCoreFree V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ J : Subgroup G,
      CentralizerComponent A J →
        (∃ n, BorelAlternative M V A J n) ∨
        (∃ n, SymplecticAlternative M V A J n) ∨ actionCorank V J ≤ 2)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (hsize : D.size = 2)
    (hC : Nat.card (inducedAutomizer V X) = 3)
    (hmodel : Nonempty (D.factor D.distinguished ≃* Frobenius21.Model))
    (hgen : normalClosure ((inducedAutomizer V X).subgroupOf
      (D.factor D.distinguished) : Set (D.factor D.distinguished)) = ⊤)
    (hdim : ∀ i, Module.finrank (ZMod 2) (D.summand i) = 3)
    (hact : ∀ a ∈ inducedAutomizer V
        (M ⊓ centralizer (subspaceGroup (D.summand (otherIndex hsize D.distinguished)) : Set G)),
      ∃ b ∈ D.factor D.distinguished, ∀ v ∈ D.summand D.distinguished,
        automizerRepresentation V a v = automizerRepresentation V b v)
    (hL : CentralizerComponent U L)
    (hXL : X ≤ L) (hfixed : V ⊓ centralizer (L : Set G) = U) : False := by
  have hLC : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G)) :=
    ⟨hL.1, (ChapterI.Balance.ordinary_isTwoComponent hL.2).1⟩
  obtain ⟨J, d, _⟩ := exceptional_two_factor_configuration h containment normalization
    hU hX D hsize hC hmodel hgen hdim hact hLC hXL hfixed
  have hJ := Hyperplanes.SourceBalance.exceptional_enlargement_component_of_ordinary_seed
    hGLS h containment ho hU hL d
  exact d.not_quasisimple_or_field_four_seed hU.1 (h68 _ d.obstruction J hJ)
    (Or.inl (show IsComponentIn L (centralizer (U : Set G)) from hL).quasisimple)


/-- The original ordinary-seed E.6.3 counterexample is excluded once its earlier
regular decomposition, local models and single-summand action have been supplied.
The local models construct the factor count; no exceptional-factor data is assumed. -/
theorem counterexample_ordinary_seed_excluded [IsElementaryAbelian 2 V]
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
    (hact : ∀ hs : D.size = 2, ∀ a ∈ inducedAutomizer V
        (M ⊓ centralizer (subspaceGroup (D.summand (otherIndex hs D.distinguished)) : Set G)),
      ∃ b ∈ D.factor D.distinguished, ∀ v ∈ D.summand D.distinguished,
        automizerRepresentation V a v = automizerRepresentation V b v)
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
    ho h68 hU hX D hs hC hmodel hgen hdim (hact hs) hL hXL hfixed

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
