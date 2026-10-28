module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.FactorReduction
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalActor
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels.SourceIdentification
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
public import Theory.Representation.RegularCyclicNormalClosure.Assembly
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.SylowOrbit

/-!
# The actual minimal-obstruction assembly for E.6.3

The earlier E.6.11 output retains the original centralizer C_G(U), selected
C-component L, torus X, quotient Borel or parabolic, and literal action on V.
The normal-closure decomposition is constructed from a factor seed. Local
models count the factors; the source corank and dimension bounds then leave
two exceptional factors. Their original centralizer action constructs the
enlarged C-component, whose ordinary and block alternatives are both excluded.

The final theorem selects an actual minimum from the full domain defining r.
It retains the genuine earlier E.6.23 bound, E.6.11 selection, E.6.7 and E.6.8
outputs, E.6.21 odd-core elimination, 3.1.1 and
1.2 local inputs, and the cited regular-cyclic factor-seed existence theorem.
The A.3.8 Sylow orbit statement is supplied by its proved source theorem.
The retained premises are not asserted as proved here. In particular this conditional
assembly is not an unconditional proof of E.6.3.

Source: Aschbacher–Smith, E.6.3 and E.6.23–25, printed pp.245,255–256.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
open Components LocalFactors LocalFactors.ExceptionalModels
open Hyperplanes Hyperplanes.ComponentBalance Hyperplanes.Enlargement
open InvariantSubspaces.BlockSelection
open Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks
open Representation.RegularCyclicNormalClosure
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {M V U : Subgroup G}

/-- The portion of E.6.11 used at an actual minimum with corank greater than one.
The fields are local group and action data, with no normal-closure conclusions. -/
structure MinimalRegularSection (T : Sylow 2 G) (M V U : Subgroup G) where
  component : Subgroup G
  torus : Subgroup G
  membership : component ∈ Chapter1.cComponentsIn (centralizer (U : Set G))
  escape : ¬ component ≤ M
  regular : RegularCyclicSection M V U torus
  torus_le : torus ≤ component
  fixed : V ⊓ centralizer (component : Set G) = U
  type : IsQuasisimple component ∨ ChapterC.IsL2EvenBlock component (subgroupCorank V U)
  models :
    (torus ≤ component ∧ L2BlockBorel component ((component ⊓ M).subgroupOf component)
      (subgroupCorank V U)) ∨
    (ComponentIn (centralizer (U : Set G)) component ∧
      BorelAlternative M V U component (subgroupCorank V U) ∧
      TorusAction M V component torus (subgroupCorank V U) ∧
      V ≤ normalizer (component : Set G) ∧
      ∃ S : Sylow 2 component, (S : Subgroup component).map component.subtype =
        component ⊓ sylowCentralizer (T : Subgroup G) V) ∨
    (V ≤ normalizer (component : Set G) ∧
      TorusAction M V component torus (subgroupCorank V U) ∧
      MaximalParabolic component (component ⊓ M) ∧
      SymplecticRoot component ⁅V, torus⁆ (subgroupCorank V U))

/-- Both source seed types are excluded, with factor counting, the distinguished
actor, and the enlarged component-versus-block inspection all constructed. -/
theorem counterexample_minimalSection_excluded [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V) (h311 : InvariantSubspaces.CommonNormalInput K T)
    (containment : EarlierLocalContainment K) (normalization : EarlierResidualNormalization K)
    (ho : OddCoreFree V) (h67 : E67Input T M V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ J : Subgroup G,
      CentralizerComponent A J →
        (∃ n, BorelAlternative M V A J n) ∨
        (∃ n, SymplecticAlternative M V A J n) ∨ actionCorank V J ≤ 2)
    (hU : U ∈ obstructionFamily M V)
    (hm : 2 < localM V) (hsmall : subgroupCorank V U < localM V)
    (hr : 1 < subgroupCorank V U) (s : MinimalRegularSection T M V U)
    (D : Decomposition (automizerRepresentation V) (inducedAutomizer V s.torus)) : False := by
  have hcount := CommutingLifts.factor_count_le_two_of_local_models
    h normalization hU s.regular hr D s.membership s.models
  obtain ⟨hs,hC,hmodel,hgen,hdim⟩ :=
    exceptional_two_factor_of_counterexample h h311 hU s.regular hm hsmall D hcount
  obtain ⟨J,d,_⟩ := exceptional_two_factor_configuration h containment normalization
    hU s.regular D hs hC hmodel hgen hdim
    (exceptional_distinguished_action h hU s.regular D hs hdim hmodel)
    s.membership s.torus_le s.fixed
  have hseed : IsQuasisimple s.component ∨ ChapterC.IsL2EvenBlock s.component 2 := by
    simpa only [exceptional_corank_eq_two s.regular hC] using s.type
  have h38 : SylowOrbitSource K := by
    intro H _ _ hH hcore S A hA hgen B hB
    exact ChapterA.Section03.SourceComponents.sylow_orbit_of_generated hH hcore S hA hgen hB
  exact d.excluded_of_earlier_sources h ho h67 h38 h68 hU.1 s.escape hseed

/-- Assemble the original lower bound on the full source minimum, retaining only
named earlier-source producers and the genuine regular-cyclic seed theorem. -/
theorem lower_bound_of_earlier_sources [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V) (hm : 2 < localM V)
    (h311 : InvariantSubspaces.CommonNormalInput K T)
    (containment : EarlierLocalContainment K) (normalization : EarlierResidualNormalization K)
    (ho : OddCoreFree V) (h67 : E67Input T M V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ J : Subgroup G,
      CentralizerComponent A J →
        (∃ n, BorelAlternative M V A J n) ∨
        (∃ n, SymplecticAlternative M V A J n) ∨ actionCorank V J ≤ 2)
    (h23 : 1 < globalR V)
    (h11 : ∀ U ∈ obstructionFamily M V,
      (subgroupCorank V U : ℕ∞) = globalR V → 1 < subgroupCorank V U →
        Nonempty (MinimalRegularSection T M V U))
    (hONan : ∀ X : Subgroup G,
      Input (automizerRepresentation V) (inducedAutomizer V X) →
        ∃ B : Subgroup (Automizer V),
          FactorSeed (automizerRepresentation V) (inducedAutomizer V X) B) :
    (localM V : ℕ∞) ≤ globalR V ∧
      globalS V = (localM V : ℕ∞) ∧ 2 < globalS V := by
  have hbound : (localM V : ℕ∞) ≤ globalR V := by
    by_contra hn
    have hsmall := lt_of_not_ge hn
    obtain ⟨U,hU,hcor⟩ := h.exists_minimal_obstruction hsmall
    have hr : 1 < subgroupCorank V U := by
      apply ENat.natCast_lt_natCast.mp
      simpa only [Nat.cast_one,hcor] using h23
    have hsm : subgroupCorank V U < localM V := by
      apply ENat.natCast_lt_natCast.mp
      rwa [hcor]
    obtain ⟨s⟩ := h11 U hU hcor hr
    obtain ⟨B,hB⟩ := hONan s.torus (s.regular.toInput h hU hr hsm)
    obtain ⟨D⟩ := exists_decomposition_of_factorSeed (automizerRepresentation V)
      (automizerRepresentation_injective V) hB
    exact counterexample_minimalSection_excluded h h311 containment normalization ho
      h67 h68 hU hm hsm hr s D
  have he : globalS V = (localM V : ℕ∞) := min_eq_right hbound
  refine ⟨hbound,he,?_⟩
  rw [he]
  exact_mod_cast hm

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
