module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.NonFFFixedSpan
public import Theory.GroupTheory.ReducedNormal.SylowCentralSeed
public import Theory.GroupTheory.SylowFixedConjugateSpanSplitting
public import Theory.GroupTheory.Commutator.SylowFixedSeed
public import Theory.GroupTheory.ConjugateSpanSupplement
public import Theory.GroupTheory.ConjugateSpanNormalizer
public import Theory.GroupTheory.TwoFixedLinesIrreducible

/-!
# A genuine reduced module from the quiet Sylow-fixed seed

The L₀-orbit of C_{V_M}(T) is nonzero and is two-reduced for L₀T.
Odd-index Sylow averaging splits it into its L₀-moved and fixed parts;
in the quiet multiple-overgroup branch the fixed part vanishes. Its
normalizer lies in the original M by uniqueness. Odd section-kernel actors
fixing the Sylow omega-center centralize this entire module.

These assertions construct the fixed-generation module used in the proof
of 4.4.14. They do not identify it with V_M or assert its non-FF clause.
Source: Aschbacher--Smith B.2.14, 4.4.14 and 10.2.3(2), printed pp.78,
624--625 and745 (combined manuscript of 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
private theorem unique : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- The literal L₀-orbit of the original full module's T-fixed subgroup. -/
@[expose] def sourceQuietFixedSpan : Subgroup G :=
  conjugateSpanBy (D.fullModule ⊓ centralizer (T : Set G)) (localOrbit T L)

/-- The fixed-seed orbit remains inside the original full module. -/
theorem sourceQuietFixedSpan_le : sourceQuietFixedSpan D ≤ D.fullModule :=
  conjugateSpanBy_le inf_le_left
    ((localOrbit T L).le_normalizer.trans D.maximalLocal_normalizes_fullModule)

private theorem seed_normalized :
    (T : Subgroup G) ≤ normalizer
      (D.fullModule ⊓ centralizer (T : Set G) : Set G) :=
  (le_inf ((le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule)
    ((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf

private theorem span_join : sourceQuietFixedSpan D = conjugateSpanBy
    (D.fullModule ⊓ centralizer (T : Set G)) (localJoin T L) :=
  (conjugateSpanBy_sup_of_normalizes_seed _ _ _ (seed_normalized D)
    (le_normalizer_componentOrbit L T)).symm

/-- Both original local actors normalize the fixed-seed orbit. -/
theorem sourceQuietFixedSpan_normalized :
    localJoin T L ≤ normalizer (sourceQuietFixedSpan D : Set G) := by
  rw [span_join]
  exact le_normalizer_conjugateSpanBy _ _

/-- Reducedness uses the actual centralizer quotient inside L₀T. -/
theorem sourceQuietFixedSpan_reduced :
    IsPReduced 2 ((sourceQuietFixedSpan D).subgroupOf (localJoin T L)) := by
  let := D.fullModule_elementary (unique D)
  let : IsElementaryAbelian 2 (sourceQuietFixedSpan D) :=
    IsElementaryAbelian.of_le (sourceQuietFixedSpan_le D)
  exact reduced_of_sylow_central_seed T (localJoin T L) (sourceQuietFixedSpan D)
    (D.fullModule ⊓ centralizer (T : Set G)) le_sup_right
    ((sourceQuietFixedSpan_le D).trans (D.fullModule_le_orbit.trans le_sup_left))
    (sourceQuietFixedSpan_normalized D) (le_conjugateSpanBy _ _) inf_le_right (span_join D)

/-- The two-group fixed-point theorem makes the original fixed seed nonzero. -/
theorem sourceQuietFixedSpan_ne_bot : sourceQuietFixedSpan D ≠ ⊥ := by
  let := D.fullModule_elementary (unique D)
  have hV : D.fullModule ≠ ⊥ := by
    intro he
    exact D.module_ne_bot (bot_unique ((le_componentOrbit _ _).trans_eq he))
  have hz := inf_centralizer_ne_bot_of_pGroups (T : Subgroup G) D.fullModule
    T.isPGroup' (IsElementaryAbelian.isPGroup 2 D.fullModule)
    ((le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule) hV
  exact fun he => hz (bot_unique ((le_conjugateSpanBy _ _).trans_eq he))

/-- Taking the L₀-orbit does not add new T-fixed vectors inside V_M. -/
theorem sourceQuietFixedSpan_fixed :
    sourceQuietFixedSpan D ⊓ centralizer (T : Set G) =
      D.fullModule ⊓ centralizer (T : Set G) :=
  le_antisymm (inf_le_inf_right _ (sourceQuietFixedSpan_le D))
    (le_inf (le_conjugateSpanBy _ _) inf_le_right)

/-- The constructed module satisfies the literal fixed-generation equality. -/
theorem sourceQuietFixedSpan_generation : sourceQuietFixedSpan D =
    conjugateSpanBy (sourceQuietFixedSpan D ⊓ centralizer (T : Set G)) (localOrbit T L) := by
  rw [sourceQuietFixedSpan_fixed]
  rfl

/-- In the quiet branch the entire constructed module is moved by L₀. -/
theorem sourceQuietFixedSpan_commutator
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)) :
    ⁅sourceQuietFixedSpan D,localOrbit T L⁆ = sourceQuietFixedSpan D := by
  let X := localOrbit T L
  let H := localJoin T L
  let Z := D.fullModule ⊓ centralizer (T : Set G)
  let := D.fullModule_elementary (unique D)
  let : IsElementaryAbelian 2 (sourceQuietFixedSpan D) :=
    IsElementaryAbelian.of_le (sourceQuietFixedSpan_le D)
  have he := span_join D
  have hZH : Z ≤ H := inf_le_left.trans (D.fullModule_le_orbit.trans le_sup_left)
  have hHX : H ≤ normalizer (X : Set G) :=
    sup_le X.le_normalizer (le_normalizer_componentOrbit L T)
  have hmove := commutator_conjugateSpan_eq_of_fixed_supplement Z H H X T
    hZH le_sup_left le_sup_right H.le_normalizer hHX le_sup_left le_rfl inf_le_right
  have hzero : sourceQuietFixedSpan D ⊓ centralizer (H : Set G) = ⊥ := by
    apply bot_unique
    exact (inf_le_inf (sourceQuietFixedSpan_le D)
      (centralizer_le (show localOrbit T L ≤ H from le_sup_left))).trans_eq
      (source_fullModule_fixed_eq_bot_of_many D hmany hJ)
  have hElm : IsElementaryAbelian 2 (conjugateSpanBy Z H) := he ▸ inferInstance
  let := hElm
  have hs := conjugateSpan_split_of_sylow_fixed (T.subtype (show (T : Subgroup G) ≤ H from le_sup_right))
    (show Z ≤ centralizer (((T.subtype (show (T : Subgroup G) ≤ H from le_sup_right) : Sylow 2 H) :
        Subgroup H).map H.subtype : Set G) by
      rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right]
      exact inf_le_right)
  rw [hmove,←he,hzero,sup_bot_eq] at hs
  exact hs.symm

/-- The ambient normalizer of the nonzero reduced seed stays in the original M. -/
theorem sourceQuietFixedSpan_normalizer_le :
    normalizer (sourceQuietFixedSpan D : Set G) ≤ D.maximalLocal := by
  have hu := D.lemma_3_2_3_uniqueness (unique D)
  let := D.fullModule_elementary (unique D)
  let : IsElementaryAbelian 2 (sourceQuietFixedSpan D) :=
    IsElementaryAbelian.of_le (sourceQuietFixedSpan_le D)
  exact normalizer_le_of_unique_maximalTwoLocal hu.2.2
    (IsElementaryAbelian.isPGroup 2 (sourceQuietFixedSpan D)) (sourceQuietFixedSpan_ne_bot D)
    (sourceQuietFixedSpan_normalized D)

/-- Odd actors in the literal section kernel fix the constructed module. -/
theorem sourceQuietFixedSpan_fixes
    (B : Subgroup G) (hB : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B))
    (hz : B ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    B ≤ centralizer (sourceQuietFixedSpan D : Set G) :=
  source_sectionKernel_fixes_fixed_span D B hB hodd hz

end CFSG.Quasithin.Chapter10
