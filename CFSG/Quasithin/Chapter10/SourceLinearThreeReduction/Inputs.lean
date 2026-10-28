module
public import CFSG.Quasithin.Chapter10.SourceNormalizationSurvivor
public import CFSG.Quasithin.Chapter3.Section02.MinimalModuleSelection

/-!
# Independent source inputs for the non-A5 Chapter 10 reduction

The point-centralizer proof selects a minimal original full module. The
generation bound concerns every actual H* and is independent of that choice.
The small-weak-closure argument may reselect the seed, but must preserve the
full module on which the point-centralizer and numerical arguments were made.
Its conclusion retains the literal natural section, not just a group name.

These are outstanding source obligations, not instances or source theorems.
The assembly in `SourceLinearThreeReduction` derives the exact survivor from
them. Its producers must discharge all three inputs before that reduction is
unconditional. The A5 tensor exclusion is not an input to any of them.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
10.1.1--2, 10.2.3, 10.2.9 and 10.2.12--13, printed pp.741--755.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] (T : Sylow 2 G)

/-- The geometric part of source 10.1.1(3), on one actual chosen setup.
The pair generation and exchanger will be constructed by the assembly. -/
structure SourceLinearThreeGeometry {L : Subgroup G}
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) where
  full_eq_local : D.fullModule = D.moduleSubgroup
  quotient : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
  natural : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
    (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
    ((Representation.specialLinearNatural 3).comp
      (quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))
  crossed : ∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)

/-- The original point-centralizer argument, including its choice of seed.
No irreducibility is asserted for an arbitrary fixed fundamental setup. -/
def SourceNonnormalPointControlAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ L : Subgroup G, L ∈ Chapter1.LStar G (T : Subgroup G) →
    ChapterA.Section04.IsFaithfulSignalizerType L → IsQuasisimple (L ⧸ pCore 2 L) →
    ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.IsMinimalFullModule ∧
      ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal

/-- The upper bound from original 10.2.3, for the actual H* family.
The maximal normalizer is independent of the seed in D. -/
def SourceNonnormalGenerationBoundAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal, generationParameter H ≤ 2

/-- The non-A5 implication of original 10.2.12 for an actual minimum
offender of corank at most two. Reselection
preserves the full module, so all previously proved centralizer data transport.
Only the lower bound on w is requested; the assembly proves both equalities. -/
def SourceNonnormalSmallOffenderAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    D.IsMinimalFullModule →
    ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) →
    ∀ g : G, g ∉ D.maximalLocal →
    ⁅D.fullModule,D.fullModule.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
    globalW D.fullModule (T : Subgroup G) =
      (subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
        (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) : ℕ∞) →
    subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 2 →
    ∃ E : FundamentalSetup KnownSimple.IsKnownSimple T L,
      E.fullModule = D.fullModule ∧ Nonempty (SourceLinearThreeGeometry T E) ∧
      2 ≤ globalW E.fullModule (T : Subgroup G)

end CFSG.Quasithin.Chapter10
