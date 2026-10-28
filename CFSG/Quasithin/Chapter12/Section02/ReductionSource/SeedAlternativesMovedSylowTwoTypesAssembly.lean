module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowTwoTypes

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowSieveAssembly

/-!
# Source 3.2.5 after the non-SL₃ type bounds

The actual model intertwiners discharge the type-bound premise for every
marked constituent row except SL₃. This removes those branches from both
the source alternatives and their structural Chapter 12 application.

The remaining SL₃ transport, exceptional-row exclusion and full-normalizer
exhaustion belong to qt-baumann-fsu. The final exclusion of the doubled
alternative belongs to qt-d-1222-source. These conditional consumers are
not assertions that source 3.2.5 or the final structural theorem is complete.

Source: Aschbacher--Smith D.3.5, D.3.10, 3.2.5 and 12.2.2,
combined manuscript of 1 March 2004, printed pp.195--196,201,580,794--795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Source 3.2.5 with the non-SL₃ type-bound branches fully discharged. -/
theorem source325_of_exceptional_exclusion_linearThree_types_and_exhaustion_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hexception : cubicRatio D.orbitRepresentation ≤ 2 →
      V ⊓ centralizer (L : Set G) = ⊥ → V < componentOrbit V (T : Subgroup G) →
      D.SeedSieveExceptions → False)
    (hthree : cubicRatio D.orbitRepresentation ≤ 2 →
      V ⊓ centralizer (L : Set G) = ⊥ → V < componentOrbit V (T : Subgroup G) →
      ∀ F : BinaryField,
        ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3) →
        D.SylowTwoModuleTypes)
    (hexhaust : cubicRatio D.orbitRepresentation ≤ 2 →
      D.NormalizerOrbitCubicBound h.toHypothesis1221 →
      V ⊓ centralizer (L : Set G) = ⊥ → V < componentOrbit V (T : Subgroup G) →
      D.SylowMovedModel →
      componentOrbit V (normalizer (L : Set G)) = componentOrbit V (T : Subgroup G)) :
    D.Source325Alternatives := by
  apply D.source325_of_exceptional_exclusion_types_and_exhaustion_of_many
    h hmany hexception _ hexhaust
  intro hq hc hm hmodel
  exact D.sylowTwoModuleTypes_of_constituentModel_of_linearThree h.quasisimple hc hm hmodel
    (hthree hq hc hm)

/-- Actual Chapter 12 application, retaining only the named surviving source obligations. -/
theorem structural_of_exceptional_exclusion_linearThree_types_and_exhaustion_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hexception : cubicRatio D.orbitRepresentation ≤ 2 →
      V ⊓ centralizer (L : Set G) = ⊥ → V < componentOrbit V (T : Subgroup G) →
      D.SeedSieveExceptions → False)
    (hthree : cubicRatio D.orbitRepresentation ≤ 2 →
      V ⊓ centralizer (L : Set G) = ⊥ → V < componentOrbit V (T : Subgroup G) →
      ∀ F : BinaryField,
        ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3) →
        D.SylowTwoModuleTypes)
    (hexhaust : cubicRatio D.orbitRepresentation ≤ 2 →
      D.NormalizerOrbitCubicBound h.toHypothesis1221 →
      V ⊓ centralizer (L : Set G) = ⊥ → V < componentOrbit V (T : Subgroup G) →
      D.SylowMovedModel →
      componentOrbit V (normalizer (L : Set G)) = componentOrbit V (T : Subgroup G))
    (hex : ¬ D.MarkedDoubled) :
    (T : Subgroup G) ≤ normalizer (V : Set G) ∧
    IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G))) ∧
    (∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V) ∧
    ((normalizer (L : Set G)) ≤ normalizer (V : Set G) ∨
      V ⊓ centralizer (L : Set G) = ⊥) :=
  D.structural_of_source325_of_not_doubled_of_many h hmany
    (D.source325_of_exceptional_exclusion_linearThree_types_and_exhaustion_of_many
      h hmany hexception hthree hexhaust) hex

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
