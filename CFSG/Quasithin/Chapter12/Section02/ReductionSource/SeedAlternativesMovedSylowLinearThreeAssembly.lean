module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowLinearThree

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowSieveAssembly

/-!
# Source 3.2.5 after the complete marked type bound

All marked constituent rows now supply two actual Sylow conjugates, including
SL₃ with its scalar centre. The source alternatives and their Chapter 12
application therefore retain only exceptional-row exclusion and full-normalizer
exhaustion as earlier local arguments. Those remain with qt-baumann-fsu;
the final doubled-branch exclusion belongs to qt-d-1222-source.

These are conditional applications, not completed source-theorem assertions.
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

/-- Source 3.2.5 with the complete constituent-type bound discharged. -/
theorem source325_of_exceptional_exclusion_and_exhaustion_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hexception : cubicRatio D.orbitRepresentation ≤ 2 →
      V ⊓ centralizer (L : Set G) = ⊥ → V < componentOrbit V (T : Subgroup G) →
      D.SeedSieveExceptions → False)
    (hexhaust : cubicRatio D.orbitRepresentation ≤ 2 →
      D.NormalizerOrbitCubicBound h.toHypothesis1221 →
      V ⊓ centralizer (L : Set G) = ⊥ → V < componentOrbit V (T : Subgroup G) →
      D.SylowMovedModel →
      componentOrbit V (normalizer (L : Set G)) = componentOrbit V (T : Subgroup G)) :
    D.Source325Alternatives := by
  apply D.source325_of_exceptional_exclusion_types_and_exhaustion_of_many
    h hmany hexception _ hexhaust
  intro _ hc hm hmodel
  exact D.sylowTwoModuleTypes_of_constituentModel h.quasisimple hc hm hmodel

/-- Actual Chapter 12 application, retaining only the named surviving source obligations. -/
theorem structural_of_exceptional_exclusion_and_exhaustion_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hexception : cubicRatio D.orbitRepresentation ≤ 2 →
      V ⊓ centralizer (L : Set G) = ⊥ → V < componentOrbit V (T : Subgroup G) →
      D.SeedSieveExceptions → False)
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
    (D.source325_of_exceptional_exclusion_and_exhaustion_of_many
      h hmany hexception hexhaust) hex

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
