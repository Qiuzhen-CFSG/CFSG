module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowExterior
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowLinearThreeAssembly

/-!
# Source 3.2.5 after the exterior-five exclusion

The literal moved seed now belongs to the marked constituent list or the
covered-A₆ row. The ten-dimensional SL₅ row is excluded by the same cubic
actor on both constituents, with the component and subspace maps retained.
The two conditional applications leave covered-A₆ exclusion and full-normalizer
exhaustion with qt-baumann-fsu. The final doubled-branch exclusion remains with
qt-d-1222-source. These applications do not assert the completed source theorem.

Source: Aschbacher--Smith D.3.5(5), D.3.10, 3.2.5 and 12.2.2,
printed pp.196,201,580 and794--795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Only the covered-A₆ exception survives the moved-seed model sieve. -/
theorem seed_constituentModel_or_tripleSix_of_moved_of_many (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) :
    ConstituentModel (D.seedRepresentation.comp D.componentImage.subtype) ∨
      (quadraticRatio D.seedRepresentation = 1 ∧
       offenderSubgroup D.seedRepresentation = D.componentImage ∧
       Nonempty (ChapterB.SourceInduction.ProjectiveLine.TripleSixAction
         D.seedRepresentation D.componentImage)) := by
  apply Or.imp_right _ (D.seed_constituentModel_or_exceptional_of_moved_of_many h hmany hc hm)
  intro hex
  rcases hex.2.2 with htriple | ⟨_,e,hd,_⟩
  · exact ⟨hex.1,hex.2.1,htriple⟩
  · exact (D.seed_not_exterior_of_moved h.toHypothesis1221
      (D.orbit_cubicRatio_le_of_many h hmany) hc hm hex e hd).elim

/-- Source assembly with the exterior-five exclusion discharged. -/
theorem source325_of_tripleSix_exclusion_and_exhaustion_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (htriple : cubicRatio D.orbitRepresentation ≤ 2 →
      V ⊓ centralizer (L : Set G) = ⊥ → V < componentOrbit V (T : Subgroup G) →
      quadraticRatio D.seedRepresentation = 1 →
      offenderSubgroup D.seedRepresentation = D.componentImage →
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.TripleSixAction
        D.seedRepresentation D.componentImage) → False)
    (hexhaust : cubicRatio D.orbitRepresentation ≤ 2 →
      D.NormalizerOrbitCubicBound h.toHypothesis1221 →
      V ⊓ centralizer (L : Set G) = ⊥ → V < componentOrbit V (T : Subgroup G) →
      D.SylowMovedModel →
      componentOrbit V (normalizer (L : Set G)) = componentOrbit V (T : Subgroup G)) :
    D.Source325Alternatives := by
  apply D.source325_of_exceptional_exclusion_and_exhaustion_of_many h hmany _ hexhaust
  intro hq hc hm hex
  rcases hex.2.2 with ha | ⟨_,e,hd,_⟩
  · exact htriple hq hc hm hex.1 hex.2.1 ha
  · exact D.seed_not_exterior_of_moved h.toHypothesis1221 hq hc hm hex e hd

/-- The actual Chapter 12 structural application with the same surviving inputs. -/
theorem structural_of_tripleSix_exclusion_and_exhaustion_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (htriple : cubicRatio D.orbitRepresentation ≤ 2 →
      V ⊓ centralizer (L : Set G) = ⊥ → V < componentOrbit V (T : Subgroup G) →
      quadraticRatio D.seedRepresentation = 1 →
      offenderSubgroup D.seedRepresentation = D.componentImage →
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.TripleSixAction
        D.seedRepresentation D.componentImage) → False)
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
    (D.source325_of_tripleSix_exclusion_and_exhaustion_of_many h hmany htriple hexhaust) hex

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
