module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowTripleSix
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowExteriorAssembly

/-!
# The complete moved-Sylow classification for the literal chosen seed

Both exceptional B.4.2 rows are excluded. The marked constituent models,
including the separate four-dimensional A₇ branch, therefore give the actual
two-summand Sylow orbit, its disjointness and its unchanged-L nonisomorphism.
The conditional source and structural applications leave only full-normalizer
exhaustion with qt-baumann-fsu. The final doubled-branch exclusion remains with
qt-d-1222-source; these conditional applications are not the full source theorem.

Source: Aschbacher--Smith D.3.5, D.3.10, 3.2.5 and 12.2.2,
printed pp.195--196,201--204,580 and 794--795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- All B.4.2 exclusions are discharged for the literal moved chosen seed. -/
theorem seed_constituentModel_of_moved_of_many (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) :
    ConstituentModel (D.seedRepresentation.comp D.componentImage.subtype) := by
  apply (D.seed_constituentModel_or_tripleSix_of_moved_of_many h hmany hc hm).resolve_right
  intro hex
  exact D.seed_not_tripleSix_of_moved h.toHypothesis1221
    (D.orbit_cubicRatio_le_of_many h hmany) hc hm hex.1 hex.2.1
    (Classical.choice hex.2.2)

/-- D.3.5(4--5) on the actual chosen seed, with no local classification premise. -/
theorem sylowMovedModel_of_moved_of_many (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) : D.SylowMovedModel :=
  D.sylowMovedModel_of_constituentModel h.quasisimple hc hm
    (D.seed_constituentModel_of_moved_of_many h hmany hc hm)

/-- The original source alternatives now retain only full-normalizer exhaustion. -/
theorem source325_of_exhaustion_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hexhaust : cubicRatio D.orbitRepresentation ≤ 2 →
      D.NormalizerOrbitCubicBound h.toHypothesis1221 →
      V ⊓ centralizer (L : Set G) = ⊥ → V < componentOrbit V (T : Subgroup G) →
      D.SylowMovedModel →
      componentOrbit V (normalizer (L : Set G)) = componentOrbit V (T : Subgroup G)) :
    D.Source325Alternatives := by
  apply D.source325_of_tripleSix_exclusion_and_exhaustion_of_many h hmany _ hexhaust
  intro hq hc hm hs hg ha
  obtain ⟨a⟩ := ha
  exact D.seed_not_tripleSix_of_moved h.toHypothesis1221 hq hc hm hs hg a

/-- The structural Chapter12 application retains the same one local source input. -/
theorem structural_of_exhaustion_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
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
    (D.source325_of_exhaustion_of_many h hmany hexhaust) hex

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
