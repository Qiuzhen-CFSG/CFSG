module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowOffender
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesNormalizerBoundAssembly

/-!
# The moved-seed B.4 classification and source 3.2.5 assembly

FF extraction now discharges the genuine offender premise of the corrected
B.4.2 classification on the chosen seed. The source 3.2.5 and Chapter 12
consumers combine this with both cubic bounds and fixed-space invariance.

The D.3.5 model/type sieve and D.3.10 full-orbit exhaustion remain explicit
inputs owned by `qt-baumann-fsu`; these implications do not assert the
unconditional source theorem. Final doubled-branch exclusion belongs to
`qt-d-1222-source`.
Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
B.4.2, D.3.5, D.3.10, 3.2.5 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Under the actual ambient multiple-overgroup hypothesis, the proved
local cubic bound produces the seed FF offender without any additional input. -/
theorem seed_ff_of_moved_of_many (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) : IsFFModule D.seedRepresentation :=
  D.seed_ff_of_moved h.toHypothesis1221 (D.orbit_cubicRatio_le_of_many h hmany) hc hm

/-- B.4.2 now applies unconditionally in the moved chosen-seed branch.
The subsequent D.3.5 model exclusions and type bound remain to be proved. -/
theorem seed_b4_of_moved_of_many (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) :
    ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase
      D.seedRepresentation D.componentImage (offenderSubgroup D.seedRepresentation) :=
  D.seed_b4_of_ff h.toHypothesis1221 hc (D.seed_ff_of_moved_of_many h hmany hc hm)

/-- The source 3.2.5 assembly with numerical bounds, fixed-space invariance,
and FF extraction discharged. Only the owned model/type sieve and the
full-normalizer exhaustion remain explicit. -/
theorem source325_of_sieve_and_exhaustion_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hsieve : cubicRatio D.orbitRepresentation ≤ 2 →
      V ⊓ centralizer (L : Set G) = ⊥ →
      V < componentOrbit V (T : Subgroup G) → IsFFModule D.seedRepresentation →
      ConstituentModel (D.seedRepresentation.comp D.componentImage.subtype) ∧
        D.SylowTwoModuleTypes)
    (hexhaust : cubicRatio D.orbitRepresentation ≤ 2 →
      D.NormalizerOrbitCubicBound h.toHypothesis1221 →
      V ⊓ centralizer (L : Set G) = ⊥ →
      V < componentOrbit V (T : Subgroup G) → D.SylowMovedModel →
      componentOrbit V (normalizer (L : Set G)) = componentOrbit V (T : Subgroup G)) :
    D.Source325Alternatives := by
  apply D.source325_of_moved_of_many h hmany
  intro hq hfull hc hm
  obtain ⟨hmodel,htypes⟩ := hsieve hq hc hm (D.seed_ff_of_moved h.toHypothesis1221 hq hc hm)
  have hs := D.sylowMovedModel_of_model_of_two_module_types hmodel htypes
  exact D.markedDoubled_of_sylow_model_of_orbit_eq h.toHypothesis1221 hc hs.1 hs.2
    (hexhaust hq hfull hc hm hs)

/-- Actual Chapter 12 structural application with the offender premise removed.
The remaining sieve and exhaustion belong to qt-baumann-fsu; final doubled
exclusion is retained by qt-d-1222-source. -/
theorem structural_of_sieve_and_exhaustion_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hsieve : cubicRatio D.orbitRepresentation ≤ 2 →
      V ⊓ centralizer (L : Set G) = ⊥ →
      V < componentOrbit V (T : Subgroup G) → IsFFModule D.seedRepresentation →
      ConstituentModel (D.seedRepresentation.comp D.componentImage.subtype) ∧
        D.SylowTwoModuleTypes)
    (hexhaust : cubicRatio D.orbitRepresentation ≤ 2 →
      D.NormalizerOrbitCubicBound h.toHypothesis1221 →
      V ⊓ centralizer (L : Set G) = ⊥ →
      V < componentOrbit V (T : Subgroup G) → D.SylowMovedModel →
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
    (D.source325_of_sieve_and_exhaustion_of_many h hmany hsieve hexhaust) hex

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
