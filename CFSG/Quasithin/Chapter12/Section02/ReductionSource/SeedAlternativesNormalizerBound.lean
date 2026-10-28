module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternatives
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.NormalizerOrbit

/-!
# The chosen seed's normalizer-orbit cubic bound

Theorems A and C supply the actual uniqueness theorem in the Fundamental
Setup of the chosen seed. Source 3.1.6 then bounds the action of N_G(L)
on U = ⟨V^{N_G(L)}⟩, using the exact full-orbit and normalizer identities.
No invariance of the seed under N_G(L) is required.

Source: Aschbacher--Smith 3.2.5, printed p.580, applied to the original
chosen-module input of 12.2.2, printed pp.794--795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The full normalizer action satisfies the second numerical bound of
source 3.2.5, on precisely the action in `NormalizerOrbitCubicBound`. -/
theorem normalizerOrbit_cubicBound_of_many (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    D.NormalizerOrbitCubicBound h.toHypothesis1221 := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hb := (D.fundamentalSetup h.toHypothesis1221).normalizerOrbit_cubicRatio_le_of_many
    hu hmany
  have transport (M U : Subgroup G) (hM : M = normalizer (L : Set G))
      (hU : U = componentOrbit V (normalizer (L : Set G)))
      (hn : M ≤ normalizer (U : Set G)) (he : IsElementaryAbelian 2 U)
      (hb : letI := he
        cubicRatio (ChapterD.UniqueFactor.imageRepresentation M U hn) ≤ 2) :
      D.NormalizerOrbitCubicBound h.toHypothesis1221 := by
    subst M U
    exact hb
  exact transport _ _ (by
      simp only [Chapter3.Section02.FundamentalSetup.maximalLocal, D.localOrbit_eq])
    (D.fundamentalSetup_fullModule h.toHypothesis1221) _ _ hb

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
