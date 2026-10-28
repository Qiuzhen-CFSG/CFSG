module
public import CFSG.Quasithin.Chapter14.Section02.ResidualSylow
public import CFSG.Quasithin.Chapter12.Section08.Setup.RankTwoConstruction
public import Theory.Frattini.OmegaProducts
public import Theory.ElementaryAbelian.Injective
/-!
# Original 14.2.4: the rank-two setup

Identify the Chapter 12.8 seed with the actual Chapter 14 plane module.
Original 14.1.18 supplies the residual, its unique maximal overgroup, and
the escaping point centralizer; the proved YT calculation supplies its
precise two-core and S₃ quotient. These construct all of Hypothesis
12.8.1(2) on the literal Y, T, M. Source: Aschbacher--Smith 14.2.4,
printed p.982, and 12.8.1(2), p.849.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 Chapter15.Section03.InitialSource ChapterA.Section05To06
open Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem sylowOmega_eq_centralInvolutions (T : Sylow 2 G) :
    sylowOmega T = centralInvolutions T := by
  change omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) = _
  rw [←map_omegaOneAmbient_injective (T : Subgroup G).subtype (T : Subgroup G).subtype_injective]
  rfl

omit [Finite G] in
theorem rankTwoSeed_eq_localModule (T : Sylow 2 G) (M : Subgroup G) :
    rankTwoSeed T M = localModule T M := by
  change conjugateSpanBy (sylowOmega T) M = _
  rw [sylowOmega_eq_centralInvolutions]
  rfl

theorem source_lemma_14_2_4
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3)) :
    RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M := by
  obtain ⟨_,_,_,_,_,_,huniq,_,_,_,_,_,hZ,hMc,_⟩ :=
    source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  obtain ⟨hcore,hmodel⟩ := source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  have hne := (plane_ordering_and_overgroups hG T hempty hM hu hmany hcard hZ).2.1
  let := localModule_elementary_from_source hG T ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  refine ⟨hG,hM.1.1,hM.1.2,?_,sourceResidual_le _ _,residualY_normal _ _,
    (pResidual_eq_top_iff 2 _).mpr (residualY_isPPerfect _ _),huniq,?_,hmodel,?_⟩
  · rw [rankTwoSeed_eq_localModule]
    apply le_antisymm (IsElementaryAbelian.primeRank_le_of_card_le _ (by simpa using hcard.le))
    let : IsElementaryAbelian 2 (⊤ : Subgroup (localModule T M)) :=
      IsElementaryAbelian.of_injective (⊤ : Subgroup (localModule T M)).subtype
        (⊤ : Subgroup (localModule T M)).subtype_injective
    exact IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup (localModule T M)) (by simpa using hcard)
  · rw [rankTwoSeed_eq_localModule]
    exact hcore.symm
  · rw [sylowOmega_eq_centralInvolutions,←hMc]
    intro hh
    exact hne ((show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hu ▸ Set.mem_singleton Mc).1.eq_of_le hM.1.1.1 hh).symm
end CFSG.Quasithin.Chapter14.Section02
