module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.FittingControl
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.CentralModule
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.AlternatingThree.Complete
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.Residual
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterA.Section04.Intersection
public import Theory.GroupTheory.Fitting.OutsideComponent
public import Theory.GroupTheory.MaximalTwoLocalCore

/-!
# Original intersection-core growth when the central seed has order two

Empty Lf makes the local solvable residual centralize the omega-center of
its two-core. Radical characteristic control therefore contains that residual.
C.2.6 and the genuine moved-A₃ exclusion contain the Fitting preimage as well,
and component extraction then contains the generalized-Fitting preimage.

If two distinct maximal locals had an intersection core equal to either local
core, maximality would give the needed characteristic control in the other
local. The preceding argument and A.4.4 identify both cores, hence both full
normalizers, a contradiction. This is the |Ω₁Z(T)|=2 source branch; it is the
branch supplied by the actual orthogonal action in 15.3.

Source: Aschbacher–Smith 14.1.13–14, printed p.979.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.SourcePreliminaries
open Chapter15.Section03 Chapter15.Section03.InitialSource ChapterC.Section02Source
universe u
variable {G : Type u} [Group G] [Finite G]

theorem generalizedFittingPreimage_le_of_radical_control
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hZ : Nat.card (centralInvolutions T) = 2)
    (R H : Subgroup M) (hr : IsPRadical 2 R)
    (hRT : R ≤ (T.subtype hM.2 : Subgroup M))
    (hcontrol : R.characteristicNormalizerClosure ≤ H) :
    (generalizedFitting (M ⧸ pCore 2 M)).comap (QuotientGroup.mk' (pCore 2 M)) ≤ H := by
  have hMH : M ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1,hM.2⟩
  have hc : centralizer (pCore 2 M : Set M) ≤ pCore 2 M :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hMH)
  have hQR : pCore 2 M ≤ R := pCore_le_of_pCore_normalizer_le R hr.isPGroup hr.2.le
  have hf : twoFittingCore M ≤ H := fittingCore_le_of_no_moved_alternatingThree
    (hG.twoLocal_sqtk hM.1.1) R H hr hcontrol hc
    (fun X hb hm => alternating_three_excluded_from_source hG T hM hu hmany
      X R hb hQR hRT hm (Or.inr hZ))
  have hres : solvableResidual M ≤ H := by
    by_contra hout
    apply outside_moves_radicalCentralModule hr hc hcontrol hout
    exact residual_le_centralizer_omegaCore
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hG T hempty hMH
  by_contra hout
  obtain ⟨L,hL,_,hLH⟩ := exists_cComponent_outside_of_fitting_preimage_le H hf hout
  let := hL.perfect
  exact hLH ((le_solvableResidual_of_isPerfect L).trans hres)

theorem intersection_core_ne_local_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M N Mc : Subgroup G}
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hZ : Nat.card (centralInvolutions T) = 2) (hne : M ≠ N) :
    (M ⊓ N).pCoreIn 2 ≠ M.pCoreIn 2 := by
  intro he
  let R := M.pCoreIn 2
  have hRN : R ≤ N := by
    change M.pCoreIn 2 ≤ N
    rw [←he]
    exact (pCoreIn_le 2 (M ⊓ N)).trans inf_le_right
  have hRT : R ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hM.2] using
      pCoreIn_le_sylow M (T.subtype hM.2)
  have hnorm : normalizer (R.subgroupOf N : Set N) = M.subgroupOf N := by
    rw [←subgroupOf_normalizer_eq hRN,maximalTwoLocal_normalizer_core hM.1]
  have hr : IsPRadical 2 (R.subgroupOf N) := by
    refine ⟨?_,?_⟩
    · intro hz
      have hh := congrArg (map N.subtype) hz
      rw [map_subgroupOf_eq_of_le hRN,Subgroup.map_bot] at hh
      exact maximalTwoLocal_core_ne_bot hM.1 hh
    · change (normalizer (R.subgroupOf N : Set N)).pCoreIn 2 = R.subgroupOf N
      apply map_injective N.subtype_injective
      rw [map_pCoreIn_of_injective 2 _ _ N.subtype_injective,hnorm,
        subgroupOf_map_subtype,he,map_subgroupOf_eq_of_le hRN]
  have hcpu : (R.subgroupOf N).characteristicNormalizerClosure ≤ M.subgroupOf N :=
    characteristicNormalizerClosure_subgroupOf_le hRN
      (maximalTwoLocal_characteristicNormalizer_core hM.1).le
  have hfit := generalizedFittingPreimage_le_of_radical_control hG T hempty hN hu hmany hZ
    (R.subgroupOf N) (M.subgroupOf N) hr (comap_mono hRT) hcpu
  have hfitM : ChapterA.Section04.twoGeneralizedFittingPreimage N ≤ M := by
    rintro x ⟨y,hy,rfl⟩
    exact hfit hy
  have hfitN : ChapterA.Section04.twoGeneralizedFittingPreimage N ≤ N := map_subtype_le _
  have ha : ChapterA.Section04.IntersectionAlternative
      (ChapterA.Section04.twoCoreQuotientImage N (ChapterA.Section04.twoGeneralizedFittingPreimage N)) := by
    rw [ChapterA.Section04.twoCoreQuotientImage_fittingPreimage]
    refine Or.inr ⟨le_rfl,?_,?_⟩
    · exact (inferInstance : ((generalizedFitting (N ⧸ pCore 2 N)).subgroupOf
        (generalizedFitting (N ⧸ pCore 2 N))).Normal).isSubnormal
    · exact (closure_le _).mpr (fun x hx => hx.1.1)
  have hcores := ChapterA.Section04.lemma_A_4_4_1 N M (ChapterA.Section04.twoGeneralizedFittingPreimage N)
    (ChapterA.Section04.twoCore_le_fittingPreimage N) (le_inf hfitN hfitM) ha
  rw [inf_comm N M,he] at hcores
  apply hne
  rw [←maximalTwoLocal_normalizer_core hM.1,←hcores,maximalTwoLocal_normalizer_core hN.1]

end CFSG.Quasithin.Chapter14.SourcePreliminaries
