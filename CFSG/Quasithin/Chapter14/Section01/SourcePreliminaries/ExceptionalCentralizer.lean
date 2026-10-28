module
public import CFSG.Quasithin.Chapter14.Section01.SourcePreliminaries.ExceptionalFactors
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.CubicFamily
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.WholeCubicControl

/-!
# Centralizer control for the whole original exceptional cubic product

Take all moved A₃ blocks outside the actual characteristic-control group.
Their full Sylow orbit product is normal and is A₄ or A₄². Restricting
C.2.6 to its centralizer joined with R excludes every further outside block.
The solvable residual is already controlled by empty Lf, and A.4.4 then
places the whole centralizer in H.

The actual equality R=O₂(H) is retained. No generalized-Fitting intersection
identity or centralizer core is assumed.
Source: Aschbacher–Smith 14.1.13, printed p.979.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.SourcePreliminaries
open Chapter15.Section03 Chapter15.Section03.InitialSource ChapterC.Section02Source
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_exceptional_centralizer_control
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (R H : Subgroup M) (hr : IsPRadical 2 R)
    (hRT : R ≤ (T.subtype hM.2 : Subgroup M))
    (hcontrol : R.characteristicNormalizerClosure ≤ H)
    (hcore : H.pCoreIn 2 = R)
    (hout : ¬ (generalizedFitting (M ⧸ pCore 2 M)).comap
      (QuotientGroup.mk' (pCore 2 M)) ≤ H) :
    M = Mc ∧ 2 < Nat.card (centralInvolutions T) ∧
    ∃ N : Subgroup M, N.Normal ∧
      (Nonempty (N ≃* alternatingGroup (Fin 4)) ∨ Nonempty (N ≃* AlternatingFourPair.Model)) ∧
      centralizer (N : Set M) ≤ H := by
  obtain ⟨he,hZ,n,hn,_,L,hL,_,_⟩ := source_exceptional_moved_factors
    hG T hempty hM hu hmany R H hr hRT hcontrol hout
  let I := {B : Subgroup M // ChapterC.IsBlock B ∧ ChapterC.IsAlternatingBlock B 3 ∧
    B = ⁅B,elementaryAbelianMaxJ R⁆ ∧ ¬ B ≤ H}
  let : Nonempty I := ⟨⟨L ⟨0,hn⟩,(hL _).2.2.1,(hL _).2.2.2.1,(hL _).2.2.2.2,(hL _).2.1⟩⟩
  let B : I → Subgroup M := fun i => i.val
  let N := ⨆ i, conjugateSpanBy (B i) (T.subtype hM.2 : Subgroup M)
  have hc : centralizer (pCore 2 M : Set M) ≤ pCore 2 M :=
    hG.evenCharacteristic T M hM.1 hM.2
  have hf : generalizedFitting M = pCore 2 M := generalizedFitting_eq_pCore_of_selfCentralizing 2 hc
  have h3 : primeRank 3 M ≤ 2 :=
    (hG.twoLocal_sqtk hM.1.1).stronglyQuasithin 3 Nat.prime_three (by decide)
  obtain ⟨hN,hm⟩ := ChapterC.RankOne.ChiProduct.cubic_family_models hf h3
    (T.subtype hM.2) B (fun i => i.property.1) (fun i => i.property.2.1)
  let : N.Normal := hN
  refine ⟨he,hZ,N,hN,hm,?_⟩
  have hMH : M ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1,hM.2⟩
  have hres : solvableResidual M ≤ H := by
    by_contra hres
    apply outside_moves_radicalCentralModule hr hc hcontrol hres
    exact residual_le_centralizer_omegaCore
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hG T hempty hMH
  apply centralizer_le_of_all_outside_cubic_blocks (hG.twoLocal_sqtk hM.1.1)
    hc R H N hr hcontrol hcore hres (AlternatingThree.cubic_model_structure N hm).2.1
  intro X hb ha hx houtX
  let i : I := ⟨X,hb,ha,hx,houtX⟩
  exact (le_conjugateSpanBy X (T.subtype hM.2 : Subgroup M)).trans
    (le_iSup (fun j => conjugateSpanBy (B j) (T.subtype hM.2 : Subgroup M)) i)

end CFSG.Quasithin.Chapter14.SourcePreliminaries
