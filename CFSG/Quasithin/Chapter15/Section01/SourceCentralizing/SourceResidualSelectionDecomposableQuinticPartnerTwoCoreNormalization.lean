module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoParabolicEssential
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.MaximalBorelSeed
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.Selection
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallSelection
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonFixed.Normalization

/-!
# Normalization when the original module lies in the seed-centralizer core

A moving residual selects an outside minimal parabolic P and its actual
maximal subgroup B=P∩K. The residual of B fixes the original E. The E-span
therefore supplies a small essential action, with the same sharp actor that
satisfies the full V-span balance identities. Thompson replacement makes
the residual of P fix E, contradicting the original movement.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open CFSG.Quasithin.Chapter3
variable {G : Type*} [Group G] [Finite G]

/-- A core-contained original prepared module forces residual centralization
of its actual Thompson fixed subgroup. -/
theorem PreparedChosenModule.thompsonFixed_residual_of_le_seed_centralizer_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T:Subgroup G)≤centralizer (localModule T M:Set G))
    (h : PreparedChosenModule T M V)
    (hVC : V≤(centralizer (centralInvolutions T:Set G)).pCoreIn 2) :
    (pResidual 2 (centralizer (centralInvolutions T:Set G))).map
      (centralizer (centralInvolutions T:Set G)).subtype≤
        centralizer (thompsonFixed T V:Set G) := by
  by_contra hnot
  let E := thompsonFixed T V
  let C := centralizer (centralInvolutions T:Set G)
  let K := (M⊓C)⊔((pResidual 2 C).map C.subtype⊓centralizer (E:Set G))
  obtain ⟨P,hPC,hP,hp,hSQ,hF,hout,hmove,hproper,hVP,he,hchief,hTB,hBP,hBN,hBR⟩ :=
    h.thompsonFixed_moving_parabolic_maximal_residual hG T hempty hM hJ hVC hnot
  let B := P⊓K
  let U := (conjugateSpan P V).subgroupOf P
  let F := (conjugateSpan P E).subgroupOf P
  let S := T.subtype hP.2
  obtain ⟨heU,heF,hEP,A,hA,hAQ,hquad,hmin,hUQ,hkernel,h1,h2,hc,a,hoff,hsharp⟩ :=
    h.outside_minimalParabolic_fixed_essential_actor hG T hempty hM hJ hP hp hout hVP hmove
  let := heU
  let := heF
  let := a.irreducible
  have hmax : IsCoatom (B.subgroupOf P) :=
    (ChapterB.intrinsic_minimalParabolic T P B hp hTB hBP).2
  have hSB : (S:Subgroup P)≤B.subgroupOf P := comap_mono hTB
  have hres : (pResidual 2 (B.subgroupOf P)).map (B.subgroupOf P).subtype≤
      (centralizer (E:Set G)).subgroupOf P := by
    apply map_le_iff_le_comap.mp
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le (show B≤P from inf_le_left)]
    exact hBR
  have hsmall := a.small_natural_alternatives_of_maximal hSQ (B.subgroupOf P)
    hmax hSB hres ⟨_,hoff⟩
  obtain ⟨Rbar,Lbar,hRT,hAR,hLR,hAL,hidx,hcomm,hgen⟩ :=
    ChapterB.minimalParabolic_chief_small_selection a.representation S a.original_minimal
      A hA.1 hoff hsmall
  have hcentral := thompson_centralizes_residual_of_chief_image_geometry
    a.representation S a.original_minimal U A hA hmin hUQ hkernel
    h1 h2 hc Rbar Lbar hRT hAR hLR hAL hidx hcomm hgen
  have hS : (S:Subgroup P).map P.subtype=(T:Subgroup G) := map_subgroupOf_eq_of_le hP.2
  have hm := map_mono (f:=P.subtype) hcentral
  rw [←omegaOneCenterAmbient_map_injective P.subtype P.subtype_injective,
    ←ChapterB.thompsonJ_map_injective P.subtype P.subtype_injective,hS] at hm
  have hcR := hm.trans (by
    simpa only [Subgroup.coe_map] using
      Subgroup.map_centralizer_le_centralizer_image (pResidual 2 P:Set P) P.subtype)
  exact hmove (le_centralizer_iff.mp ((h.thompsonFixed_le_omega T hM).trans hcR))

/-- The seed centralizer normalizes the original fixed subgroup whenever the
prepared module lies in its two-core. -/
theorem PreparedChosenModule.thompsonFixed_normalized_of_le_seed_centralizer_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T:Subgroup G)≤centralizer (localModule T M:Set G))
    (h : PreparedChosenModule T M V)
    (hVC : V≤(centralizer (centralInvolutions T:Set G)).pCoreIn 2) :
    centralizer (centralInvolutions T:Set G)≤normalizer (thompsonFixed T V:Set G) :=
  (h.thompsonFixed_residual_iff_normalizes hG T hM hJ).mp
    (h.thompsonFixed_residual_of_le_seed_centralizer_core hG T hempty hM hJ hVC)

/-- Containment in the actual partner core also gives the original residual
and normalization conclusions, with no condition on the partner-module size. -/
theorem PreparedChosenModule.thompsonFixed_residual_normalized_of_le_partner_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T:Subgroup G)≤centralizer (localModule T M:Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T:Set G))={Mc})
    (h : PreparedChosenModule T M V) (hVQ : V≤Mc.pCoreIn 2) :
    (pResidual 2 (centralizer (centralInvolutions T:Set G))).map
      (centralizer (centralInvolutions T:Set G)).subtype≤
        centralizer (thompsonFixed T V:Set G) ∧
      centralizer (centralInvolutions T:Set G)≤normalizer (thompsonFixed T V:Set G) := by
  let C := centralizer (centralInvolutions T:Set G)
  have hMc : Mc∈maximalTwoLocalOvergroups C := by
    rw [hu]
    exact Set.mem_singleton Mc
  have hTC : (T:Subgroup G)≤C := by
    intro t ht z hz
    exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm
  have hTMc : (T:Subgroup G)≤Mc := hTC.trans hMc.2
  have hQT : Mc.pCoreIn 2≤(T:Subgroup G) := by
    have hh := pCoreIn_le_sylow Mc (T.subtype hTMc)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc] at hh
  have hCQ : C≤normalizer (Mc.pCoreIn 2:Set G) := hMc.2.trans
    (Mc.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc)))
  have hQC : Mc.pCoreIn 2≤C.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 Mc) (hQT.trans hTC) hCQ
  have hr := h.thompsonFixed_residual_of_le_seed_centralizer_core hG T hempty hM hJ
    (hVQ.trans hQC)
  exact ⟨hr,(h.thompsonFixed_residual_iff_normalizes hG T hM hJ).mp hr⟩

end CFSG.Quasithin.Chapter15.Section01
