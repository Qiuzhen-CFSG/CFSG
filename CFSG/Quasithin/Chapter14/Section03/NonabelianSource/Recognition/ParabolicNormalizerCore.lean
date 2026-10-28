module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ParabolicNormalizerIntersection
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ParabolicNormalizerQuaternion
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.NormalSylowResidual
public import Theory.GroupTheory.PResidual.NormalizerCore
public import Theory.GroupTheory.PResidual.FiniteImage

/-! The original closure is precisely the two-core of the embedded two-residual
of H. The parabolic core gives a normal four-group in the terminal Sylow action;
its normal closure contains the nine-group residual. Consequently O²(H)
centralizes Q/U. A central Sylow argument gives the upper core inclusion, while
coprime generation of U gives the lower inclusion. Source:14.3.18(5). -/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem twoResidual_core_eq_U_of_full_orthogonal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (dg : ClosureGeometry F) (hZ : F.ZU=F.Vi 1) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hr : ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤) :
    F.U=((pResidual 2 F.H).map F.H.subtype).pCoreIn 2 := by
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let Q := F.H.pCoreIn 2
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (f:=q) (QuotientGroup.mk'_surjective _)
  obtain ⟨hRQ,hcomm,hRP,hnP,hRc⟩ := parabolic_core_intersection_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
  have hneR : F.terminalDot R≠⊥ := by
    intro he
    rw [he,Subgroup.card_bot] at hRc
    omega
  obtain ⟨hclosure,hrescard,_⟩ :=
    ChapterG.Section09.FittingRecognition.Four.full_orthogonal_normal_sylow_residual
      F.terminalRepresentation hr P (F.terminalDot R) hRP hnP hneR
  have hqker : q.ker=pCore 2 F.H := by
    rw [QuotientGroup.ker_mk',terminal_kernel_of_center_point F dg hZ]
  let RH := R.subgroupOf F.H
  let UH := F.U.subgroupOf F.H
  have hUH : UH.map F.H.subtype=F.U := map_subgroupOf_eq_of_le F.U_le_H
  have hUQ : F.U≤Q := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy _ _)
  have hUcore : UH≤pCore 2 F.H := by
    intro x hx
    obtain ⟨a,ha,he⟩ := hUQ hx
    exact (show a=x from Subtype.ext he) ▸ ha
  let : UH.Normal := (normal_subgroupOf_iff_le_normalizer F.U_le_H).mpr
    (le_normalizer_conjugateSpanBy _ _)
  have hQcomm : ⁅pCore 2 F.H,RH⁆≤UH := by
    intro x hx
    have hm := mem_map_of_mem F.H.subtype hx
    rw [map_commutator] at hm
    have hh : ⁅Q,R⁆≤F.U := by rw [commutator_comm];exact hcomm
    exact hh ((commutator_mono le_rfl (by rw [subgroupOf_map_subtype];exact inf_le_left)) hm)
  have hcover : (pResidual 2 F.H).map q≤(normalClosure (RH:Set F.H)).map q := by
    rw [map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _),
      map_normalClosure RH q (QuotientGroup.mk'_surjective _)]
    change pResidual 2 F.TerminalHdot≤normalClosure (F.terminalDot R:Set F.TerminalHdot)
    rw [←hclosure]
    exact map_subtype_le _
  have hc : ⁅pResidual 2 F.H,pCore 2 F.H⁆≤UH :=
    commutator_pResidual_core_le_of_normalClosure_cover_map UH RH hQcomm q hqker hcover
  have hodd : Odd (Nat.card ((pResidual 2 F.H).map q)) := by
    rw [map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _),hrescard]
    decide
  have hupper : pResidual 2 F.H⊓pCore 2 F.H≤UH :=
    pResidual_inf_pCore_le_of_central_mod_map UH hUcore hc q hqker hodd
  let K := (pResidual 2 F.H).map F.H.subtype
  have hKQ : K.pCoreIn 2≤Q := pCoreIn_mono_of_normalizes
    (map_subtype_le _) (le_normalizer_embedded_pResidual 2 F.H)
  have hKU : K.pCoreIn 2≤F.U := by
    have hi : K.pCoreIn 2≤K⊓Q := le_inf (pCoreIn_le 2 K) hKQ
    have hm := map_mono (f:=F.H.subtype) hupper
    rw [map_inf _ _ F.H.subtype F.H.subtype_injective,hUH] at hm
    exact hi.trans hm
  have hUK : F.U≤K := U_le_embedded_twoResidual_of_full_orthogonal F dg hZ hne hr
  have hUC : F.U≤K.pCoreIn 2 := le_pCoreIn_of_normalizes dg.two hUK
    ((map_subtype_le (pResidual 2 F.H)).trans (le_normalizer_conjugateSpanBy _ _))
  exact le_antisymm hUC hKU

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
