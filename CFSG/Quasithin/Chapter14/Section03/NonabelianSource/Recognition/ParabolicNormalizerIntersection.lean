module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ParabolicIndex
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.OriginalMaximality
public import Theory.GroupTheory.PResidual.CentralCore
public import Theory.GroupTheory.WreathTwoResidual
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-! The original parabolic core meets Q in W. Normalization of both elementary
factors by Q therefore gives the valid commutator bound [R,Q]≤W≤U.
This is the geometric input to the residual-core argument in14.3.18(5). -/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
theorem parabolic_core_intersection_of_full_orthogonal
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
    let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
    let Q := F.H.pCoreIn 2
    let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
      (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
    R⊓Q=F.W ∧ ⁅R,Q⁆≤F.U ∧ F.terminalDot R≤(P:Subgroup F.TerminalHdot) ∧
      (P:Subgroup F.TerminalHdot)≤normalizer (F.terminalDot R:Set F.TerminalHdot) ∧
      Nat.card (F.terminalDot R)=4 := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let L := sourceResidual M Mc
  let R := (F.I₂ L).pCoreIn 2
  let Q := F.H.pCoreIn 2
  obtain ⟨A,B,hAR,hBR,hVA,hVB,hEA,hEB,hAc,hBc,hi,hs,hRc,hAN,hBN,hmax⟩ :=
    maximal_elementary_factors_of_full_orthogonal hG T hempty hM hu hmany hcard e hnot
      F dg hZ hne g hgP hgH hr
  have hQR : Q≤normalizer (R:Set G) := by
    change Q≤normalizer ((F.I₂ (sourceResidual M Mc)).pCoreIn 2:Set G)
    rw [←hs]
    exact (le_inf (le_sup_right.trans hAN) (le_sup_right.trans hBN)).trans
      (normalizer_inf_normalizer_le_normalizer_sup A B)
  let : Fact (IsPGroup 2 F.U) := ⟨dg.two⟩
  have hPhi : (frattini F.U).map F.U.subtype=F.Vi 1 := by
    rw [dg.frattini_point]
    exact map_subgroupOf_eq_of_le ((F.le_seed 1).trans (le_conjugateSpanBy _ _))
  have hcomm : ⁅F.U,F.U⁆≤F.Vi 1 := by
    rw [←F.U.map_subtype_commutator]
    exact (map_mono (f:=F.U.subtype) (commutator_le_frattini_of_isPGroup (p:=2))).trans hPhi.le
  have hsquare : ∀u∈F.U,u^2∈F.Vi 1 := fun u hu=>
    hPhi ▸ mem_map_of_mem F.U.subtype (pth_power_mem_frattini_of_isPGroup (p:=2) (⟨u,hu⟩:F.U))
  have hspan : F.U=conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  obtain ⟨e₀,_,hgen,_,hIG,hIN,_,_,hfactor,hPH,hcore,hindex,_⟩ :=
    F.binary_generation (by decide) L h.L_normalizes_seed (h.binarySeedAction_surjective F)
      h.centralizer hcomm hsquare hspan hne g hgP hgH
  have hsplit : R=F.W⊔F.X g :=
    F.binary_core_factorization L g hgP hfactor hPH hgen.symm e₀ hcore hindex
  have hRN : F.Gi 2≤normalizer (R:Set G) :=
    ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN).trans
      (normalizer_le_normalizer_characteristic_image (F.I₂ L) (pCore 2 (F.I₂ L)))
  have hRT : R≤(T:Subgroup G) := normalized_pSubgroup_le_sylow T (F.Gi 2) R
    (F.invariant 2) ((pCoreIn_le 2 (F.I₂ L)).trans hIG) hRN (isPGroup_pCoreIn 2 (F.I₂ L))
  have hTH : (T:Subgroup G)≤F.H := F.invariant 1
  have hQT : Q≤(T:Subgroup G) := by
    have hh := pCoreIn_le_sylow F.H (T.subtype hTH)
    change Q≤((T:Subgroup G).subgroupOf F.H).map F.H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTH] at hh
  have hRH : R≤F.H := hRT.trans hTH
  have hQH : Q≤F.H := pCoreIn_le 2 F.H
  have hUQ : F.U≤Q := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy _ _)
  have hWH : F.W≤F.H := inf_le_left.trans F.U_le_H
  have hXH : F.X g≤F.H := F.X_le_H g (F.P_le_G₂ (by decide) L h.L_normalizes_seed hgP)
  obtain ⟨dU⟩ := quaternion_closure_of_full_orthogonal F dg hZ hne hr
  have hWc : Nat.card F.W=16 := by
    have hh := relIndex_mul_card_of_le (show F.W≤F.U from inf_le_left)
    rw [hindex,dU.card] at hh
    omega
  have hXc : Nat.card (F.X g)=16 := by
    change Nat.card (F.W.map (MulAut.conj g⁻¹).toMonoidHom)=16
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective,hWc]
  have hVx : rankTwoSeed T M≤F.X g :=
    (F.seed_le_E_of_normalizes g (F.P_le_seed_normalizer L h.L_normalizes_seed hgP)).trans inf_le_right
  have hVc : Nat.card (rankTwoSeed T M)=4 := by
    simpa only [F.last,show (2:ℕ)^2=4 from rfl] using F.card 2 le_rfl
  have hQX : Q⊓F.X g=rankTwoSeed T M := by
    have hh := core_inf_conjugate_U_of_full_orthogonal hG T hempty hM hu hmany hcard e hnot
      F dg hZ hne g hgP hgH hr
    rw [←conjugate_U_inf_H_eq_X F h.L_normalizes_seed g hgP hgH]
    rw [←inf_assoc,inf_comm Q,inf_assoc,inf_eq_left.mpr hQH,inf_comm]
    exact hh
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  have hqker : q.ker=pCore 2 F.H := by
    rw [QuotientGroup.ker_mk',terminal_kernel_of_center_point F dg hZ]
  have hXdotc : Nat.card (F.terminalDot (F.X g))=4 := by
    change Nat.card ((F.X g).subgroupOf F.H |>.map q)=4
    rw [←relIndex_ker _ q,hqker]
    have he := relIndex_map_map_of_injective (pCore 2 F.H) ((F.X g).subgroupOf F.H) F.H.subtype_injective
    rw [map_subgroupOf_eq_of_le hXH] at he
    change Q.relIndex (F.X g)=(pCore 2 F.H).relIndex ((F.X g).subgroupOf F.H) at he
    rw [←he,←inf_relIndex_right,hQX]
    have hh := relIndex_mul_card_of_le hVx
    rw [hVc,hXc] at hh
    omega
  have hWdot : F.terminalDot F.W=⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [hqker]
    intro w hw
    obtain ⟨a,ha,he⟩ := (hUQ ((show F.W≤F.U from inf_le_left) hw))
    exact (show a=w from Subtype.ext he) ▸ ha
  have hRdot : F.terminalDot R=F.terminalDot (F.X g) := by
    change (R.subgroupOf F.H).map q=((F.X g).subgroupOf F.H).map q
    rw [hsplit,subgroupOf_sup hWH hXH,Subgroup.map_sup]
    change F.terminalDot F.W⊔F.terminalDot (F.X g)=F.terminalDot (F.X g)
    rw [hWdot,bot_sup_eq]
  let P : Sylow 2 F.TerminalHdot := (T.subtype hTH).mapSurjective
    (f:=q) (QuotientGroup.mk'_surjective _)
  have hPc : Nat.card P=8 := by
    obtain ⟨a,f,ha⟩ := hr
    have hc : Nat.card F.TerminalHdot=72 :=
      (Nat.card_congr (a.trans topEquiv).toEquiv).trans ChapterG.Section09.FittingRecognition.Four.card_orthogonalFour
    rw [Sylow.card_eq_multiplicity,hc,show 72=2^3*9 by decide,
      Nat.factorization_mul (by decide) (by decide),Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization,Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2∣9)]
  have hRP : F.terminalDot R≤(P:Subgroup F.TerminalHdot) :=
    map_mono (show R.subgroupOf F.H≤(T:Subgroup G).subgroupOf F.H from fun _ hx=>hRT hx)
  have hRI : Q.relIndex R=4 := by
    have he := relIndex_map_map_of_injective (pCore 2 F.H) (R.subgroupOf F.H)
      F.H.subtype_injective
    rw [map_subgroupOf_eq_of_le hRH] at he
    change Q.relIndex R=(pCore 2 F.H).relIndex (R.subgroupOf F.H) at he
    rw [he,←hqker,relIndex_ker]
    change Nat.card (F.terminalDot R)=4
    rw [hRdot,hXdotc]
  have hRQc : Nat.card (R⊓Q:Subgroup G)=16 := by
    rw [inf_comm R Q]
    have hh := relIndex_mul_card_of_le (show R⊓Q≤R from inf_le_left)
    rw [inf_comm R Q,inf_relIndex_right,hRI,hRc] at hh
    omega
  have hWQ : F.W≤Q := (show F.W≤F.U from inf_le_left).trans hUQ
  have hWR : F.W≤R := le_sup_left.trans hsplit.ge
  have hRQ : R⊓Q=F.W := (eq_of_le_of_card_ge (le_inf hWR hWQ)
    (by rw [hWc,hRQc])).symm
  have hRHnorm : R≤normalizer (Q:Set G) := hRH.trans
    (F.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H)))
  have hRQcomm : ⁅R,Q⁆≤F.U := by
    have hi : ⁅R,Q⁆≤R⊓Q := le_inf
      (le_normalizer_iff_commutator_le_left.mp hQR)
      (by rw [commutator_comm];exact le_normalizer_iff_commutator_le_left.mp hRHnorm)
    rw [hRQ] at hi
    exact hi.trans inf_le_left
  have hTR : (T:Subgroup G)≤normalizer (R:Set G) := (F.invariant 2).trans hRN
  have hnH : (T:Subgroup G).subgroupOf F.H≤normalizer (R.subgroupOf F.H:Set F.H) := by
    intro t ht
    apply mem_normalizer_iff.mpr
    intro r
    change (r:G)∈R ↔ (t:G)*(r:G)*(t:G)⁻¹∈R
    exact (mem_normalizer_iff.mp (hTR ht)) (r:G)
  have hnP : (P:Subgroup F.TerminalHdot)≤normalizer (F.terminalDot R:Set F.TerminalHdot) :=
    (map_mono hnH).trans (le_normalizer_map _)
  exact ⟨hRQ,hRQcomm,hRP,hnP,by rw [hRdot,hXdotc]⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
