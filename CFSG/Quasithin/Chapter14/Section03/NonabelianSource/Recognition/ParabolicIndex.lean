module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.OriginalSolvable
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.OrthogonalOrder
public import Theory.GroupTheory.SylowOvergroupCharacteristic

/-!
# The actual parabolic core has index two after adjoining the local core

The binary parabolic core is the join of the two plane centralizers.
The first is in the original local two-core; the second has order sixteen
and meets that core in the seed four-group. Hence its dotted image has
order four. The full orthogonal quotient has Sylow two-subgroups of order
eight, so adjoining the local core gives index two in the original Sylow
subgroup. Normality inside the seed normalizer supplies core containment
in that Sylow subgroup before the index calculation.

Source: Aschbacher--Smith 14.3.18(3), printed pp.995--996. The source
solvable wrapper discharges the orthogonal and center hypotheses internally.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
theorem parabolic_core_sylow_index_of_full_orthogonal
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
    (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ≤ (T : Subgroup G) ∧
    (((F.I₂ (sourceResidual M Mc)).pCoreIn 2) ⊔ F.H.pCoreIn 2).relIndex (T : Subgroup G)=2 := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let L := sourceResidual M Mc
  let R := (F.I₂ L).pCoreIn 2
  let Q := F.H.pCoreIn 2
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
  have hidx : (F.terminalDot R).relIndex (P:Subgroup F.TerminalHdot)=2 := by
    have hRc : Nat.card (F.terminalDot R)=4 := by rw [hRdot,hXdotc]
    have hh := relIndex_mul_card_of_le hRP
    rw [hRc,hPc] at hh
    omega
  have hkT : q.ker≤(T:Subgroup G).subgroupOf F.H := by
    rw [hqker]
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype hTH)
  have hkmap : q.ker.map F.H.subtype=Q := by rw [hqker]; rfl
  have he := relIndex_map_map q (R.subgroupOf F.H) ((T:Subgroup G).subgroupOf F.H)
  rw [sup_of_le_left hkT] at he
  have he' := relIndex_map_map_of_injective (R.subgroupOf F.H⊔q.ker)
    ((T:Subgroup G).subgroupOf F.H) F.H.subtype_injective
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hRH,hkmap,map_subgroupOf_eq_of_le hTH] at he'
  exact ⟨hRT,he'.trans (he.symm.trans hidx)⟩


theorem source_parabolic_core_sylow_index_of_solvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot) :
    (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ≤ (T : Subgroup G) ∧
    (((F.I₂ (sourceResidual M Mc)).pCoreIn 2) ⊔ F.H.pCoreIn 2).relIndex (T : Subgroup G)=2 := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,hx,B,v,hyp,cover⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  exact parabolic_core_sylow_index_of_full_orthogonal hG T hempty hM hu hmany hcard e hnot
    F dg hZ hne g hgP hgH hr

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
