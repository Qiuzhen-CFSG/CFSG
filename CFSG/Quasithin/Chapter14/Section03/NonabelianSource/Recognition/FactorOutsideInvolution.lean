module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ParabolicResidual
public import Theory.GroupAction.CoprimeIndexTwoInvolution
public import Theory.GroupTheory.PCoreRestriction

/-!
# The outside involution in the original index-two branch

Let P=LT and R=O₂(I₂). The original parabolic factorization makes
R normal in P, so R lies in Q=O₂(P), and Q meets I₂ precisely in R.
The original S₃ quotient gives |T:Q|=2. Since |RU:R|=2, the source
antecedent |T:RU|=2 gives |Q:R|=2. The cubic element already constructed
in L acts without fixed points on R. Coprime fixed-point lifting in Q
therefore produces an involution outside RU.

The solvable source adapter derives all of this local geometry from the
original Chapter 14 input. Only the printed index-two antecedent remains.
Source: Aschbacher--Smith, Lemma 14.3.21(1), printed p.998.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem core_relIndex_sylow (T : Sylow 2 G) (P : Subgroup G)
    (hTP : (T : Subgroup G) ≤ P)
    (hc : Nat.card (P ⧸ pCore 2 P)=6) :
    (P.pCoreIn 2).relIndex (T : Subgroup G)=2 := by
  let q := QuotientGroup.mk' (pCore 2 P)
  let S : Sylow 2 (P ⧸ pCore 2 P) :=
    (T.subtype hTP).mapSurjective (f:=q) (QuotientGroup.mk'_surjective _)
  have hSc : Nat.card S=2 := by
    rw [Sylow.card_eq_multiplicity,hc]
    decide +kernel
  have hi : (pCore 2 P).relIndex ((T : Subgroup G).subgroupOf P)=2 := by
    rw [←QuotientGroup.ker_mk' (pCore 2 P),relIndex_ker]
    exact hSc
  have he := relIndex_map_map_of_injective (pCore 2 P)
    ((T : Subgroup G).subgroupOf P) P.subtype_injective
  rw [map_subgroupOf_eq_of_le hTP] at he
  exact he.trans hi

omit [Finite G] in
private theorem normalized_join_index (R U : Subgroup G)
    (hn : U ≤ normalizer (R : Set G)) :
    R.relIndex (R ⊔ U)=R.relIndex U := by
  let J := R ⊔ U
  let : (R.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le R.le_normalizer hn)
  have hh := relIndex_sup_left (U.subgroupOf J) (R.subgroupOf J)
  rw [←subgroupOf_sup (show R≤J from le_sup_left) (show U≤J from le_sup_right),
    relIndex_subgroupOf (show R⊔U≤J from le_rfl),
    relIndex_subgroupOf (show U≤J from le_sup_right)] at hh
  exact hh

theorem outside_involution_of_full_orthogonal
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
    (hr : ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤)
    (hi : (((F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.U).subgroupOf
      (T : Subgroup G)).index=2) :
    ∃ t∈(T : Subgroup G), orderOf t=2 ∧
      t∉(F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.U := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let L := sourceResidual M Mc
  let I := F.I₂ L
  let P := F.P L
  let R := I.pCoreIn 2
  let Q := P.pCoreIn 2
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
  obtain ⟨_,_,_,_,hIG,hIN,_,_,hfactor,_,hcore,hindex,_⟩ :=
    F.binary_generation (by decide) L h.L_normalizes_seed (h.binarySeedAction_surjective F)
      h.centralizer hcomm hsquare hspan hne g hgP hgH
  have hIP : I≤P := le_sup_right.trans hfactor.ge
  have hUI : F.U≤I := le_conjugateSpanBy _ _
  have hTP : (T : Subgroup G)≤P := by
    change (T : Subgroup G)≤F.P L
    rw [F.P_rankTwo]
    exact le_sup_right
  have hPI : P≤normalizer (I : Set G) :=
    (F.P_le_G₂ (by decide) L h.L_normalizes_seed).trans
      ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN)
  have hPR : P≤normalizer (R : Set G) := hPI.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hPQ : P≤normalizer (Q : Set G) := P.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hRQ : R≤Q := pCoreIn_mono_of_normalizes hIP hPI
  have hQT : Q≤(T : Subgroup G) := by
    have hh := pCoreIn_le_sylow P (T.subtype hTP)
    change Q≤((T : Subgroup G).subgroupOf P).map P.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTP] at hh
  have hUT : F.U≤(T : Subgroup G) := by
    have hh := pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))
    change F.H.pCoreIn 2≤((T : Subgroup G).subgroupOf F.H).map F.H.subtype at hh
    rw [map_subgroupOf_eq_of_le (show (T : Subgroup G)≤F.H from F.invariant 1)] at hh
    exact (le_pCoreIn_of_normalizes dg.two F.U_le_H
      (le_normalizer_conjugateSpanBy _ _)).trans hh
  have hRJ : R≤R⊔F.U := le_sup_left
  have hJT : R⊔F.U≤(T : Subgroup G) := sup_le (hRQ.trans hQT) hUT
  have hcut : Q⊓(R⊔F.U)≤R := by
    intro x hx
    exact inf_pCoreIn_le_of_le 2 hIP
      ⟨(sup_le (pCoreIn_le 2 I) hUI) hx.2,hx.1⟩
  have hWU : F.U⊓R=F.W := by
    change F.U⊓(F.I₂ L).pCoreIn 2=F.W
    rw [←hcore,←inf_assoc,inf_eq_left.mpr hUI]
    rfl
  have hRJindex : R.relIndex (R⊔F.U)=2 := by
    rw [normalized_join_index R F.U (hUI.trans (hIP.trans hPR)),
      ←inf_relIndex_right,inf_comm R F.U,hWU]
    exact hindex
  have hQindex : Q.relIndex (T : Subgroup G)=2 := by
    apply core_relIndex_sylow T P hTP
    obtain ⟨eP⟩ := h.quotient_model
    have hc := Nat.card_congr eP.toEquiv
    change Nat.card ((L⊔(T : Subgroup G) : Subgroup G) ⧸ pCore 2 (L⊔(T : Subgroup G) : Subgroup G))=_ at hc
    change Nat.card ((F.P L) ⧸ pCore 2 (F.P L))=6
    rw [F.P_rankTwo,hc]
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hRQindex : (R.subgroupOf Q).index=2 := by
    have ha := relIndex_mul_relIndex R (R⊔F.U) (T : Subgroup G) hRJ hJT
    have hb := relIndex_mul_relIndex R Q (T : Subgroup G) hRQ hQT
    change (R⊔F.U).relIndex (T : Subgroup G)=2 at hi
    rw [hRJindex,hi] at ha
    rw [hQindex] at hb
    change R.relIndex Q=2
    omega
  let : (R.subgroupOf Q).Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 P).trans hPR)
  obtain ⟨hres,_,_,c,hcL,hc3,hfixed⟩ :=
    parabolic_residual_core_structure_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
  have hLI : L≤I := hres.ge.trans (map_subtype_le _)
  let X := zpowers c
  have hXP : X≤P := (zpowers_le.mpr hcL).trans (hLI.trans hIP)
  have hX : IsPGroup 3 X := IsPGroup.of_card (n:=1) (by
    change Nat.card (zpowers c)=3^1
    rw [Nat.card_zpowers,hc3,pow_one])
  have hfixedX : R⊓centralizer (X : Set G)=⊥ := by
    apply le_antisymm _ bot_le
    rw [←hfixed]
    apply inf_le_inf le_rfl (centralizer_le _)
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact mem_zpowers _
  obtain ⟨t,ht,ht2,htout,_⟩ :=
    exists_involution_outside_join_of_coprime_fixed_kernel T R F.U Q X
      (isPGroup_pCoreIn 2 P) hX hQT hcut (hXP.trans hPQ) (hXP.trans hPR)
      hRQindex hfixedX
  exact ⟨t,ht,ht2,htout⟩


/-- Original 14.3.21(1), with the literal index-two antecedent retained. -/
theorem source_outside_involution_of_solvable
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
    (hs : Group.IsSolvable F.TerminalHdot)
    (hi : (((F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.U).subgroupOf
      (T : Subgroup G)).index=2) :
    ∃ t∈(T : Subgroup G), orderOf t=2 ∧
      t∉(F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.U := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  exact outside_involution_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr hi

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
