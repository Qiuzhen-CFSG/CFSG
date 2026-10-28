module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorPointResidual
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorAutomizersOvergroup
public import Theory.GroupTheory.PResidual.PGroupFactor
public import Theory.SpecificGroups.SymmetricTwoResidual

/-! The original point-normalizer residual Y has dotted image of order three.
The dotted parabolic core is a disjoint four-group, while source18(5) bounds
Y∩Q by U and residual displacement supplies U≤Y. The actual product RY
therefore has kernel U and dotted order twelve, hence order384. The literal
conjugation action on the chosen factor A is consequently S₄.

Source: Aschbacher–Smith, 14.3.19(4), printed p.997. The final wrapper retains
the chosen A and derives the full orthogonal setup from terminal solvability. -/

public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

theorem factor_point_residual_geometry_of_full_orthogonal
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
    (A:Subgroup G) [IsElementaryAbelian 2 A]
    (hAR:A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hVA:rankTwoSeed T M≤A) (hAc:Nat.card A=16)
    (hc8:Nat.card (A⊓F.U:Subgroup G)=8)
    (hAN:F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G)) :
    let N := F.H⊓normalizer (A:Set G)
    let Y := (pResidual 2 N).map N.subtype
    let J := (F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔Y
    J⊓F.H.pCoreIn 2=F.U ∧ Nat.card J=384 := by
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let Q := F.H.pCoreIn 2
  let N := F.H⊓normalizer (A:Set G)
  let Y := (pResidual 2 N).map N.subtype
  let J := R⊔Y
  let K := (pResidual 2 F.H).map F.H.subtype
  let C := centralizer (F.terminalDot A:Set F.TerminalHdot)
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  have hRT:R≤(T:Subgroup G) := (parabolic_core_sylow_index_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hRH:R≤F.H := hRT.trans (F.invariant 1)
  have hRA:R≤normalizer (A:Set G) := (pCoreIn_le 2 _).trans (le_sup_left.trans hAN)
  have hRN:R≤N := le_inf hRH hRA
  have hNH:N≤F.H := inf_le_left
  have hYN:Y≤N := map_subtype_le _
  have hYH:Y≤F.H := hYN.trans hNH
  have hJH:J≤F.H := sup_le hRH hYH
  have hUQ:F.U≤Q := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy _ _)
  have hUY:F.U≤Y := (factor_point_residual_fixed_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A hAR hVA hAc hc8 hAN).2.1
  have hYU:Y⊓Q≤F.U := by
    have hcore:=twoResidual_core_eq_U_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    exact (inf_le_inf_right Q (embedded_pResidual_mono 2 hNH)).trans
      ((inf_pCoreIn_le_of_le 2 (show K≤F.H from map_subtype_le _)).trans hcore.ge)
  have hqker:q.ker=pCore 2 F.H := by
    rw [QuotientGroup.ker_mk',terminal_kernel_of_center_point F dg hZ]
  obtain ⟨hRQ,_,_,_,hRdot⟩ := parabolic_core_intersection_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
  obtain ⟨hNC,⟨eC⟩⟩ := elementary_factor_normalizer_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A
    hAR hVA hAc hc8 hRA
  let f₀:N→*F.TerminalHdot := q.comp (inclusion hNH)
  have hf₀:f₀.range=C := by
    rw [MonoidHom.range_comp,inclusion_range]
    exact hNC
  let f:N→*C := f₀.codRestrict C (fun n=>hf₀ ▸ (show f₀ n∈f₀.range from ⟨n,rfl⟩))
  have hf:Function.Surjective f := by
    rintro ⟨c,hc⟩
    obtain ⟨n,hn⟩ := (show c∈f₀.range from hf₀.symm ▸ hc)
    exact ⟨n,Subtype.ext hn⟩
  have hYsub:Y.subgroupOf F.H=(pResidual 2 N).map (inclusion hNH) := by
    apply Subgroup.map_injective F.H.subtype_injective
    rw [map_subgroupOf_eq_of_le hYH,map_map]
    rfl
  have hYdot:F.terminalDot Y=(pResidual 2 C).map C.subtype := by
    change (Y.subgroupOf F.H).map q=_
    rw [hYsub,map_map]
    change (pResidual 2 N).map (C.subtype.comp f)=_
    rw [←map_map,map_pResidual_of_surjective 2 f hf]
  have hCres:Nat.card (pResidual 2 C)=3 := by
    have htwo:IsPGroup 2 (Multiplicative (ZMod 2)) := IsPGroup.of_card (n:=1) (by
      simp [Nat.card_eq_fintype_card])
    rw [Nat.card_congr (pResidualEquivOfPGroupFactor 2 eC htwo).toEquiv,
      Equiv.Perm.twoResidual_eq_alternating,nat_card_alternatingGroup,Nat.card_fin]
    rfl
  have hYdotc:Nat.card (F.terminalDot Y)=3 := by
    rw [hYdot,card_map_of_injective C.subtype_injective,hCres]
  have hd:Disjoint (F.terminalDot R) (F.terminalDot Y) :=
    disjoint_of_coprime_natCard (by rw [hRdot,hYdotc];decide)
  have hRY:R≤normalizer (Y:Set G) := hRN.trans (le_normalizer_embedded_pResidual 2 N)
  have hJU:J⊓Q≤F.U := by
    rintro x ⟨hxJ,hxQ⟩
    have hx':x∈(R:Set G)*(Y:Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right R Y hRY]
      exact hxJ
    obtain ⟨r,hrR,y,hyY,he⟩ := hx'
    change r*y=x at he
    have hxk:(⟨x,hJH hxJ⟩:F.H)∈q.ker := by
      rw [hqker]
      obtain ⟨b,hb,hbX⟩:=hxQ
      exact (show b=⟨x,hJH hxJ⟩ from Subtype.ext hbX) ▸ hb
    have hxq:q (⟨r,hRH hrR⟩*⟨y,hYH hyY⟩)=1 := by
      rw [show (⟨r,hRH hrR⟩:F.H)*⟨y,hYH hyY⟩=⟨x,hJH hxJ⟩ from Subtype.ext he]
      exact hxk
    have hrY:q ⟨r,hRH hrR⟩∈F.terminalDot Y := by
      have heq:q ⟨r,hRH hrR⟩=(q ⟨y,hYH hyY⟩)⁻¹ := eq_inv_of_mul_eq_one_left (by
        rw [←map_mul];exact hxq)
      rw [heq]
      exact (F.terminalDot Y).inv_mem (mem_map_of_mem q hyY)
    have hrq:q ⟨r,hRH hrR⟩=1 := by
      have hh:=hd.le_bot (show q ⟨r,hRH hrR⟩∈F.terminalDot R⊓F.terminalDot Y from
        ⟨mem_map_of_mem q hrR,hrY⟩)
      exact hh
    have hrQ:r∈Q := by
      have hh:(⟨r,hRH hrR⟩:F.H)∈q.ker := hrq
      rw [hqker] at hh
      exact mem_map_of_mem F.H.subtype hh
    have hrU:r∈F.U := (show r∈F.W from hRQ ▸ ⟨hrR,hrQ⟩).1
    have hyQ:y∈Q := by
      have hh:=Q.mul_mem (Q.inv_mem hrQ) hxQ
      rw [←he,inv_mul_cancel_left] at hh
      exact hh
    exact he ▸ F.U.mul_mem hrU (hYU ⟨hyY,hyQ⟩)
  have hJQ:J⊓Q=F.U := le_antisymm hJU (le_inf (hUY.trans le_sup_right) hUQ)
  have hRdC:F.terminalDot R≤C := by
    change F.terminalDot R≤centralizer (F.terminalDot A:Set F.TerminalHdot)
    rw [←hNC]
    exact map_mono (fun _ hx=>hRN hx)
  have hRdY:F.terminalDot R≤normalizer (F.terminalDot Y:Set F.TerminalHdot) := by
    rw [hYdot]
    exact hRdC.trans (le_normalizer_embedded_pResidual 2 C)
  have hJdot:Nat.card (F.terminalDot J)=12 := by
    change Nat.card (((R⊔Y).subgroupOf F.H).map q)=12
    rw [subgroupOf_sup hRH hYH,Subgroup.map_sup]
    change Nat.card (F.terminalDot R⊔F.terminalDot Y:Subgroup F.TerminalHdot)=12
    rw [sup_comm,card_sup_eq_mul_of_normalizes_of_disjoint _ _ hRdY hd.symm,
      hYdotc,hRdot]
  have hind:F.U.relIndex J=12 := by
    change Nat.card ((J.subgroupOf F.H).map q)=12 at hJdot
    rw [←relIndex_ker _ q,hqker] at hJdot
    have he:=relIndex_map_map_of_injective (pCore 2 F.H) (J.subgroupOf F.H) F.H.subtype_injective
    rw [map_subgroupOf_eq_of_le hJH] at he
    change Q.relIndex J=(pCore 2 F.H).relIndex (J.subgroupOf F.H) at he
    rw [←he,←inf_relIndex_right,inf_comm Q J,hJQ] at hJdot
    exact hJdot
  obtain ⟨dU⟩ := quaternion_closure_of_full_orthogonal F dg hZ hne hr
  have hh:=relIndex_mul_card_of_le (show F.U≤J from hUY.trans le_sup_right)
  rw [hind,dU.card] at hh
  exact ⟨hJQ,hh.symm⟩

/-- The literal second symmetric-four actor, with both residual geometry
premises discharged from the original orthogonal source data. -/
theorem factor_point_residual_symmetric_automizer_of_full_orthogonal
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
    (A:Subgroup G) [IsElementaryAbelian 2 A]
    (hAR:A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hVA:rankTwoSeed T M≤A) (hAc:Nat.card A=16)
    (hc8:Nat.card (A⊓F.U:Subgroup G)=8)
    (hAN:F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G)) :
    let N := F.H⊓normalizer (A:Set G)
    let Y := (pResidual 2 N).map N.subtype
    let J := (F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔Y
    ∃hJA:J≤normalizer (A:Set G),
      Nat.card (A.normalizerMonoidHom.comp (inclusion hJA)).range=24 ∧
      Nonempty ((A.normalizerMonoidHom.comp (inclusion hJA)).range ≃* Equiv.Perm (Fin 4)) := by
  obtain ⟨hJQ,hJcard⟩ := factor_point_residual_geometry_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A hAR hVA hAc hc8 hAN
  exact factor_residual_normalizer_symmetric_automizer
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A hAR hVA hAc hc8 ((pCoreIn_le 2 _).trans (le_sup_left.trans hAN)) hJQ.le hJcard

/-- Terminal solvability supplies the full orthogonal setup without changing
the chosen factor or either literal residual and action homomorphism. -/
theorem source_factor_point_residual_symmetric_automizer_of_solvable
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
    (A:Subgroup G) [IsElementaryAbelian 2 A]
    (hAR:A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hVA:rankTwoSeed T M≤A) (hAc:Nat.card A=16)
    (hc8:Nat.card (A⊓F.U:Subgroup G)=8)
    (hAN:F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G)) :
    let N := F.H⊓normalizer (A:Set G)
    let Y := (pResidual 2 N).map N.subtype
    let J := (F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔Y
    ∃hJA:J≤normalizer (A:Set G),
      Nat.card (A.normalizerMonoidHom.comp (inclusion hJA)).range=24 ∧
      Nonempty ((A.normalizerMonoidHom.comp (inclusion hJA)).range ≃* Equiv.Perm (Fin 4)) := by
  let h:=source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩:=rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ:=source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr:=source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  exact factor_point_residual_symmetric_automizer_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A hAR hVA hAc hc8 hAN

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
