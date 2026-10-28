module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorGeneratedResidual
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorPointResidualAutomizer
public import Theory.GroupTheory.PCoreActionSplitting

/-!
# The original point residual has quaternion two-core

The literal terminal image of Y=O²(N_H(A)) has order three, while its kernel
is U. The kernel is therefore O₂(Y). The previously established equality
O²(RY)=Y identifies the two-core of this point-stabilizer residual as the
same original U. All maps remain in the original ambient group.

Source: Aschbacher–Smith 14.3.19(10), intrinsic marking for the U centralizer.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

theorem factor_point_residual_dot_card_of_full_orthogonal
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
    Nat.card (F.terminalDot Y)=3 := by
  intro N Y
  let C := centralizer (F.terminalDot A:Set F.TerminalHdot)
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  have hNH:N≤F.H := inf_le_left
  have hYH:Y≤F.H := (map_subtype_le _).trans hNH
  have hRA:(F.I₂ (sourceResidual M Mc)).pCoreIn 2≤normalizer (A:Set G) :=
    (pCoreIn_le 2 _).trans (le_sup_left.trans hAN)
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
  exact hYdotc

theorem factor_point_residual_core_of_full_orthogonal
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
    Y.pCoreIn 2=F.U := by
  intro N Y
  let Q := F.H.pCoreIn 2
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  have hNH:N≤F.H := inf_le_left
  have hYH:Y≤F.H := (map_subtype_le _).trans hNH
  have hUY:F.U≤Y := (factor_point_residual_fixed_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN).2.1
  have hUQ:F.U≤Q := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy _ _)
  have hJQ := (factor_point_residual_geometry_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN).1
  have hYQ:Y⊓Q=F.U := le_antisymm
    ((inf_le_inf_right Q (show Y≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔Y from le_sup_right)).trans hJQ.le)
    (le_inf hUY hUQ)
  let f:Y→*F.TerminalHdot := q.comp (inclusion hYH)
  have hqker:q.ker=pCore 2 F.H := by
    rw [QuotientGroup.ker_mk',terminal_kernel_of_center_point F dg hZ]
  have hk:f.ker=F.U.subgroupOf Y := by
    ext x
    change inclusion hYH x∈q.ker ↔ (x:G)∈F.U
    rw [hqker]
    constructor
    · intro hx
      exact hYQ.le ⟨x.property,mem_map_of_mem F.H.subtype hx⟩
    · intro hx
      obtain ⟨y,hy,he⟩ := hUQ hx
      exact (show y=inclusion hYH x from Subtype.ext he) ▸ hy
  have hc:Nat.card f.range=3 := by
    have he:f.range=F.terminalDot Y := by
      rw [MonoidHom.range_comp,inclusion_range]
      rfl
    rw [he]
    exact factor_point_residual_dot_card_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN
  have hcore:pCore 2 f.range=⊥ := by
    apply Subgroup.card_eq_one.mp
    have hd : Nat.card (pCore 2 f.range)∣3 := hc ▸ (pCore 2 f.range).card_subgroup_dvd_card
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p:=2) (G:=f.range)).exists_card_eq
    have hcop : Nat.Coprime (2^n) 3 := (by decide : Nat.Coprime 2 3).pow_left n
    exact Nat.eq_one_of_dvd_coprimes hcop (hn ▸ dvd_refl _) hd
  have hp:IsPGroup 2 f.ker := hk.symm ▸ dg.two.comap_subtype
  have he := f.ker_eq_pCore_of_range_core_eq_bot 2 hp hcore
  change (pCore 2 Y).map Y.subtype=F.U
  rw [←he,hk,map_subgroupOf_eq_of_le hUY]

theorem factor_point_join_residual_core_of_full_orthogonal
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
    ((pResidual 2 J).map J.subtype).pCoreIn 2=F.U := by
  intro N Y J
  rw [(factor_generated_residual_geometry_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN).1]
  exact factor_point_residual_core_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN

theorem source_factor_point_residual_core_of_solvable
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
    Y.pCoreIn 2=F.U := by
  let h:=source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩:=rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ:=source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr:=source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  exact factor_point_residual_core_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN

theorem source_factor_point_join_residual_core_of_solvable
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
    ((pResidual 2 J).map J.subtype).pCoreIn 2=F.U := by
  let h:=source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩:=rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ:=source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr:=source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  exact factor_point_join_residual_core_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
