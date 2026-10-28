module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorCentralizerCubic
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorNormalizerSylow
public import Theory.GroupTheory.FrattiniFixedFreeDisplacement

/-! The residual of the actual point-factor normalizer generates U by
commutators. Its dotted cubic is fixed-free on U/Z(U); Frattini generation
then recovers U itself. Consequently the residual fixes exactly the marked
central involution in A. Source: Aschbacher–Smith 14.3.19. -/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

theorem factor_point_residual_fixed_of_full_orthogonal
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
    ⁅F.U,Y⁆=F.U ∧ F.U≤Y ∧ A⊓centralizer (Y:Set G)=F.Vi 1 := by
  let N := F.H⊓normalizer (A:Set G)
  let Y := (pResidual 2 N).map N.subtype
  let C := centralizer (F.terminalDot A:Set F.TerminalHdot)
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  have hNH:N≤F.H := inf_le_left
  have hRT:(F.I₂ (sourceResidual M Mc)).pCoreIn 2≤(T:Subgroup G) :=
    (parabolic_core_sylow_index_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hAH:A≤F.H := hAR.trans (hRT.trans (F.invariant 1))
  have hUQ:F.U≤F.H.pCoreIn 2 := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy _ _)
  have hUN:F.U≤N := le_inf F.U_le_H (hUQ.trans (le_sup_right.trans hAN))
  obtain ⟨hNC,⟨eC⟩⟩ := elementary_factor_normalizer_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A
    hAR hVA hAc hc8 ((pCoreIn_le 2 _).trans (le_sup_left.trans hAN))
  have hC12:Nat.card C=12 := by
    rw [Nat.card_congr eC.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Nat.card_prod,Fintype.card_perm,Nat.factorial]
  let f₀:N→*F.TerminalHdot := q.comp (inclusion hNH)
  have hf₀:f₀.range=C := by
    rw [MonoidHom.range_comp,inclusion_range]
    exact hNC
  let f:N→*C := f₀.codRestrict C (fun n=>hf₀ ▸ (show f₀ n∈f₀.range from ⟨n,rfl⟩))
  have hf:Function.Surjective f := by
    rintro ⟨c,hc⟩
    obtain ⟨n,hn⟩ := (show c∈f₀.range from hf₀.symm ▸ hc)
    exact ⟨n,Subtype.ext hn⟩
  obtain ⟨c,hc3⟩ := exists_prime_orderOf_dvd_card' (G:=C) 3 (by rw [hC12];decide)
  have hcm:c∈(pResidual 2 N).map f := by
    rw [map_pResidual_of_surjective 2 f hf]
    exact mem_pResidual_of_orderOf_coprime (by rw [hc3];decide)
  obtain ⟨b,hb,hbc⟩ := hcm
  have hbq:f₀ b=(c:F.TerminalHdot) := congrArg Subtype.val hbc
  have hbY:(b:G)∈Y := mem_map_of_mem N.subtype hb
  have hcpow:(c:F.TerminalHdot)^3=1 := by
    have hh:=pow_orderOf_eq_one c
    rw [hc3] at hh
    exact congrArg Subtype.val hh
  have hcne:(c:F.TerminalHdot)≠1 := by
    intro hh
    have he:c=1 := Subtype.ext hh
    rw [he,orderOf_one] at hc3
    contradiction
  let act:MulAut F.U := F.uAction (inclusion hNH b)
  have hfix:∀z:F.Uhat,quotientAut (center F.U) act z=z→z=1 := by
    intro z hz
    have hfixed:F.terminalRepresentation (c:F.TerminalHdot) (Additive.ofMul z)=Additive.ofMul z := by
      rw [←hbq]
      apply Additive.toMul.injective
      change F.terminalHatAction (inclusion hNH b) z=z
      exact hz
    exact elementary_factor_centralizer_cubic_fixed_free
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A
      hAR hAH hVA hc8 hAc c hcpow hcne c.property (Additive.ofMul z) hfixed
  let : IsExtraspecial 2 F.U := extraspecial_of_center_point F dg (by omega) hZ hne
  have hJU:⁅F.U,Y⁆≤F.U := le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le (pResidual 2 N)).trans (hNH.trans (le_normalizer_conjugateSpanBy _ _)))
  have hJY:⁅F.U,Y⁆≤Y := le_normalizer_iff_commutator_le_right.mp
    (hUN.trans (le_normalizer_embedded_pResidual 2 N))
  have hgen:(⁅F.U,Y⁆.subgroupOf F.U)=⊤ := by
    apply eq_top_of_fixedFree_quotient_displacements (center F.U)
      (by rw [IsExtraspecial.frattini_eq_center_two]) act hfix
    intro u
    change (b:G)*(u:G)*(b:G)⁻¹*(u:G)⁻¹∈⁅F.U,Y⁆
    rw [commutator_comm F.U Y]
    exact commutator_mem_commutator hbY u.property
  have hcomm:⁅F.U,Y⁆=F.U := by
    have hh:=congrArg (Subgroup.map F.U.subtype) hgen
    simpa only [map_subgroupOf_eq_of_le hJU,←MonoidHom.range_eq_map,F.U.range_subtype] using hh
  have hUY:F.U≤Y := hcomm ▸ hJY
  have hCAU:A⊓centralizer (F.U:Set G)=F.Vi 1 :=
    (factor_normalizer_sylow_of_full_orthogonal hG T hempty hM hu hmany hcard e hnot
      F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN).1
  have hHC:F.H≤centralizer (F.Vi 1:Set G) :=
    normalizer_le_centralizer_of_card_two (F.Vi 1) (by simpa using F.card 1 (by decide))
  refine ⟨hcomm,hUY,le_antisymm ?_ ?_⟩
  · exact (inf_le_inf_left A (centralizer_le hUY)).trans hCAU.le
  · exact le_inf ((F.le_seed 1).trans hVA)
      (le_centralizer_iff.mp ((map_subtype_le (pResidual 2 N)).trans (hNH.trans hHC)))

theorem source_factor_point_residual_fixed_of_solvable
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
    let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
    let Q := F.H.pCoreIn 2
    ∃ A:Subgroup G,
      A≤R ∧ rankTwoSeed T M≤A ∧ IsElementaryAbelian 2 A ∧ Nat.card A=16 ∧
      Nat.card (A⊓F.U:Subgroup G)=8 ∧
      ∃ _hAN:F.I₂ (sourceResidual M Mc)⊔Q≤normalizer (A:Set G),
        let N := F.H⊓normalizer (A:Set G)
        let Y := (pResidual 2 N).map N.subtype
        ⁅F.U,Y⁆=F.U ∧ F.U≤Y ∧ A⊓centralizer (Y:Set G)=F.Vi 1 := by
  let h:=source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩:=rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ:=source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr:=source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  obtain ⟨_,A,hAR,hVA,hEA,hAc,hc8,hAN,_⟩:=source_factor_supplement_action_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  let := hEA
  exact ⟨A,hAR,hVA,hEA,hAc,hc8,hAN,factor_point_residual_fixed_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN⟩
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
