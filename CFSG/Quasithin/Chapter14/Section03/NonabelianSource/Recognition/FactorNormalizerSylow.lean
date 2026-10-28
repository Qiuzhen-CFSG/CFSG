module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ParabolicNormalizer
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorSupplementAction
public import Theory.GroupTheory.RelativeSylowNormalizer
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# Sylow automizers of the original elementary factor

The two local cores generate a two-subgroup whose dotted image has order
four. The actual local normalizer has dotted order twelve, so this subgroup
is Sylow in the local normalizer. Its fixed subgroup in the elementary
factor is exactly the marked point; every element normalizing both must
therefore lie in the point normalizer. Relative normalizer control promotes
the same subgroup to Sylow in the full factor normalizer. Taking the literal
conjugation image gives the full automizer assertion.

Source: Aschbacher--Smith, 14.3.19(3), printed p.997. The final wrapper
retains the original source prefix and explicit terminal solvability.
-/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

theorem factor_normalizer_sylow_of_full_orthogonal
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
    let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
    let Q := F.H.pCoreIn 2
    A⊓centralizer (F.U:Set G)=F.Vi 1 ∧
    A⊓centralizer ((R⊔Q:Subgroup G):Set G)=F.Vi 1 ∧
    ∃ P:Sylow 2 (normalizer (A:Set G)),
      (P:Subgroup (normalizer (A:Set G))).map (normalizer (A:Set G)).subtype=R⊔Q := by
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let Q := F.H.pCoreIn 2
  let N := normalizer (A:Set G)
  let K := F.H⊓N
  let S := R⊔Q
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  have hRT:R≤(T:Subgroup G) := (parabolic_core_sylow_index_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hTH:(T:Subgroup G)≤F.H := F.invariant 1
  have hQT:Q≤(T:Subgroup G) := by
    have hh := pCoreIn_le_sylow F.H (T.subtype hTH)
    change Q≤((T:Subgroup G).subgroupOf F.H).map F.H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTH] at hh
  have hST:S≤(T:Subgroup G) := sup_le hRT hQT
  have hSH:S≤F.H := hST.trans hTH
  have hAH:A≤F.H := hAR.trans (hRT.trans hTH)
  have hSN:S≤N := (sup_le_sup (pCoreIn_le 2 _) le_rfl).trans hAN
  have hSK:S≤K := le_inf hSH hSN
  have hUQ:F.U≤Q := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy _ _)
  have hqker:q.ker=pCore 2 F.H := by
    rw [QuotientGroup.ker_mk',terminal_kernel_of_center_point F dg hZ]
  obtain ⟨hRQ,_,_,_,hRdot⟩ := parabolic_core_intersection_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
  have hCAU:A⊓centralizer (F.U:Set G)=F.Vi 1 := by
    apply le_antisymm
    · intro a ha
      let aH:F.H := ⟨a,hAH ha.1⟩
      have ha0:F.uAction aH=1 := by
        ext u
        change a*(u:G)*a⁻¹=(u:G)
        rw [←mem_centralizer_iff.mp ha.2 (u:G) u.property,mul_inv_cancel_right]
      have hak:aH∈F.terminalHatAction.ker := by
        change quotientAut (center F.U) (F.uAction aH)=1
        rw [ha0,map_one]
      rw [terminal_kernel_of_center_point F dg hZ] at hak
      have haQ:a∈Q := mem_map_of_mem F.H.subtype hak
      have haU:a∈F.U := (show a∈F.W from hRQ ▸ ⟨hAR ha.1,haQ⟩).1
      rw [←hZ,ZU,centerIn_eq_inf_centralizer]
      exact ⟨haU,ha.2⟩
    · refine le_inf ((F.le_seed 1).trans hVA) ?_
      rw [←hZ,ZU,centerIn_eq_inf_centralizer]
      exact inf_le_right
  have hHC:F.H≤centralizer (F.Vi 1:Set G) :=
    normalizer_le_centralizer_of_card_two (F.Vi 1) (by simpa using F.card 1 (by decide))
  have hCAS:A⊓centralizer (S:Set G)=F.Vi 1 := by
    apply le_antisymm
    · exact (inf_le_inf_left A (centralizer_le (hUQ.trans le_sup_right))).trans hCAU.le
    · exact le_inf ((F.le_seed 1).trans hVA)
        (le_centralizer_iff.mp (hSH.trans hHC))
  obtain ⟨hNK,⟨eN⟩⟩ := elementary_factor_normalizer_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A
    hAR hVA hAc hc8 ((pCoreIn_le 2 _).trans (le_sup_left.trans hAN))
  have hK12:Nat.card (F.terminalDot K)=12 := by
    rw [hNK,Nat.card_congr eN.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hQdot:F.terminalDot Q=⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [hqker]
    intro a ha
    obtain ⟨b,hb,he⟩ := ha
    exact (show b=a from Subtype.ext he) ▸ hb
  have hSdot:F.terminalDot S=F.terminalDot R := by
    change ((R⊔Q).subgroupOf F.H).map q=(R.subgroupOf F.H).map q
    rw [subgroupOf_sup (hRT.trans hTH) (pCoreIn_le 2 F.H),Subgroup.map_sup]
    change F.terminalDot R⊔F.terminalDot Q=F.terminalDot R
    rw [hQdot,sup_bot_eq]
  have hidxDot:(F.terminalDot S).relIndex (F.terminalDot K)=3 := by
    have hh:=relIndex_mul_card_of_le (show F.terminalDot S≤F.terminalDot K from
      map_mono (fun _ hx=>hSK hx))
    rw [hSdot,hRdot,hK12] at hh
    rw [hSdot]
    omega
  have hkS:q.ker≤S.subgroupOf F.H := by
    rw [hqker]
    intro a ha
    exact (show Q≤S from le_sup_right) (mem_map_of_mem F.H.subtype ha)
  have hkK:q.ker≤K.subgroupOf F.H := hkS.trans (fun _ hx=>hSK hx)
  have hidx:S.relIndex K=3 := by
    have hh:=relIndex_map_map q (S.subgroupOf F.H) (K.subgroupOf F.H)
    rw [sup_of_le_left hkS,sup_of_le_left hkK] at hh
    have he:=relIndex_map_map_of_injective (S.subgroupOf F.H) (K.subgroupOf F.H) F.H.subtype_injective
    rw [map_subgroupOf_eq_of_le hSH,map_subgroupOf_eq_of_le inf_le_left] at he
    exact he.trans (hh.symm.trans hidxDot)
  have hlocal:∃P:Sylow 2 K,(P:Subgroup K).map K.subtype=S := by
    have hp:IsPGroup 2 S := T.isPGroup'.to_le hST
    have hi:¬2∣(S.subgroupOf K).index := by change ¬2∣S.relIndex K;rw [hidx];decide
    exact ⟨hp.comap_subtype.toSylow hi,map_subgroupOf_eq_of_le hSK⟩
  have hn:N⊓normalizer (S:Set G)≤K := by
    intro x hx
    refine ⟨?_,hx.1⟩
    have hxc:x∈normalizer (centralizer (S:Set G):Set G) :=
      normalizer_le_normalizer_centralizer S hx.2
    have hxfix:=inf_normalizer_le_normalizer_inf ⟨hx.1,hxc⟩
    rw [hCAS] at hxfix
    exact hxfix
  exact ⟨hCAU,hCAS,exists_sylow_eq_of_relative_normalizer_le hlocal inf_le_right hn⟩

theorem factor_automizer_sylow_of_full_orthogonal
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
    let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
    let Q := F.H.pCoreIn 2
    (T:Subgroup G)⊓normalizer (A:Set G)=R⊔Q ∧
    ∃ hSN:R⊔Q≤normalizer (A:Set G),
      ∃ P:Sylow 2 A.normalizerMonoidHom.range,
        (P:Subgroup A.normalizerMonoidHom.range).map A.normalizerMonoidHom.range.subtype=
          (A.normalizerMonoidHom.comp (inclusion hSN)).range := by
  let S := (F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔F.H.pCoreIn 2
  let N := normalizer (A:Set G)
  let f := A.normalizerMonoidHom
  have hSN:S≤N := (sup_le_sup (pCoreIn_le 2 _) le_rfl).trans hAN
  obtain ⟨_,_,P,hP⟩ := factor_normalizer_sylow_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN
  have hPeq:(P:Subgroup N)=S.subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hSN]
  have hRT:((F.I₂ (sourceResidual M Mc)).pCoreIn 2)≤(T:Subgroup G) :=
    (parabolic_core_sylow_index_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hTH:(T:Subgroup G)≤F.H := F.invariant 1
  have hQT:F.H.pCoreIn 2≤(T:Subgroup G) := by
    have hh:=pCoreIn_le_sylow F.H (T.subtype hTH)
    change F.H.pCoreIn 2≤((T:Subgroup G).subgroupOf F.H).map F.H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTH] at hh
  have hST:S≤(T:Subgroup G) := sup_le hRT hQT
  have hTN:(T:Subgroup G)⊓N=S := by
    have hp:IsPGroup 2 (((T:Subgroup G)⊓N).subgroupOf N) :=
      (T.isPGroup'.to_le (show (T:Subgroup G)⊓N≤(T:Subgroup G) from inf_le_left)).comap_subtype
    have he:=P.is_maximal' hp (show (P:Subgroup N)≤((T:Subgroup G)⊓N).subgroupOf N from by
      rw [hPeq];exact fun x hx=>⟨hST hx,x.property⟩)
    have hm:=congrArg (fun B:Subgroup N=>B.map N.subtype) he
    rw [map_subgroupOf_eq_of_le inf_le_right,hP] at hm
    exact hm
  refine ⟨hTN,hSN,P.mapSurjective f.rangeRestrict_surjective,?_⟩
  change ((P:Subgroup N).map f.rangeRestrict).map f.range.subtype=
    (f.comp (inclusion hSN)).range
  rw [Subgroup.map_map,hPeq]
  change (S.subgroupOf N).map f=(f.comp (inclusion hSN)).range
  ext a
  constructor
  · rintro ⟨n,hn,rfl⟩
    exact ⟨⟨n,hn⟩,rfl⟩
  · rintro ⟨n,rfl⟩
    exact ⟨inclusion hSN n,n.property,rfl⟩

theorem source_factor_automizer_sylow_of_solvable
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
      (T:Subgroup G)⊓normalizer (A:Set G)=R⊔Q ∧
      ∃ hSN:R⊔Q≤normalizer (A:Set G),
        ∃ P:Sylow 2 A.normalizerMonoidHom.range,
          (P:Subgroup A.normalizerMonoidHom.range).map A.normalizerMonoidHom.range.subtype=
            (A.normalizerMonoidHom.comp (inclusion hSN)).range := by
  let h:=source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩:=rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ:=source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr:=source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  obtain ⟨_,A,hAR,hVA,hEA,hAc,hc8,hAN,_⟩:=source_factor_supplement_action_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  let := hEA
  exact ⟨A,hAR,hVA,hEA,hAc,hc8,factor_automizer_sylow_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN⟩
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
