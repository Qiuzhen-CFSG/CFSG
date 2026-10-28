module
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.Involutions
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorBlockSplit
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorConjugacy
public import Theory.Representation.BinaryPermutation.SixTransitivity
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Transfer

/-!
# Involution fusion in the original rank-two block

The chosen maximal elementary factors A and B of R are conjugate in T.
The original K has its marked natural split A₆ coordinates, so all involutions
outside A form one K-class and hence fuse into B. Transitivity on A minus the
identity then fuses every involution in R U to the nonidentity point of the
flag. The final transfer consumer discharges this internal-fusion hypothesis.

Source: Aschbacher–Smith, Quasithin Groups, 14.3.21(3), printed p.998.
-/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem fusion_of_marked_split_conjugate_factor
    (A B K:Subgroup G) [IsElementaryAbelian 2 B] (hBK:B≤K)
    (eK:K≃*BinaryPermutation.SixNaturalSplit.Model)
    (he:(A.subgroupOf K).map eK.toMonoidHom=
      (SemidirectProduct.inl:BinaryPermutation.SixNaturalSplit.Vector→*
        BinaryPermutation.SixNaturalSplit.Model).range)
    (hBA:¬B≤A) (t:G) (ht:conjugate A t=B)
    (htrans:∀ a b:A,a≠1→b≠1→∃k∈K,k*(a:G)*k⁻¹=b)
    (z:G) (hz:z∈A) (hzne:z≠1) (x:G) (hx:x∈K) (hx2:x^2=1) (hxne:x≠1) :
    IsConj x z := by
  have hAfuse (a:G) (ha:a∈A) (hne:a≠1) : IsConj a z := by
    obtain ⟨k,_,hk⟩ := htrans ⟨a,ha⟩ ⟨z,hz⟩
      (fun hh=>hne (congrArg Subtype.val hh)) (fun hh=>hzne (congrArg Subtype.val hh))
    exact isConj_iff.mpr ⟨k,hk⟩
  by_cases hxa:x∈A
  · exact hAfuse x hxa hxne
  have hbex:∃b:G,b∈B ∧ b∉A := by
    by_contra hbad
    apply hBA
    intro b hb
    by_contra ha
    exact hbad ⟨b,hb,ha⟩
  obtain ⟨b,hbB,hbA⟩ := hbex
  have hb2:b^2=1 := elemPow_eq_one_of_isElementaryAbelian b hbB
  have hout (a:K) (ha:(a:G)∉A) : (eK a).right≠1 := by
    intro hh
    have hm:eK a∈(SemidirectProduct.inl:BinaryPermutation.SixNaturalSplit.Vector→*
      BinaryPermutation.SixNaturalSplit.Model).range := by
      rw [SemidirectProduct.range_inl_eq_ker_rightHom]
      exact hh
    rw [←he] at hm
    obtain ⟨c,hc,hce⟩ := hm
    exact ha ((eK.injective hce) ▸ hc)
  let xK:K:=⟨x,hx⟩
  let bK:K:=⟨b,hBK hbB⟩
  have hxb:IsConj x b := by
    have hm:=BinaryPermutation.SixNaturalSplit.outside_involutions_isConj
      (eK xK) (eK bK)
      (by
        have h:xK^2=1:=Subtype.ext hx2
        rw [←map_pow,h,map_one])
      (by
        have h:bK^2=1:=Subtype.ext hb2
        rw [←map_pow,h,map_one])
      (hout xK hxa) (hout bK hbA)
    have hh:=eK.symm.toMonoidHom.map_isConj hm
    have hh':IsConj xK bK := by simpa only [MulEquiv.coe_toMonoidHom,eK.symm_apply_apply] using hh
    exact K.subtype.map_isConj hh'
  have hbt:b∈conjugate A t := ht.symm ▸ hbB
  obtain ⟨a,ha,hab⟩ := hbt
  change t⁻¹*a*(t⁻¹)⁻¹=b at hab
  rw [inv_inv] at hab
  have hc:IsConj a b := isConj_iff.mpr ⟨t⁻¹,by simpa only [inv_inv] using hab⟩
  have hane:a≠1 := by
    intro hh
    subst a
    have hb:b=1 := by simpa using hab.symm
    exact hbA (hb ▸ A.one_mem)
  exact hxb.trans (hc.symm.trans (hAfuse a ha hane))

/-- All original RU involutions are fused to the nonidentity point of the flag. -/
theorem ru_involutions_fused_of_full_orthogonal
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
    ∀ z∈F.Vi 1,z≠1→∀ x∈(F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔F.U,
      orderOf x=2→IsConj z x := by
  obtain ⟨A,B,t,hAR,hBR,hVA,hVB,hEA,hEB,hAc,hBc,hi,hAB,hRc,hAN,hBN,hmax,htT,htR,ht⟩ :=
    conjugate_maximal_elementary_factors_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
  let := hEA
  let := hEB
  obtain ⟨hc8,_⟩ := elementary_factor_core_intersections_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A B hAR hBR hVA hVB hEA hEB hmax
  let N:=F.H⊓normalizer (A:Set G)
  let Y:=(pResidual 2 N).map N.subtype
  let K:=sourceResidual M Mc⊔Y
  have hRU:(F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔F.U≤K :=
    (factor_generated_residual_geometry_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN).2.2.1
  obtain ⟨hAK,qA,eK,_,he⟩ := factor_block_split_model_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN
  obtain ⟨hKA,eA,q,hq⟩ := factor_alternating_natural_action_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A B hAR hBR hVA hAc hc8 hAB hRc hAN
  have hBA:¬B≤A := by
    intro hh
    have hRA:(F.I₂ (sourceResidual M Mc)).pCoreIn 2=A := hAB.symm.trans (sup_eq_left.mpr hh)
    rw [hRA,hAc] at hRc
    contradiction
  intro z hz hzne x hx hxord
  exact (fusion_of_marked_split_conjugate_factor A B K
    (hBR.trans (le_sup_left.trans hRU)) eK he hBA t ht
    (BinaryPermutation.exists_conjugator_of_alternatingSix_natural_action A K hKA eA q hq)
    z (hVA (F.le_seed 1 hz)) hzne x (hRU hx)
    (hxord ▸ pow_orderOf_eq_one x) (by intro hh; simp [hh] at hxord)).symm

/-- Source 14.3.21(3) from the original solvable terminal hypotheses. -/
theorem source_ru_involutions_fused_of_solvable
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
    ∀ z∈F.Vi 1,z≠1→∀ x∈(F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔F.U,
      orderOf x=2→IsConj z x := by
  let h:=source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩:=rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ:=source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr:=source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  exact ru_involutions_fused_of_full_orthogonal hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr

/-- The transfer endpoint with its internal involution-fusion premise discharged. -/
theorem source_false_of_ru_fusion_of_solvable
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
    (z:G) (hz:z∈F.Vi 1) (hzne:z≠1)
    (hi:(((F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔F.U).subgroupOf (T:Subgroup G)).index=2)
    (hex:∃t∈(T:Subgroup G),orderOf t=2 ∧ t∉(F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔F.U)
    (hout:∀t∈(T:Subgroup G),orderOf t=2→t∉(F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔F.U→¬IsConj z t) :
    False := by
  exact NonabelianSource.false_of_ru_fusion hG T _ F.U z hi hex hout
    (source_ru_involutions_fused_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs z hz hzne)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
