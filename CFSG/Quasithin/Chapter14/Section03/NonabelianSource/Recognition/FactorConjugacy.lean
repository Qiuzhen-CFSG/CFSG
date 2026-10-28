module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorMovement

/-!
# Conjugate maximal elementary factors in the original section

An elementary factor containing an involution in W outside V meets the
actual U in a singular section strictly larger than the seed. If T
normalized that factor, its image in U/Z(U) would be a Sylow-invariant
singular plane, contradicting the full orthogonal action. Thus T moves the
factor to the other maximal elementary factor.

Source: Aschbacher--Smith 14.3.18(4), printed p.996.
-/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G:Type*} [Group G] [Finite G]


omit [Finite G] in
private theorem involution_outside_of_generation (W V:Subgroup G)
    (hgen:closure {x:W|x^2=1}=⊤) (hn:¬IsMulCommutative W)
    [IsElementaryAbelian 2 V] : ∃x:W,x^2=1 ∧ (x:G)∉V := by
  by_contra hbad
  have hh:closure {x:W|x^2=1}≤V.subgroupOf W := by
    apply (closure_le _).mpr
    intro x hx
    by_contra hxV
    exact hbad ⟨x,hx,hxV⟩
  have hWV:W≤V := by
    intro x hx
    exact hh (hgen.symm ▸ (show (⟨x,hx⟩:W)∈(⊤:Subgroup W) from mem_top _))
  apply hn
  exact le_centralizer_iff_isMulCommutative.mp
    (hWV.trans (V.le_centralizer.trans (centralizer_le hWV)))

private theorem conjugate_factor_eq_other
    (T R K A B:Subgroup G) [IsElementaryAbelian 2 A]
    (hTR:T≤normalizer (R:Set G)) (hAR:A≤R)
    (hKA:K≤normalizer (A:Set G))
    (hn:¬T≤normalizer (A:Set G)) (hc:Nat.card A=Nat.card B)
    (hmax:∀E:Subgroup G,IsElementaryAbelian 2 E→E≤R→E≤A ∨ E≤B) :
    ∃t:G,t∈T ∧ t∉K ∧ conjugate A t=B := by
  have hex:∃t:G,t∈T ∧ t∉normalizer (A:Set G) := by
    by_contra hbad
    apply hn
    intro t ht
    by_contra hn
    exact hbad ⟨t,ht,hn⟩
  obtain ⟨t,ht,htn⟩ := hex
  let :IsElementaryAbelian 2 (conjugate A t) :=
    IsElementaryAbelian.map (MulAut.conj t⁻¹).toMonoidHom
  have hct:conjugate A t≤R := conjugate_le_of_normalizes hAR t (hTR ht)
  have hcc:Nat.card (conjugate A t)=Nat.card A :=
    card_map_of_injective (MulAut.conj t⁻¹).injective
  have he:conjugate A t=B := by
    rcases hmax (conjugate A t) inferInstance hct with ha|hb
    · exact (htn ((conjugate_eq_iff A t).mp
        (eq_of_le_of_card_ge ha (by rw [hcc])))).elim
    · exact eq_of_le_of_card_ge hb (by rw [hcc,hc])
  exact ⟨t,ht,fun htk=>htn (hKA htk),he⟩

theorem conjugate_maximal_elementary_factors_of_full_orthogonal
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
    ∃ (A B : Subgroup G) (t:G),
      A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2 ∧ B≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2 ∧
      rankTwoSeed T M≤A ∧ rankTwoSeed T M≤B ∧
      IsElementaryAbelian 2 A ∧ IsElementaryAbelian 2 B ∧
      Nat.card A=16 ∧ Nat.card B=16 ∧ A⊓B=rankTwoSeed T M ∧
      A⊔B=(F.I₂ (sourceResidual M Mc)).pCoreIn 2 ∧
      Nat.card ((F.I₂ (sourceResidual M Mc)).pCoreIn 2)=64 ∧
      F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G) ∧
      F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (B:Set G) ∧
      (∀E:Subgroup G,IsElementaryAbelian 2 E→E≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2→E≤A ∨ E≤B) ∧
      t∈(T:Subgroup G) ∧ t∉(F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔F.H.pCoreIn 2 ∧
      conjugate A t=B := by
  obtain ⟨A,B,hAR,hBR,hVA,hVB,hEA,hEB,hAc,hBc,hi,hs,hRc,hAN,hBN,hmax⟩ :=
    maximal_elementary_factors_of_full_orthogonal hG T hempty hM hu hmany hcard e hnot
      F dg hZ hne g hgP hgH hr
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let L := sourceResidual M Mc
  let :Fact (IsPGroup 2 F.U):=⟨dg.two⟩
  have hPhi:(frattini F.U).map F.U.subtype=F.Vi 1 := by
    rw [dg.frattini_point]
    exact map_subgroupOf_eq_of_le ((F.le_seed 1).trans (le_conjugateSpanBy _ _))
  have hcomm:⁅F.U,F.U⁆≤F.Vi 1 := by
    rw [←F.U.map_subtype_commutator]
    exact (map_mono (f:=F.U.subtype) (commutator_le_frattini_of_isPGroup (p:=2))).trans hPhi.le
  have hsquare:∀u∈F.U,u^2∈F.Vi 1 := fun u hu=>
    hPhi ▸ mem_map_of_mem F.U.subtype (pth_power_mem_frattini_of_isPGroup (p:=2) (⟨u,hu⟩:F.U))
  have hspan:F.U=conjugateSpanBy (F.Vi 2) F.H := by rw [F.last];rfl
  obtain ⟨_,_,_,_,hIG,hIN,_,_,_,_,hcore,_,_⟩ :=
    F.binary_generation (by decide) L h.L_normalizes_seed (h.binarySeedAction_surjective F)
      h.centralizer hcomm hsquare hspan hne g hgP hgH
  have hTR:(T:Subgroup G)≤normalizer ((F.I₂ L).pCoreIn 2:Set G) :=
    ((F.invariant 2).trans ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN)).trans
      (normalizer_le_normalizer_characteristic_image (F.I₂ L) (pCore 2 (F.I₂ L)))
  have hW:F.W≤(F.I₂ L).pCoreIn 2 := by
    rw [←hcore]
    exact le_inf (inf_le_left.trans (le_conjugateSpanBy _ _)) inf_le_right
  obtain ⟨dU⟩ := quaternion_closure_of_full_orthogonal F dg hZ hne hr
  obtain ⟨z,hz,hnz,hWz⟩ := W_as_involution_centralizer_of_center_point F hZ
  have hnW:¬IsMulCommutative F.W :=
    QuaternionCentralProductData.ambient_involution_centralizer_overgroup_noncommutative
      F.U F.W dU z hz hnz hWz.symm.le
  obtain ⟨x,hx,hxV⟩ := involution_outside_of_generation F.W (rankTwoSeed T M)
    (W_involution_generated_of_full_orthogonal F dg hZ hne hr) hnW
  let :IsElementaryAbelian 2 (zpowers (x:G)) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (congrArg (fun y:F.W=>(y:G)) hx)
  have hxR:zpowers (x:G)≤(F.I₂ L).pCoreIn 2 :=
    zpowers_le.mpr (hW x.property)
  let := hEA
  let := hEB
  have hRN:(F.I₂ L).pCoreIn 2⊔F.H.pCoreIn 2≤F.I₂ L⊔F.H.pCoreIn 2 :=
    sup_le_sup (pCoreIn_le 2 _) le_rfl
  rcases hmax (zpowers (x:G)) inferInstance hxR with hxA|hxB
  · have hnotT := elementary_factor_not_sylow_normalized_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
      A hVA (x:G) (hxA (mem_zpowers _)) x.property.1 hxV
    obtain ⟨t,ht,htR,he⟩ := conjugate_factor_eq_other (T:Subgroup G) _
      ((F.I₂ L).pCoreIn 2⊔F.H.pCoreIn 2) A B hTR hAR (hRN.trans hAN)
      hnotT (hAc.trans hBc.symm) hmax
    exact ⟨A,B,t,hAR,hBR,hVA,hVB,hEA,hEB,hAc,hBc,hi,hs,hRc,hAN,hBN,hmax,ht,htR,he⟩
  · have hnotT := elementary_factor_not_sylow_normalized_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
      B hVB (x:G) (hxB (mem_zpowers _)) x.property.1 hxV
    have hmax':∀E:Subgroup G,IsElementaryAbelian 2 E→E≤(F.I₂ L).pCoreIn 2→E≤B ∨ E≤A :=
      fun E hE hER=>(hmax E hE hER).symm
    obtain ⟨t,ht,htR,he⟩ := conjugate_factor_eq_other (T:Subgroup G) _
      ((F.I₂ L).pCoreIn 2⊔F.H.pCoreIn 2) B A hTR hBR (hRN.trans hBN)
      hnotT (hBc.trans hAc.symm) hmax'
    exact ⟨B,A,t,hBR,hAR,hVB,hVA,hEB,hEA,hBc,hAc,by rw [inf_comm,hi],
      by rw [sup_comm,hs],hRc,hBN,hAN,hmax',ht,htR,he⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
