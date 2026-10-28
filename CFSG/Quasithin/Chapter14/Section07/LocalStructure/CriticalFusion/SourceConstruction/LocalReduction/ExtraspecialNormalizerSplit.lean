module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizerSylow
public import Theory.GroupTheory.SylowLocalCore
public import Theory.GroupTheory.SylowThreeCubic
public import Theory.GroupTheory.PCoreNormalizerAction.SylowKernel
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.GroupTheory.DetectedNormalCubic
public import Theory.GroupTheory.PPrimeCoreSubgroup
public import FeitThompson.BGsection1.PLengthLemmas

/-!
# Splitting the original three-Sylow normalizer factor

For the chosen B in N_G(K), the intersection B₁ = B ∩ L₁ is a normal
cubic in B_M = N_B(R₁). Its action on L/O₂(L) is faithful. The automorphism
group of that quotient has three-part three, so B₁ splits off the literal
kernel B₂ = C_{B_M}(L/O₂(L)). The ambient three-rank bound makes B₂ cyclic.
Since B ∩ C_N(K/O₂(K)) is cyclic and contains B₁, the same detection proves
that intersection is exactly B₁. Consequently the original residual
centralizer C is L₁ O_{3′}(C), with quotient of order three.

The source application constructs B using the repaired inner-kernel Frattini
factorization and retains the original group, flag and quotient actions.
It does not assume Data. The rank argument excluding B₂ and the subsequent
Baumann centralizer control remain necessary for N_G(K) = H.

Source: Aschbacher–Smith 14.7.21(1), printed pp.1049–1050,
refs/quasithin.pdf. The literal product is proved without claiming C R₁
normal in N_G(K).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The literal intersection of any original normalizer three-Sylow with
L₁ is a Sylow of L₁ and has order three. -/
theorem extraspecial_normalizer_point_three_sylow
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (B : Sylow 3 (normalizer (K F : Set G))) :
    let B₀ := (B : Subgroup _).map (normalizer (K F : Set G)).subtype
    IsSylowIn 3 (B₀ ⊓ F.Li L 1) (F.Li L 1) ∧
      Nat.card (B₀ ⊓ F.Li L 1 : Subgroup G) = 3 := by
  obtain ⟨S,hS⟩ := B.exists_map_subtype_eq_inf_of_normalizes
    ((pointResidual_le F).trans (K F).le_normalizer)
    (extraspecial_normalizer_normalizes_point h hab structural previous faithful he)
  refine ⟨⟨S,hS⟩,?_⟩
  rw [←hS,card_map_of_injective (F.Li L 1).subtype_injective]
  exact card_sylow_three_of_two_group_index_three (pCore 2 (F.Li L 1)) pCore_isPGroup
    (pointResidual_core_quotient_card h structural) S

private theorem original_quotient_aut_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    Nat.card (MulAut (L ⧸ pCore 2 L)) = 336 := by
  let := h.chosen.elementary
  let e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL :=
    h.naturalMarking.quotientEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
  rw [Nat.card_congr (MulAut.congr (e.trans Matrix.PSL3Two.equiv)).toEquiv]
  exact Matrix.PSL3Two.Automorphisms.card_aut

private theorem original_quotient_center
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    center (L ⧸ pCore 2 L) = ⊥ := by
  let := h.chosen.elementary
  let e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL :=
    h.naturalMarking.quotientEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
  apply bot_unique
  intro x hx
  have hz : e x ∈ center Matrix.PSL3Two.SL := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx z)
  rw [Matrix.PSL3Two.center_eq_bot] at hz
  exact e.injective (hz.trans e.map_one.symm)

private theorem original_three_action_image_bound
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (X : Subgroup G) (hX : IsPGroup 3 X) (hXL : X ≤ normalizer (L : Set G)) :
    Nat.card ((pCoreNormalizerAction 2 L).comp (inclusion hXL)).range ≤ 3 := by
  let f := (pCoreNormalizerAction 2 L).comp (inclusion hXL)
  obtain ⟨S,hS⟩ := (hX.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  have hc : Nat.card S = 3 := by
    rw [S.card_eq_multiplicity,original_quotient_aut_card h]
    decide +kernel
  exact (Nat.card_le_card_of_injective (inclusion hS) (inclusion_injective hS)).trans_eq hc

private theorem original_three_action_detects
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (X A : Subgroup G) (hX : IsPGroup 3 X) (hXL : X ≤ normalizer (L : Set G))
    (hAL : A ≤ L) :
    Function.Injective (((pCoreNormalizerAction 2 L).comp (inclusion hXL)).comp
      (A.subgroupOf X).subtype) := by
  let f := (pCoreNormalizerAction 2 L).comp (inclusion hXL)
  have hd : Disjoint X (L.pCoreIn 2) :=
    hX.disjoint_of_coprime (isPGroup_pCoreIn 2 L) (by decide)
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  have hm : ((x : X) : G) ∈ pCoreActionKernelIn 2 L (normalizer (L : Set G)) ⊓ L := by
    exact ⟨⟨hXL x.val.property,inclusion hXL x.val,hx,rfl⟩,hAL x.property⟩
  rw [pCoreActionKernelIn_inf_eq_core L (normalizer (L : Set G)) L.le_normalizer
    (original_quotient_center h)] at hm
  exact Subtype.ext (Subtype.ext (hd.le_bot ⟨x.val.property,hm⟩))

/-- The original normalizer factor splits over the detected point cubic;
the cyclic residual-centralizer Sylow is exactly that cubic. -/
theorem extraspecial_normalizer_three_sylow_split
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (B : Sylow 3 (normalizer (K F : Set G)))
    (hBCM : ((B : Subgroup _).map (normalizer (K F : Set G)).subtype) ⊓
      normalizerResidualCentralizer F ≤
      ((B : Subgroup _).map (normalizer (K F : Set G)).subtype) ⊓
        normalizer (F.Ri L 1 : Set G))
    (hBML : ((B : Subgroup _).map (normalizer (K F : Set G)).subtype) ⊓
      normalizer (F.Ri L 1 : Set G) ≤ normalizer (L : Set G)) :
    let B₀ := (B : Subgroup _).map (normalizer (K F : Set G)).subtype
    let B₁ := B₀ ⊓ F.Li L 1
    let B_M := B₀ ⊓ normalizer (F.Ri L 1 : Set G)
    let B₂ := pCoreActionKernelIn 2 L B_M
    Nat.card B₁ = 3 ∧ B₀ ⊓ normalizerResidualCentralizer F = B₁ ∧
      B_M = B₁ ⊔ B₂ ∧ Disjoint B₁ B₂ ∧
      B₁ ≤ centralizer (B₂ : Set G) ∧ IsCyclic B₂ := by
  let N := normalizer (K F : Set G)
  let C := normalizerResidualCentralizer F
  let B₀ := (B : Subgroup N).map N.subtype
  let A := B₀ ⊓ F.Li L 1
  let X := B₀ ⊓ normalizer (F.Ri L 1 : Set G)
  let D := pCoreActionKernelIn 2 L X
  have hB : IsPGroup 3 B₀ := B.isPGroup'.map N.subtype
  have hX : IsPGroup 3 X := hB.to_le inf_le_left
  have hXN : X ≤ N := inf_le_left.trans (map_subtype_le _)
  have hAC : A ≤ B₀ ⊓ C := inf_le_inf_left _
    (extraspecial_point_le_residualCentralizer h hab structural previous faithful he)
  have hAX : A ≤ X := hAC.trans hBCM
  have hAc : Nat.card A = 3 :=
    (extraspecial_normalizer_point_three_sylow h hab structural previous faithful he B).2
  have hXA : X ≤ normalizer (A : Set G) :=
    (le_inf (inf_le_left.trans B₀.le_normalizer)
      (hXN.trans (extraspecial_normalizer_normalizes_point h hab structural previous faithful he))).trans
      inf_normalizer_le_normalizer_inf
  let A' := A.subgroupOf X
  let : A'.Normal := normal_subgroupOf_of_le_normalizer hXA
  have hA'c : Nat.card A' = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAX).toEquiv).trans hAc
  let f := (pCoreNormalizerAction 2 L).comp (inclusion hBML)
  have hi : Function.Injective (f.comp A'.subtype) :=
    original_three_action_detects h X A hX hBML
      (inf_le_right.trans ((F.Li_le L 1).trans inf_le_left))
  have hr : Nat.card f.range ≤ 3 := original_three_action_image_bound h X hX hBML
  obtain ⟨hgen,hd,hz⟩ := detected_normal_cubic_product hX A' hA'c f hi hr
  have hD : D = f.ker.map X.subtype := pCoreActionKernelIn_eq_map_ker 2 L X hBML
  have hsplit : X = A ⊔ D := by
    have hh := congrArg (Subgroup.map X.subtype) hgen
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hAX,←hD,
      ←MonoidHom.range_eq_map,X.range_subtype] at hh
    exact hh.symm
  have hdis : Disjoint A D := by
    rw [hD,←map_subgroupOf_eq_of_le hAX]
    exact disjoint_map X.subtype_injective hd
  have hcentral : A ≤ centralizer (D : Set G) := by
    intro a ha c hc
    rw [hD] at hc
    obtain ⟨x,hx,rfl⟩ := hc
    exact congrArg Subtype.val (mem_center_iff.mp (hz (show (⟨a,hAX ha⟩ : X) ∈ A' from ha)) x)
  have hrX : primeRank 3 X ≤ 2 :=
    (primeRank_le_of_injective 3 (inclusion hXN) (inclusion_injective hXN)).trans
      (extraspecial_normalizer_threeRanks d h hab structural previous faithful he).1.le
  have hcyc : IsCyclic D := by
    rw [hD]
    let := detected_normal_cubic_kernel_cyclic hX hrX A' hA'c f hi hr
    exact isCyclic_of_surjective (X.subtype.subgroupMap f.ker) (X.subtype.subgroupMap_surjective f.ker)
  have hBC : B₀ ⊓ C = A := by
    obtain ⟨S,hS⟩ := B.exists_map_subtype_eq_inf_of_normalizes
      (show C ≤ N from map_subtype_le _) normalizerResidualCentralizer_normalizes
    have hc : IsCyclic (B₀ ⊓ C : Subgroup G) := by
      rw [←hS]
      let := extraspecial_normalizer_centralizer_sylow_cyclic d h hab structural previous faithful he S
      exact isCyclic_of_surjective (C.subtype.subgroupMap (S : Subgroup C))
        (C.subtype.subgroupMap_surjective (S : Subgroup C))
    let E := (B₀ ⊓ C).subgroupOf X
    let : IsCyclic E := (subgroupOfEquivOfLe hBCM).isCyclic.mpr hc
    have heq : E = A' := cyclic_eq_detected_cubic hX A' hA'c f hi hr E (comap_mono hAC)
    have hh := congrArg (Subgroup.map X.subtype) heq
    rwa [map_subgroupOf_eq_of_le hBCM,map_subgroupOf_eq_of_le hAX] at hh
  exact ⟨hAc,hBC,hsplit,hdis,hcentral,hcyc⟩

/-- The source Sylow choice, now with the exact split normalizer factor and
its residual-centralizer Sylow identified, under the original hypotheses. -/
theorem extraspecial_normalizer_three_sylow_split_source
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ B : Sylow 3 (normalizer (K F : Set G)),
      let B₀ := (B : Subgroup _).map (normalizer (K F : Set G)).subtype
      let B_K := B₀ ⊓ K F
      let B₁ := B₀ ⊓ F.Li L 1
      let B_M := B₀ ⊓ normalizer (F.Ri L 1 : Set G)
      let B₂ := pCoreActionKernelIn 2 L B_M
      (B₀ : Set G) = (B_K : Set G) * (B_M : Set G) ∧
        B_M ≤ normalizer (L : Set G) ∧
        IsSylowIn 3 B₁ (F.Li L 1) ∧ Nat.card B₁ = 3 ∧
        B₀ ⊓ normalizerResidualCentralizer F = B₁ ∧
        B_M = B₁ ⊔ B₂ ∧ Disjoint B₁ B₂ ∧
        B₁ ≤ centralizer (B₂ : Set G) ∧ IsCyclic B₂ ∧
        Nonempty (B₁ × B₂ ≃* B_M) := by
  obtain ⟨B,_,hf,hBC,hML⟩ := extraspecial_normalizer_three_sylow_factorization
    d h hab structural previous faithful earlier he
  obtain ⟨hc,hC,hs,hd,hcent,hcyc⟩ := extraspecial_normalizer_three_sylow_split
    d h hab structural previous faithful he B hBC hML
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hd hcent
  exact ⟨B,hf,hML,
    (extraspecial_normalizer_point_three_sylow h hab structural previous faithful he B).1,
    hc,hC,hs,hd,hcent,hcyc,⟨e.trans (MulEquiv.subgroupCongr hs.symm)⟩⟩

/-- The original residual centralizer is L₁ times its normal three-complement;
its quotient by that complement has order exactly three. -/
theorem extraspecial_normalizer_centralizer_three_structure
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let C := normalizerResidualCentralizer F
    (∀ S : Sylow 3 C, Nat.card S = 3) ∧
      C = F.Li L 1 ⊔ (pPrimeCore 3 C).map C.subtype ∧
      Nat.card (C ⧸ pPrimeCore 3 C) = 3 := by
  let N := normalizer (K F : Set G)
  let C := normalizerResidualCentralizer F
  obtain ⟨B,_,_,_,hc,hBC,_,_,_,_,_⟩ :=
    extraspecial_normalizer_three_sylow_split_source d h hab structural previous faithful earlier he
  obtain ⟨S,hS⟩ := B.exists_map_subtype_eq_inf_of_normalizes
    (show C ≤ N from map_subtype_le _) normalizerResidualCentralizer_normalizes
  have hSc : Nat.card S = 3 := by
    have hh := congrArg (fun A : Subgroup G => Nat.card A) hS
    rw [card_map_of_injective C.subtype_injective,hBC] at hh
    exact hh.trans hc
  have hcomp : HasNormalPComplement 3 C := hasNormalPComplement_of_le 3 le_sup_left
    (extraspecial_centralizer_point_normal_complement d h hab structural previous faithful he)
  have hQ : IsPGroup 3 (C ⧸ pPrimeCore 3 C) :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 3 C hcomp
  have hgen := S.sup_eq_top_of_quotient_isPGroup (pPrimeCore 3 C) hQ
  have hgen' : C = ((S : Subgroup C).map C.subtype) ⊔ (pPrimeCore 3 C).map C.subtype := by
    have hh := congrArg (Subgroup.map C.subtype) hgen
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,C.range_subtype] at hh
    exact hh.symm
  have hL : F.Li L 1 ≤ C := extraspecial_point_le_residualCentralizer
    h hab structural previous faithful he
  have hSL : (S : Subgroup C).map C.subtype ≤ F.Li L 1 :=
    hS.le.trans (hBC.le.trans inf_le_right)
  have hCL : C = F.Li L 1 ⊔ (pPrimeCore 3 C).map C.subtype :=
    le_antisymm (hgen'.le.trans (sup_le_sup hSL le_rfl))
      (sup_le hL (map_subtype_le _))
  let q := QuotientGroup.mk' (pPrimeCore 3 C)
  let S' := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hS' : (S' : Subgroup (C ⧸ pPrimeCore 3 C)) = ⊤ :=
    (S'.is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  have honto : Function.Surjective (q.comp (S : Subgroup C).subtype) := by
    intro x
    obtain ⟨s,hs,hsx⟩ := (show x ∈ (S' : Subgroup (C ⧸ pPrimeCore 3 C)) from hS' ▸ mem_top x)
    exact ⟨⟨s,hs⟩,hsx⟩
  have hinj := IsPGroup.quotient_pPrimeCore_injective (S : Subgroup C) S.isPGroup'
  have hQc : Nat.card (C ⧸ pPrimeCore 3 C) = 3 :=
    (Nat.card_congr (Equiv.ofBijective (q.comp (S : Subgroup C).subtype) ⟨hinj,honto⟩)).symm.trans hSc
  exact ⟨fun S₀ => (Nat.card_congr (S₀.equiv S).toEquiv).trans hSc,hCL,hQc⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
