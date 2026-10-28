module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizerSplit
public import Theory.GroupTheory.Extraspecial27CubicRank
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import Theory.GroupTheory.ConjugateSpanSupplement
/-!
# Excluding the remaining cubic normalizer kernel

The original R₁ action on K/O₂(K) is a nontrivial center-fixing two-group.
Its unique involution is fixed by every actor normalizing R₁. The actual
intersection of a three-Sylow B of N_G(K) with K maps isomorphically onto
K/O₂(K). Transporting that involution and the cubic action to this normal
subgroup of B makes the ambient three-rank obstruction applicable.

Every cubic in N_B(R₁) therefore acts trivially on K/O₂(K). In the source
split B_M = B₁ × B₂, this puts a hypothetical cubic of B₂ in B ∩ C = B₁,
contradicting disjointness. Thus B₂ = 1, B_M = B₁ and B lies wholly in K,
with its actual Heisenberg isomorphism retained. The marked outer image is
a two-group, giving N = H O₃′(N) and C = L₁ O₃′(N). The original orbit
W = ⟨V₁^C⟩ lies in Z(O₂(N)), is reduced in C R₁, and its faithful
C R₁-action has order prime to three.

Source: Aschbacher–Smith 14.7.21(1), printed pp.1049–1050,
refs/quasithin.pdf. The final Baumann-normalizer argument and N_G(K)=H
remain separate obligations. No normality of C R₁ is asserted here.
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

private theorem residual_quotient_action_star (n : F.H)
    (x : (K F) ⧸ pCore 2 (K F)) :
    residualStarEquiv F (pCoreNormalizerAction 2 (K F) (inclusion (H_normalizes_K F) n) x) =
      MulAut.conjNormal (starMap F n) (residualStarEquiv F x) := by
  induction x using QuotientGroup.induction_on with | H k =>
    change residualStarEquiv F (pCoreNormalizerAction 2 (K F) (inclusion (H_normalizes_K F) n) (QuotientGroup.mk' _ k)) = _
    apply Subtype.ext
    rw [pCoreNormalizerAction_mk,residualStarEquiv_mk]
    change starMap F _ = starMap F n *
      (residualStarEquiv F (QuotientGroup.mk' (pCore 2 (K F)) k) : HStar F.H) * (starMap F n)⁻¹
    rw [residualStarEquiv_mk,←map_inv,←map_mul,←map_mul]
    congr 1

/-- The actual point-core action has a center-fixing involution preserved by
its original normalizer. -/
theorem extraspecial_point_action_involution
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ a : MulAut ((K F) ⧸ pCore 2 (K F)), a^2=1 ∧ a≠1 ∧
      (∀ z ∈ center ((K F) ⧸ pCore 2 (K F)), a z=z) ∧
      ∀ n : normalizer (K F : Set G), (n : G) ∈ normalizer (F.Ri L 1 : Set G) →
        a * pCoreNormalizerAction 2 (K F) n = pCoreNormalizerAction 2 (K F) n * a := by
  obtain ⟨e⟩ := he
  let J := (K F) ⧸ pCore 2 (K F)
  let N := normalizer (K F : Set G)
  let f := pCoreNormalizerAction 2 (K F)
  let R := (F.Ri L 1).subgroupOf N
  let A := R.map f
  let : IsExtraspecial 3 J := (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hc : Nat.card J=27 := (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p:=3))
  have hR2 : IsPGroup 2 A := (isPGroup_pCoreIn 2 _).comap_subtype.map f
  have hRY : F.Ri L 1 ≤ normalizerPointCentralizer F L :=
    (isSylowIn_iff.mp (extraspecial_normalizer_point_sylow h hab structural previous faithful ⟨e⟩)).2.1
  have hZ : ∀ a ∈ A, ∀ z ∈ center J, a z=z := by
    rintro a ⟨r,hr,rfl⟩
    have hy : r ∈ (normalizerPointCentralizer F L).subgroupOf N := hRY hr
    rw [extraspecial_normalizer_point_outer_preimage h hab structural previous faithful e] at hy
    exact (HeisenbergPrime.TernaryOuterAction.markedAction_mem_special_iff e (f r)).mp hy
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous
    (inferInstanceAs (IsExtraspecial 3 J)) hc
    ((Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2)))
  obtain ⟨c,hs,_,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  obtain ⟨a,ha,_,_,hne,_⟩ := exists_extraspecial_critical_actor h hab structural previous
    (inferInstanceAs (IsExtraspecial 3 J)) hc
    ((Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))) c hs
  have hA : A ≠ ⊥ := by
    intro hh
    have hfa : f (inclusion (H_normalizes_K F) a) = 1 := by
      have hm : f (inclusion (H_normalizes_K F) a) ∈ A :=
        mem_map_of_mem f (critical_le_Ri h structural c ha)
      simpa only [hh,mem_bot] using hm
    apply hne
    ext x
    obtain ⟨y,rfl⟩ := (residualStarEquiv F).surjective x
    rw [←residual_quotient_action_star a y,hfa]
    rfl
  obtain ⟨a,ha,ha2,ha1,hfix⟩ :=
    MulAut.exists_involution_fixed_by_normalizer_of_extraspecial27 hc A hR2 hA hZ
  refine ⟨a,ha2,ha1,hZ a ha,?_⟩
  intro n hnR
  apply hfix
  apply le_normalizer_map f
  apply mem_map_of_mem
  apply mem_normalizer_fintype
  intro r hr
  exact (mem_normalizer_iff.mp hnR r).mp hr

/-- The quotient map identifies the actual intersection with K with its
Heisenberg quotient, retaining equivariance for the containing three-Sylow. -/
private theorem normalizer_three_sylow_residual_quotient_bijective
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (B : Sylow 3 (normalizer (K F : Set G))) :
    let B₀ := (B : Subgroup _).map (normalizer (K F : Set G)).subtype
    Function.Bijective (fun x : (K F).subgroupOf B₀ =>
      QuotientGroup.mk' (pCore 2 (K F)) ⟨x.val.val,x.property⟩) := by
  let N := normalizer (K F : Set G)
  let B₀ := (B : Subgroup N).map N.subtype
  let P := (K F).subgroupOf B₀
  let i : P →* K F := {
    toFun x := ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let q := QuotientGroup.mk' (pCore 2 (K F))
  change Function.Bijective (q.comp i)
  have hB : IsPGroup 3 B₀ := B.isPGroup'.map N.subtype
  have hd := hB.disjoint_of_coprime (isPGroup_pCoreIn 2 (K F)) (by decide : Nat.Coprime 3 2)
  have hi : Function.Injective (q.comp i) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    have hm : (i x : G) ∈ (K F).pCoreIn 2 :=
      mem_map_of_mem (K F).subtype ((QuotientGroup.eq_one_iff _).mp hx)
    exact Subtype.ext (Subtype.ext (hd.le_bot ⟨x.val.property,hm⟩))
  refine ⟨hi,?_⟩
  obtain ⟨S,hS⟩ := B.exists_map_subtype_eq_inf_of_normalizes (K F).le_normalizer le_rfl
  obtain ⟨e⟩ := he
  have hQ : IsPGroup 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).isPGroup.of_equiv e.symm
  let S' := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hStop : (S' : Subgroup ((K F) ⧸ pCore 2 (K F))) = ⊤ :=
    (S'.is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  intro y
  obtain ⟨k,hk,hky⟩ := (show y ∈ (S' : Subgroup ((K F) ⧸ pCore 2 (K F))) from hStop ▸ mem_top y)
  have hkB : (k : G) ∈ B₀ := (hS ▸ mem_map_of_mem (K F).subtype hk).1
  exact ⟨⟨⟨k,hkB⟩,k.property⟩,hky⟩

/-- Every cubic in the original point-core normalizer acts trivially on
K/O₂(K), using the actual ambient three-rank bound. -/
theorem extraspecial_normalizer_cubic_action_trivial
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (B : Sylow 3 (normalizer (K F : Set G)))
    (b : (B : Subgroup _).map (normalizer (K F : Set G)).subtype)
    (hb : b^3=1) (hbn : (b : G) ∈ normalizer (F.Ri L 1 : Set G)) :
    pCoreNormalizerAction 2 (K F) ⟨b,map_subtype_le _ b.property⟩ = 1 := by
  let N := normalizer (K F : Set G)
  let B₀ := (B : Subgroup N).map N.subtype
  let P := (K F).subgroupOf B₀
  have hBN : B₀ ≤ N := map_subtype_le _
  let : P.Normal := normal_subgroupOf_of_le_normalizer hBN
  let i : P →* K F := {
    toFun x := ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let q := QuotientGroup.mk' (pCore 2 (K F))
  let eP := MulEquiv.ofBijective (q.comp i) (normalizer_three_sylow_residual_quotient_bijective he B)
  obtain ⟨e⟩ := he
  obtain ⟨a,ha2,ha1,haZ,hcomm⟩ := extraspecial_point_action_involution h hab structural previous faithful ⟨e⟩
  let β := pCoreNormalizerAction 2 (K F) ⟨b,hBN b.property⟩
  have hβ3 : β^3=1 := by
    change pCoreNormalizerAction 2 (K F) (inclusion hBN b)^3=1
    rw [←map_pow,←map_pow,hb,map_one,map_one]
  have hc : Nat.card (center ((K F) ⧸ pCore 2 (K F)))=3 := by
    rw [Nat.card_congr (centerCongr e).toEquiv,HeisenbergPrime.card_center]
  have hr : primeRank 3 B₀ ≤ 2 := (primeRank_mono 3 hBN).trans
    (extraspecial_normalizer_threeRanks d h hab structural previous faithful ⟨e⟩).1.le
  apply cubic_action_trivial_of_extraspecial27_marking P hr eP e a β ha2 ha1 haZ b hb
    (hcomm ⟨b,hBN b.property⟩ hbn) (MulAut.fixes_cubic_center_of_cube_eq_one hc β hβ3)
  intro x
  change q (i (MulAut.conjNormal b x)) =
    pCoreNormalizerAction 2 (K F) ⟨b,hBN b.property⟩ (q (i x))
  rw [pCoreNormalizerAction_mk]
  rfl

/-- The remaining literal L/O₂(L)-action kernel of B_M is trivial. -/
theorem extraspecial_normalizer_three_sylow_kernel_eq_bot
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
    pCoreActionKernelIn 2 L (((B : Subgroup _).map
      (normalizer (K F : Set G)).subtype) ⊓ normalizer (F.Ri L 1 : Set G)) = ⊥ := by
  let N := normalizer (K F : Set G)
  let B₀ := (B : Subgroup N).map N.subtype
  let B₁ := B₀ ⊓ F.Li L 1
  let B_M := B₀ ⊓ normalizer (F.Ri L 1 : Set G)
  let B₂ := pCoreActionKernelIn 2 L B_M
  obtain ⟨_,hC,_,hd,_,_⟩ := extraspecial_normalizer_three_sylow_split
    d h hab structural previous faithful he B hBCM hBML
  have hB : IsPGroup 3 B₀ := B.isPGroup'.map N.subtype
  have hDB : B₂ ≤ B₀ := inf_le_left.trans inf_le_left
  have hD : IsPGroup 3 B₂ := hB.to_le hDB
  change B₂ = ⊥
  by_contra hn
  have hdiv : 3 ∣ Nat.card B₂ := hD.card_eq_or_dvd.resolve_left
    (fun hh => hn (card_eq_one.mp hh))
  obtain ⟨b,hbo⟩ := exists_prime_orderOf_dvd_card' (G:=B₂) 3 hdiv
  let bB : B₀ := inclusion hDB b
  have hb3 : bB^3=1 := by
    change inclusion hDB b ^ 3=1
    rw [←map_pow,←hbo,pow_orderOf_eq_one,map_one]
  have ha := extraspecial_normalizer_cubic_action_trivial d h hab structural previous faithful he B
    bB hb3 b.property.1.2
  have hbC : (b : G) ∈ normalizerResidualCentralizer F :=
    ⟨⟨b,map_subtype_le _ (hDB b.property)⟩,ha,rfl⟩
  have hb1 : (b : G) ∈ B₁ := by
    change (b : G) ∈ B₀ ⊓ F.Li L 1
    rw [←hC]
    exact ⟨hDB b.property,hbC⟩
  have hbone : b=1 := Subtype.ext (hd.le_bot ⟨hb1,b.property⟩)
  have hh : (1 : ℕ)=3 := by simpa only [hbone,orderOf_one] using hbo
  omega

/-- In the original source choice the full three-Sylow lies in K and has
order 27, and its point-core normalizer is exactly its intersection with L₁. -/
theorem extraspecial_normalizer_three_sylow_in_residual
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
      B₀ ≤ K F ∧ Nat.card B₀=27 ∧ Nonempty (B₀ ≃* HeisenbergPrime 3) ∧
        B₀ ⊓ normalizer (F.Ri L 1 : Set G) = B₀ ⊓ F.Li L 1 ∧
        pCoreActionKernelIn 2 L (B₀ ⊓ normalizer (F.Ri L 1 : Set G))=⊥ := by
  obtain ⟨B,hgen,hprod,hBCM,hBML⟩ := extraspecial_normalizer_three_sylow_factorization
    d h hab structural previous faithful earlier he
  have hbot := extraspecial_normalizer_three_sylow_kernel_eq_bot
    d h hab structural previous faithful he B hBCM hBML
  obtain ⟨_,_,hsplit,_,_,_⟩ := extraspecial_normalizer_three_sylow_split
    d h hab structural previous faithful he B hBCM hBML
  rw [hbot,sup_bot_eq] at hsplit
  have hBK : (B : Subgroup _).map (normalizer (K F : Set G)).subtype ≤ K F := by
    rw [hgen,hsplit]
    exact sup_le inf_le_right (inf_le_right.trans (pointResidual_le F))
  let B₀ := (B : Subgroup _).map (normalizer (K F : Set G)).subtype
  let f : B₀ →* ((K F) ⧸ pCore 2 (K F)) :=
    (QuotientGroup.mk' (pCore 2 (K F))).comp (inclusion hBK)
  have htop : (K F).subgroupOf B₀ = ⊤ := (subgroupOf_eq_top).mpr hBK
  let j : B₀ ≃* (K F).subgroupOf B₀ :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)
  have hj : Function.Bijective f :=
    (normalizer_three_sylow_residual_quotient_bijective he B).comp j.bijective
  obtain ⟨e⟩ := he
  let eB := (MulEquiv.ofBijective f hj).trans e
  exact ⟨B,hBK,(Nat.card_congr eB.toEquiv).trans (HeisenbergPrime.card (p:=3)),⟨eB⟩,hsplit,hbot⟩

private theorem outer_image_isTwoGroup_of_three_sylow_killed
    {X : Type*} [Group X] [Finite X]
    (f : X →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (B : Sylow 3 X)
    (hB : (B : Subgroup X) ≤ f.ker) : IsPGroup 2 f.range := by
  let S := B.mapSurjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  have hS : (S : Subgroup f.range)=⊥ := by
    apply bot_unique
    rintro x ⟨b,hb,rfl⟩
    exact Subtype.ext (hB hb)
  have hthree : ¬ 3 ∣ Nat.card f.range := by
    have hh := S.not_dvd_index
    rwa [hS,index_bot] at hh
  have hd : Nat.card f.range ∣ 48 := by
    have hc : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))=48 := by
      rw [Matrix.card_GL_field]; decide
    exact hc ▸ f.range.card_subgroup_dvd_card
  apply IsPGroup.of_card_dvd_pow (p:=2) (n:=4)
  have hcop : Nat.Coprime (Nat.card f.range) 3 :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr hthree).symm
  exact hcop.dvd_of_dvd_mul_left hd

/-- After the original cubic exclusion, H together with the literal
residual centralizer exhausts N_G(K). -/
theorem extraspecial_normalizer_eq_H_sup_centralizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    normalizer (K F : Set G) = F.H ⊔ normalizerResidualCentralizer F := by
  obtain ⟨B,hBK,_,_,_,_⟩ := extraspecial_normalizer_three_sylow_in_residual
    d h hab structural previous faithful earlier he
  obtain ⟨e⟩ := he
  let N := normalizer (K F : Set G)
  let a := pCoreNormalizerAction 2 (K F)
  let f := (HeisenbergPrime.TernaryOuterAction.markedAction e).comp a
  have hk : f.ker = (K F).subgroupOf N ⊔ a.ker := by
    rw [show f.ker = (HeisenbergPrime.TernaryOuterAction.markedAction e).ker.comap a from rfl,
      HeisenbergPrime.TernaryOuterAction.markedAction_ker,
      ←pCoreNormalizerAction_component_image,comap_map_eq]
  have hBf : (B : Subgroup N) ≤ f.ker := by
    rw [hk]
    intro b hb
    exact mem_sup_left (hBK (mem_map_of_mem N.subtype hb))
  have himage := outer_image_isTwoGroup_of_three_sylow_killed f B hBf
  have hQ : IsPGroup 2 (N ⧸ f.ker) :=
    himage.of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have hTN : (T : Subgroup G) ≤ N := (F.invariant 1).trans (H_normalizes_K F)
  have hgen := congrArg (Subgroup.map N.subtype)
    ((T.subtype hTN).sup_eq_top_of_quotient_isPGroup f.ker hQ)
  rw [Subgroup.map_sup,hk,Subgroup.map_sup,map_subgroupOf_eq_of_le (K F).le_normalizer,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN,←MonoidHom.range_eq_map,N.range_subtype] at hgen
  have hH : K F ⊔ (T : Subgroup G) = F.H := (residual_product F).symm
  change _ = F.H ⊔ a.ker.map N.subtype
  rw [←hH]
  simpa only [sup_assoc,sup_comm,sup_left_comm] using hgen.symm

private theorem normalizer_threePrimeCore_le_centralizer
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    (pPrimeCore 3 (normalizer (K F : Set G))).map (normalizer (K F : Set G)).subtype ≤
      normalizerResidualCentralizer F := by
  let N := normalizer (K F : Set G)
  let D := (pPrimeCore 3 N).map N.subtype
  let I := D.subgroupOf (K F)
  let q := QuotientGroup.mk' (pCore 2 (K F))
  have hcopD : Nat.Coprime 3 (Nat.card D) := by
    rw [card_map_of_injective N.subtype_injective]
    exact pPrimeCore_coprime_card
  have hcopI : Nat.Coprime 3 (Nat.card I) := hcopD.of_dvd_right
    (card_comap_dvd_of_injective D (K F).subtype (K F).subtype_injective)
  obtain ⟨e⟩ := he
  have hQ : IsPGroup 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).isPGroup.of_equiv e.symm
  have hI : I ≤ pCore 2 (K F) := by
    have hc : Nat.Coprime 3 (Nat.card (I.map q)) := hcopI.of_dvd_right (I.card_map_dvd q)
    have hi : I.map q=⊥ := card_eq_one.mp
      ((hQ.to_subgroup (I.map q)).card_eq_or_dvd.resolve_right
        (Nat.prime_three.coprime_iff_not_dvd.mp hc))
    simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff I).mp hi
  have hnD : N ≤ normalizer (D : Set G) := by
    have hh := (pPrimeCore 3 N).le_normalizer_map N.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,N.range_subtype] using hh
  rintro x ⟨n,hn,rfl⟩
  refine ⟨n,?_,rfl⟩
  change pCoreNormalizerAction 2 (K F) n = 1
  rw [pCoreNormalizerAction_eq_one_iff]
  intro k
  apply hI
  change (n : G) * (k : G) * (n : G)⁻¹ / (k : G) ∈ D
  rw [div_eq_mul_inv]
  exact le_normalizer_iff_commutator_le_left.mp ((K F).le_normalizer.trans hnD)
    (commutator_mem_commutator (mem_map_of_mem N.subtype hn) k.property)

/-- The source three-prime supplement is the core of the full normalizer,
not just an unspecified three-prime subgroup of C. -/
theorem extraspecial_normalizer_threePrime_supplement
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let N := normalizer (K F : Set G)
    let D := (pPrimeCore 3 N).map N.subtype
    normalizerResidualCentralizer F = F.Li L 1 ⊔ D ∧ N = F.H ⊔ D ∧
      (N : Set G) = (F.H : Set G) * (D : Set G) := by
  let N := normalizer (K F : Set G)
  let C := normalizerResidualCentralizer F
  let E := (pPrimeCore 3 C).map C.subtype
  let D := (pPrimeCore 3 N).map N.subtype
  have hCN : C ≤ N := map_subtype_le _
  have hEN : E ≤ N := (map_subtype_le _).trans hCN
  have hNE : N ≤ normalizer (E : Set G) :=
    normalizerResidualCentralizer_normalizes.trans
      (normalizer_le_normalizer_characteristic_image C (pPrimeCore 3 C))
  have hED : E ≤ D := by
    let : (E.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hNE
    have hc : Nat.Coprime 3 (Nat.card (E.subgroupOf N)) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv,
        card_map_of_injective C.subtype_injective]
      exact pPrimeCore_coprime_card
    have hh : E.subgroupOf N ≤ pPrimeCore 3 N := le_sSup ⟨inferInstance,hc⟩
    have hm := map_mono (f:=N.subtype) hh
    rwa [map_subgroupOf_eq_of_le hEN] at hm
  have hDC : D ≤ C := normalizer_threePrimeCore_le_centralizer he
  have hLC : F.Li L 1 ≤ C := extraspecial_point_le_residualCentralizer
    h hab structural previous faithful he
  have hC : C = F.Li L 1 ⊔ D := le_antisymm
    ((extraspecial_normalizer_centralizer_three_structure
      d h hab structural previous faithful earlier he).2.1.le.trans (sup_le_sup_left hED _))
    (sup_le hLC hDC)
  have hN : N = F.H ⊔ D := by
    change normalizer (K F : Set G) = F.H ⊔ D
    rw [extraspecial_normalizer_eq_H_sup_centralizer d h hab structural previous faithful earlier he]
    change F.H ⊔ C = F.H ⊔ D
    have hLH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
    rw [hC,←sup_assoc,sup_eq_left.mpr hLH]
  refine ⟨hC,hN,?_⟩
  change (N : Set G) = (F.H : Set G) * (D : Set G)
  rw [hN]
  apply coe_mul_of_left_le_normalizer_right
  have hND : N ≤ normalizer (D : Set G) := by
    have hh := (pPrimeCore 3 N).le_normalizer_map N.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,N.range_subtype] using hh
  exact (H_normalizes_K F).trans hND

/-- The original central-seed orbit is reduced in C R₁, with a faithful
action quotient of order prime to three. -/
theorem extraspecial_normalizer_central_seed_reduced
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let N := normalizer (K F : Set G)
    let C := normalizerResidualCentralizer F
    let X := C ⊔ F.Ri L 1
    let W := conjugateSpanBy (F.Vi 1) C
    IsElementaryAbelian 2 W ∧ W ≤ N.pCoreIn 2 ∧
      W ≤ centralizer (N.pCoreIn 2 : Set G) ∧
      Theory.GroupTheory.IsPReduced 2 (W.subgroupOf X) ∧
      F.Li L 1 ≤ centralizer (W : Set G) ∧
      Nat.Coprime 3 ((centralizer (W : Set G)).relIndex X) := by
  let N := normalizer (K F : Set G)
  let C := normalizerResidualCentralizer F
  let X := C ⊔ F.Ri L 1
  let W := conjugateSpanBy (F.Vi 1) C
  have hTN : (T : Subgroup G) ≤ N := (F.invariant 1).trans (H_normalizes_K F)
  have hCN : C ≤ N := map_subtype_le _
  have hZT : F.Vi 1 ≤ (T : Subgroup G) := (F.le_seed 1).trans h.chosen.le_sylow
  have hZC : F.Vi 1 ≤ centralizer (T : Set G) :=
    le_centralizer_iff.mp ((F.invariant 1).trans
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))))
  have hNmax := (extraspecial_residual_normalizer_unique d h hab structural previous faithful he).1
  have hNHe : N ∈ He G := mem_He_iff.mpr (d.qtke.evenCharacteristic T N hNmax hTN)
  have hQT : N.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN] using
      pCoreIn_le_sylow N (T.subtype hTN)
  have hWN : W ≤ N := conjugateSpanBy_le (hZT.trans hTN) (hCN.trans N.le_normalizer)
  have hWQcentral : W ≤ centralizer (N.pCoreIn 2 : Set G) :=
    conjugateSpanBy_le (hZC.trans (centralizer_le hQT))
      ((hCN.trans (N.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image N (pCore 2 N)))).trans
        (normalizer_le_normalizer_centralizer _))
  have hWQ : W ≤ N.pCoreIn 2 := (le_inf hWN hWQcentral).trans hNHe
  let : IsMulCommutative W := le_centralizer_iff_isMulCommutative.mp
    (hWQcentral.trans (centralizer_le hWQ))
  let := h.chosen.elementary
  let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le (F.le_seed 1)
  let : IsElementaryAbelian 2 W := conjugateSpanBy_elementary_of_commutative _ _
  have hZR : F.Vi 1 ≤ F.Ri L 1 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 (F.Vi 1)) (hZT.trans le_sup_right)
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1))
  have hRT : F.Ri L 1 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow (F.Li L 1 ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hRY := (isSylowIn_iff.mp
    (extraspecial_normalizer_point_sylow h hab structural previous faithful he)).2.1
  have hXY : X ≤ normalizerPointCentralizer F L := sup_le
    (extraspecial_normalizer_residualCentralizer_le_pointCentralizer h hab structural previous faithful he) hRY
  have hXC : X ≤ normalizer (C : Set G) :=
    (hXY.trans inf_le_left).trans normalizerResidualCentralizer_normalizes
  have hspan : conjugateSpanBy (F.Vi 1) X = W :=
    conjugateSpanBy_sup_of_normalizes_seed _ _ _ (hRT.trans (F.invariant 1))
      (le_sup_right.trans hXC)
  have hZX : F.Vi 1 ≤ X := hZR.trans le_sup_right
  have hWX : W ≤ X := hspan ▸ conjugateSpanBy_le_self hZX
  have hclosure : normalClosure (F.Vi 1 |>.subgroupOf X : Set X) = W.subgroupOf X := by
    rw [normalClosure_subgroupOf_eq_conjugateSpanBy _ _ hZX,hspan]
  have hred : Theory.GroupTheory.IsPReduced 2 (W.subgroupOf X) := by
    obtain ⟨S,hS⟩ := (extraspecial_normalizer_point_sylow
      h hab structural previous faithful he).restrict le_sup_right hXY
    have hS' : (S : Subgroup X) = (F.Ri L 1).subgroupOf X := by
      apply map_injective X.subtype_injective
      rw [hS,map_subgroupOf_eq_of_le le_sup_right]
    let : IsElementaryAbelian 2 ((F.Vi 1).subgroupOf X) := IsElementaryAbelian.subgroupOf hZX
    let : IsMulCommutative (normalClosure (F.Vi 1 |>.subgroupOf X : Set X)) := by
      rw [hclosure]
      infer_instance
    have hs : (F.Vi 1).subgroupOf X ≤ (S : Subgroup X) := by
      rw [hS']; exact comap_mono hZR
    have hc : (F.Vi 1).subgroupOf X ≤ centralizer (S : Set X) := by
      intro z hz s hs
      change s ∈ (S : Subgroup X) at hs
      rw [hS'] at hs
      exact Subtype.ext (hZC hz s (hRT hs))
    rw [←hclosure]
    exact Theory.GroupTheory.isPReduced_normalClosure_of_sylow_central S _ hs hc
  have hLZ : F.Li L 1 ≤ centralizer (F.Vi 1 : Set G) :=
    ((F.Li_le L 1).trans inf_le_right).trans
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)))
  have hLW : F.Li L 1 ≤ centralizer (W : Set G) :=
    le_centralizer_conjugateSpanBy_of_normalizes _ _ _
      (hCN.trans (extraspecial_normalizer_normalizes_point h hab structural previous faithful he)) hLZ
  let D := (pPrimeCore 3 N).map N.subtype
  have hND : N ≤ normalizer (D : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,N.range_subtype] using
      (pPrimeCore 3 N).le_normalizer_map N.subtype
  have hCD : C = F.Li L 1 ⊔ D :=
    (extraspecial_normalizer_threePrime_supplement d h hab structural previous faithful earlier he).1
  have hcopD : Nat.Coprime 3 (Nat.card D) := by
    rw [card_map_of_injective N.subtype_injective]
    exact pPrimeCore_coprime_card
  have hcopC : Nat.Coprime 3 ((centralizer (W : Set G)).relIndex C) := by
    apply (hcopD.of_dvd_right ?_).of_dvd_right (relIndex_dvd_of_le_left C hLW)
    rw [hCD,sup_comm,relIndex_sup_of_normalizes D (F.Li L 1)
      (((F.Li_le L 1).trans inf_le_right).trans ((H_normalizes_K F).trans hND))]
    exact relIndex_dvd_card _ _
  have hcopR : Nat.Coprime 3 (Nat.card (F.Ri L 1)) := by
    obtain ⟨k,hk⟩ := (isPGroup_pCoreIn 2 (F.Li L 1 ⊔ (T : Subgroup G))).exists_card_eq
    rw [show Nat.card (F.Ri L 1)=2^k from hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have hcopX : Nat.Coprime 3 (C.relIndex X) := by
    let : (C.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer hXC
    have hi := relIndex_sup_left ((F.Ri L 1).subgroupOf X) (C.subgroupOf X)
    rw [←subgroupOf_sup (show C ≤ X from le_sup_left) (show F.Ri L 1 ≤ X from le_sup_right),
      relIndex_subgroupOf le_rfl,relIndex_subgroupOf (show F.Ri L 1 ≤ X from le_sup_right)] at hi
    rw [hi]
    exact hcopR.of_dvd_right (relIndex_dvd_card _ _)
  refine ⟨inferInstance,hWQ,hWQcentral,hred,hLW,?_⟩
  have hp := hcopC.mul_right hcopX
  have hm := relIndex_inf_mul_relIndex (centralizer (W : Set G)) C X
  rw [inf_eq_left.mpr (show C ≤ X from le_sup_left)] at hm
  rw [hm] at hp
  exact hp.of_dvd_right (relIndex_dvd_of_le_left X inf_le_left)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction

