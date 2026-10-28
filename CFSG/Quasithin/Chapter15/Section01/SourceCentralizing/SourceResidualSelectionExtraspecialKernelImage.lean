module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelCoreFullDisplacement
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialSquareRoot
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelChain

/-!
# The actual extraspecial kernel-core image

All center-fixing involutions in the original Sylow image are equal. The
core image therefore either lies in the order-two Thompson image, or contains
an order-four element squaring to that involution. The first case moves V
only into U. In the second, the square-root fixed-plane calculation forces
the exact commutator chain [Q,V]=E and [Q,E]=U.
No bound on the rank or order of the ambient core is assumed.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Section02.ChosenGeometry.Cyclic
variable {G : Type*} [Group G] [Finite G]

private theorem center_fixing_involution_eq
    (P : Subgroup G) [P.Normal] [IsExtraspecial 3 P] (hP : Nat.card P = 27)
    (hC : centralizer (P : Set G) ≤ P) (S : Sylow 2 G)
    (a t : G) (haS : a ∈ (S : Subgroup G)) (htS : t ∈ (S : Subgroup G))
    (ha : orderOf a = 2) (ht : orderOf t = 2)
    (haC : a ∈ centralizer ((center P).map P.subtype : Set G))
    (htC : t ∈ centralizer ((center P).map P.subtype : Set G)) : a = t := by
  have hfix (s : G) (hs : s ∈ centralizer ((center P).map P.subtype : Set G)) :
      ∀ z ∈ center P, (MulAut.conjNormal s : MulAut P) z = z := by
    intro z hz
    apply Subtype.ext
    change s * (z : G) * s⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.mpr (hs z (mem_map_of_mem P.subtype hz)).symm
  have hprod : a*t ∈ P := IsExtraspecial.involution_mul_mem_of_card27 P hP hC a t
    ⟨by intro he; simp [he] at ha,by simpa only [ha] using pow_orderOf_eq_one a⟩
    ⟨by intro he; simp [he] at ht,by simpa only [ht] using pow_orderOf_eq_one t⟩
    (hfix a haC) (hfix t htC)
  have hdis : Disjoint P (S : Subgroup G) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n,hn⟩ := S.isPGroup'.exists_card_eq
    rw [hP,hn]
    exact (by decide : Nat.Coprime 27 2).pow_right n
  have he : a*t=1 := mem_bot.mp (hdis.eq_bot ▸
    (show a*t ∈ P ⊓ (S : Subgroup G) from ⟨hprod,(S : Subgroup G).mul_mem haS htS⟩))
  have ht2 : t*t=1 := by simpa only [pow_two,ht] using pow_orderOf_eq_one t
  exact (eq_inv_of_mul_eq_one_left he).trans (inv_eq_of_mul_eq_one_right ht2)

private theorem core_image_order_four
    (P : Subgroup G) [P.Normal] [IsExtraspecial 3 P] (hP : Nat.card P = 27)
    (hC : centralizer (P : Set G) ≤ P) (S : Sylow 2 G)
    (B : Subgroup G) (hBS : B ≤ (S : Subgroup G))
    (hBC : B ≤ centralizer ((center P).map P.subtype : Set G))
    (t : G) (htS : t ∈ (S : Subgroup G)) (ht : orderOf t = 2)
    (htC : t ∈ centralizer ((center P).map P.subtype : Set G))
    (hne : ¬ B ≤ zpowers t) :
    ∃ x ∈ B, orderOf x = 4 ∧ x^2=t ∧
      x ∈ centralizer ((center P).map P.subtype : Set G) := by
  obtain ⟨b,hb,hbt⟩ := SetLike.not_le_iff_exists.mp hne
  have hb2 : b^2≠1 := by
    intro he
    by_cases hb1 : b=1
    · exact hbt (hb1 ▸ one_mem _)
    · have hbe := center_fixing_involution_eq P hP hC S b t (hBS hb) htS
        (orderOf_eq_prime he hb1) ht (hBC hb) htC
      exact hbt (hbe ▸ mem_zpowers t)
  obtain ⟨n,hn⟩ := S.isPGroup'.exists_orderOf_eq_pow (⟨b,hBS hb⟩ : S)
  rw [←Subgroup.orderOf_coe] at hn
  have hn2 : 2≤n := by
    by_contra hh
    have hn01 : n=0 ∨ n=1 := by omega
    rcases hn01 with rfl | rfl
    · have hb1 : b=1 := orderOf_eq_one_iff.mp hn
      exact hb2 (by rw [hb1,one_pow])
    · exact hb2 (by simpa only [hn,pow_one] using pow_orderOf_eq_one b)
  let x := b^(orderOf b/4)
  have hxB : x∈B := B.pow_mem hb _
  have hx : orderOf x=4 := orderOf_pow_orderOf_div
    (by rw [hn]; positivity) (by rw [hn]; exact pow_dvd_pow 2 hn2)
  have hx2ne : x^2≠1 := by
    intro he
    have hd := orderOf_dvd_of_pow_eq_one he
    rw [hx] at hd
    norm_num at hd
  have hx22 : (x^2)^2=1 := by
    rw [←pow_mul]
    simpa only [hx] using pow_orderOf_eq_one x
  have hxt := center_fixing_involution_eq P hP hC S (x^2) t
    (hBS (B.pow_mem hxB 2)) htS (orderOf_eq_prime hx22 hx2ne) ht
    (hBC (B.pow_mem hxB 2)) htC
  exact ⟨x,hxB,hx,hxt,hBC hxB⟩

omit [Finite G] in
private theorem ambientSpace_card {V : Subgroup G} [IsElementaryAbelian 2 V]
    (W : Submodule (ZMod 2) (Additive V)) : Nat.card (ambientSpace V W) = Nat.card W := by
  rw [ambientSpace,card_map_of_injective V.subtype_injective]
  apply Nat.card_congr
  exact {
    toFun := fun v => ⟨Additive.ofMul v.val,v.property⟩
    invFun := fun v => ⟨v.val.toMul,v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

set_option backward.isDefEq.respectTransparency false in
/-- The original core image either lies in the small Thompson image, or
contains a literal order-four actor giving both exact displacement layers. -/
theorem PreparedChosenModule.extraspecial_kernel_image_alternatives
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
    let Q := (centralizer (U : Set G)).pCoreIn 2
    let f := (actionHom M V h.normalized).rangeRestrict
    let B := (Q.subgroupOf M).map f
    let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
    ∃ t, orderOf t=2 ∧ zpowers t=R ∧
      ((B≤R ∧ ⁅Q,V⁆≤U) ∨
        ∃ x∈B, orderOf x=4 ∧ x^2=t ∧
          ⁅Q,V⁆=thompsonFixed T V ∧ ⁅Q,thompsonFixed T V⁆=U) := by
  let := h.elementary
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let Q := (centralizer (U : Set G)).pCoreIn 2
  let E := thompsonFixed T V
  let D := internalActionImage M V h.normalized
  let ρ := imageRepresentation M V h.normalized
  let f : M →* D := (actionHom M V h.normalized).rangeRestrict
  have hf : Function.Surjective f := (actionHom M V h.normalized).rangeRestrict_surjective
  let B := (Q.subgroupOf M).map f
  let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  let P := pResidual 2 D
  let ZP := (center P).map P.subtype
  let S : Sylow 2 D := (T.subtype hM.1.2).mapSurjective hf
  have hcore := h.extraspecial_moved_centralizer_twoCore
    hG T hempty hM hmany hJ hu hfull hex
  have hQT : Q ≤ (T : Subgroup G) := hcore.2.1
  have hQM := hQT.trans hM.1.2
  have hBS : B≤(S : Subgroup D) := map_mono (subgroupOf_mono M hQT)
  have hQnorm : Mc ≤ normalizer (Q : Set G) := by
    change Mc ≤ normalizer ((centralizer (U : Set G)).pCoreIn 2 : Set G)
    rw [hcore.1]
    exact Mc.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))
  have hmod := h.extraspecial_partner_module_and_normalizer
    hG T hempty hM hmany hJ hu hfull hex
  have hQE : ⁅Q,V⁆≤E := h.extraspecial_moved_centralizer_full_displacement
    hG T hempty hM hmany hJ hu hfull hex
  have hQU : ⁅Q,E⁆≤U := h.extraspecial_moved_centralizer_core_displacement
    hG T hempty hM hmany hJ hu hfull hex
  have hEc : Nat.card E=16 :=
    h.extraspecial_thompson_fixed_card hG T hempty hM hmany hJ hfull hex
  obtain ⟨t,ht,htR,hr⟩ := h.extraspecial_small_thompson_image
    hG T hempty hM hmany hJ hfull hex
  change zpowers t=R at htR
  change fixedCodim ρ R=2 at hr
  have htS : t∈(S : Subgroup D) :=
    (map_mono (subgroupOf_mono M (ChapterB.thompsonJ_le _ _))) (htR ▸ mem_zpowers t)
  have hDcore : pCore 2 D=⊥ := by
    subst V
    exact source_localAction_twoCore hG T hM
  obtain ⟨_,_,_,hP,hPc,_,h6,_⟩ := hex
  let : IsExtraspecial 3 P := hP
  have hZc : Nat.card ZP=3 := by
    rw [card_map_of_injective P.subtype_injective,IsExtraspecial.center_order_p 3 P]
  have htZ : t∈centralizer (ZP : Set D) :=
    ExtraspecialBinarySix.small_involution_centralizes_center ρ
      (imageRepresentation_injective M V h.normalized) P hPc h6 t
      (by simpa only [ht] using pow_orderOf_eq_one t) (by rw [htR]; exact hr.le)
  have hZR : ZP≤normalizer (R : Set D) := by
    rw [←htR]
    exact (le_centralizer_iff.mp (zpowers_le.mpr htZ)).trans
      (Subgroup.centralizer_le_normalizer _)
  let WU := subspaceCommutator ρ ⊤ R
  have hZstable : ZP≤subspaceStabilizer ρ WU :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hZR
  have hUambient := ambientSpace_moved h.normalized h.le_selected
    ((ChapterB.thompsonJ_le (T : Subgroup G) 1).trans hM.1.2)
  change ambientSpace V WU=U at hUambient
  have hZpre : (ZP.comap f).map M.subtype≤Mc := by
    rw [hmod.2]
    change (ZP.comap f).map M.subtype≤normalizer (U : Set G)
    rw [←hUambient]
    apply le_normalizer_iff.mpr
    rintro _ ⟨m,hm,rfl⟩ _ ⟨v,hv,rfl⟩
    exact ⟨(ρ (f m) (Additive.ofMul v)).toMul,
      (hZstable hm (Additive.ofMul v)).2 hv,rfl⟩
  have hZB : ZP≤normalizer (B : Set D) := by
    intro z hz
    obtain ⟨m,hm⟩ := hf z
    have hmMc : (m : G)∈Mc := hZpre ⟨m,show f m∈ZP from hm.symm ▸ hz,rfl⟩
    have hmQ : m∈normalizer (Q.subgroupOf M : Set M) := by
      rw [←subgroupOf_normalizer_eq hQM]
      exact hQnorm hmMc
    exact hm ▸ (Q.subgroupOf M).le_normalizer_map f (mem_map_of_mem f hmQ)
  have hB2 : IsPGroup 2 B := (isPGroup_pCoreIn 2 _).comap_subtype.map f
  have hZ3 : IsPGroup 3 ZP := IsPGroup.of_card (n := 1) hZc
  have hBC : B≤centralizer (ZP : Set D) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    exact (le_inf (le_normalizer_iff_commutator_le_left.mp hZB)
      (le_normalizer_iff_commutator_le_right.mp (show B≤normalizer (ZP : Set D) from
        le_normalizer_of_normal))).trans
      (hB2.disjoint_of_coprime hZ3 (by decide)).le_bot
  change ∃ t, orderOf t=2 ∧ zpowers t=R ∧
    ((B≤R ∧ ⁅Q,V⁆≤U) ∨ ∃ x∈B, orderOf x=4 ∧ x^2=t ∧ ⁅Q,V⁆=E ∧ ⁅Q,E⁆=U)
  refine ⟨t,ht,htR,?_⟩
  by_cases hBR : B≤R
  · left
    refine ⟨hBR,?_⟩
    have hspaces : subspaceCommutator ρ ⊤ B≤WU := by
      apply Submodule.span_le.mpr
      rintro _ ⟨b,hb,v,hv,rfl⟩
      exact Submodule.subset_span ⟨b,hBR hb,v,hv,rfl⟩
    have hBambient := ambientSpace_moved h.normalized h.le_selected hQM
    change ambientSpace V (subspaceCommutator ρ ⊤ B)=⁅V,Q⁆ at hBambient
    rw [commutator_comm,←hBambient,←hUambient]
    rintro _ ⟨v,hv,rfl⟩
    exact ⟨v,hspaces hv,rfl⟩
  · right
    obtain ⟨x,hxB,hx,hxt,hxC⟩ := core_image_order_four P hPc
      (centralizer_pResidual_le_of_pCore_eq_bot hDcore) S B hBS hBC t htS ht htZ
      (by rwa [htR])
    obtain ⟨q,hq,hqx⟩ := hxB
    have hfix := SourceExtraspecialModel.extraspecial_square_root_fixed_plane ρ
      (imageRepresentation_injective M V h.normalized) P hPc h6 x t
      (by simpa only [ht] using pow_orderOf_eq_one t) hxt hxC (by rwa [htR])
    have hxdim : fixedCodim ρ (zpowers x)=4 := by
      have hh := fixedCodim_add_finrank ρ (zpowers x)
      rw [hfix.2,h6] at hh
      omega
    let L := (ρ x-LinearMap.id).range
    have hLdim : Module.finrank (ZMod 2) L=4 :=
      (fixedCodim_zpowers_eq_displacement_rank ρ x).symm.trans hxdim
    have hLcard : Nat.card (ambientSpace V L)=16 := by
      rw [ambientSpace_card,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hLdim]
      norm_num
    have hdisplacement (w : Additive V) :
        ((ρ x w-w).toMul : G)=⁅(q : G),(w.toMul : G)⁆ := by
      rw [←hqx]
      simp only [toMul_sub,div_eq_mul_inv]
      rfl
    have hLcomm : ambientSpace V L≤⁅Q,V⁆ := by
      rintro _ ⟨v,⟨w,hw⟩,rfl⟩
      change ρ x w-w=Additive.ofMul v at hw
      have he : ((ρ x w-w).toMul : G)=(v : G) :=
        congrArg (fun a : Additive V => (a.toMul : G)) hw
      change (v : G)∈⁅Q,V⁆
      rw [←he,hdisplacement]
      exact commutator_mem_commutator hq w.toMul.property
    have hLE : ambientSpace V L=E := eq_of_le_of_card_ge (hLcomm.trans hQE)
      (by rw [hLcard,hEc])
    have hQEeq : ⁅Q,V⁆=E := le_antisymm hQE (hLE ▸ hLcomm)
    have hUQE : U≤⁅Q,E⁆ := by
      rw [←hUambient]
      change ambientSpace V (subspaceCommutator ρ ⊤ R)≤⁅Q,E⁆
      rw [←htR,CyclicFixedRank.commutator_eq_range]
      rintro _ ⟨v,⟨w,hw⟩,rfl⟩
      change ρ t w-w=Additive.ofMul v at hw
      let e := ρ x w-w
      have he : (e.toMul : G)∈E := hLE ▸ (show (e.toMul : G)∈ambientSpace V L from
        ⟨e.toMul,⟨w,rfl⟩,rfl⟩)
      have hxx : ρ x (ρ x w)=ρ t w := by
        rw [←Module.End.mul_apply,←map_mul,←pow_two,hxt]
      have hdouble : ρ x e-e=ρ t w-w := by
        dsimp [e]
        rw [map_sub,hxx]
        have hneg (v : Additive V) : -v=v := by
          simpa only [CharTwo.neg_eq,one_smul] using (neg_smul (1 : ZMod 2) v).symm
        have hzero (v : Additive V) : v+v=0 := by
          simpa only [hneg] using add_neg_cancel v
        simp only [sub_eq_add_neg,hneg]
        abel_nf
        simp only [two_zsmul,hzero,zero_add]
      have hv : ((ρ x e-e).toMul : G)=(v : G) :=
        congrArg (fun a : Additive V => (a.toMul : G)) (hdouble.trans hw)
      change (v : G)∈⁅Q,E⁆
      rw [←hv,hdisplacement]
      exact commutator_mem_commutator hq he
    exact ⟨x,mem_map_of_mem f hq |> fun hh => hqx ▸ hh,hx,hxt,hQEeq,
      le_antisymm hQU hUQE⟩

/-- In the exact-intersection row, the actual core contains an order-four
action and both displacement layers are saturated. -/
theorem PreparedChosenModule.extraspecial_exact_intersection_core_image
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (heq : V ⊓ (centralizer ((⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G) : Set G)).pCoreIn 2 =
      thompsonFixed T V) :
    let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
    let Q := (centralizer (U : Set G)).pCoreIn 2
    let f := (actionHom M V h.normalized).rangeRestrict
    let B := (Q.subgroupOf M).map f
    let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
    ∃ t, orderOf t=2 ∧ zpowers t=R ∧
      ∃ x∈B, orderOf x=4 ∧ x^2=t ∧
        ⁅Q,V⁆=thompsonFixed T V ∧ ⁅Q,thompsonFixed T V⁆=U := by
  obtain ⟨t,ht,htR,ha⟩ :=
    h.extraspecial_kernel_image_alternatives hG T hempty hM hmany hJ hu hfull hex
  refine ⟨t,ht,htR,?_⟩
  rcases ha with hsmall | hlarge
  · exact (h.extraspecial_exact_intersection_core_displacement
      hG T hempty hM hmany hJ hu hfull hex heq hsmall.2).elim
  · exact hlarge

end CFSG.Quasithin.Chapter15.Section01
