module

public import Stellmacher.Recognition.GTwoSixtyFourCentric
public import ABG.ChapterII.Section1.ExtremalNormalizerCharacteristic
public import Theory.SpecificGroups.C4SquareSignSwapSmallGeometry
public import Theory.GroupTheory.CyclicFourQuaternionProductGeometry
public import Theory.GroupTheory.CyclicTwoAut
public import Theory.GroupTheory.ElementaryEightSolvableCore

/-!
# Small centric normalizer actions in the order-64 configuration

This module records the involution-partition interface and reduces the small
exceptions to eight marked candidates, each with Sylow normalizer of order
at least 32. Under the local solvability and odd-core hypotheses, the full
centralizer lies in the subgroup and the actual action kernel is a two-group.
It also proves reductions through two-group automizers, the transfer subgroup,
and O₂(N_G(X)). Candidate 28 is controlled intrinsically: its central
involutions characterize transfer membership on involutions.

The other two central-product candidates have an order-32 subgroup acting
trivially on their central quotients. Their cyclic centers and the actual
action-kernel control put that subgroup in the ambient normalizer two-core.
Thus the central-product branch gives either the normalizer step or a
normalizer two-core of order at least 32. In the elementary-eight branch,
the full centralizer has order eight, so the Sylow normalizer bound forces
four to divide the actual automizer order. Its solvable two-core has order
at least four, giving the same order-32 conclusion without an invariant plane.

Source: the centric fusion argument for Stellmacher (8.6)(a), using the
actual marked Sylow model rather than an unmarked isomorphism type.
-/

namespace Stellmacher.Recognition

open BenderSuzuki.External

/-- The exact normalizer step needed to preserve the transfer partition
on involutions of the distinguished Sylow subgroup. -/
@[expose] public def GTwoCard64NormalizerStep
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (X : Subgroup G) : Prop :=
  ∀ g : G, g ∈ Subgroup.normalizer (X : Set G) →
    ∀ x y : data.sylowIntersection, orderOf x = 2 → orderOf y = 2 →
      (x : G) ∈ X → g⁻¹ * (x : G) * g = (y : G) →
        (x ∈ gTwoCard64TransferSubgroup data ↔ y ∈ gTwoCard64TransferSubgroup data)

/-- The two smaller exceptional isomorphism types in the centric classification. -/
@[expose] public def GTwoCard64SmallException
    {G : Type*} [Group G] (X : Subgroup G) : Prop :=
  (IsElementaryAbelian 2 X ∧ Nat.card X = 8) ∨
    Later.IsCentralProductModel X Later.C4 Later.Q8

/-- Control required from the two vertex-core cases, with the extremality
and centricity hypotheses retained. -/
@[expose] public def GTwoCard64CoreControl
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G) : Prop :=
  letI := data.groupK
  letI := data.finiteK
  ∀ X : Subgroup G,
    (X = (Later.QAt data.Γ data.criticalPath.a).map data.embedding ∨
      X = (Later.QAt data.Γ data.criticalPath.firstStep).map data.embedding) →
    HuppertExtremal data.sylowIntersection X →
    subgroupCentralizerIn (data.sylowIntersection : Subgroup G) X ≤ X →
    GTwoCard64NormalizerStep data X

/-- The marked model can be chosen so that a small exceptional subgroup
is literally one of the eight small candidates. The Sylow conjugation in
the classification is absorbed into the marking. -/
public theorem gTwo_card64_small_marked_candidate
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64)
    (X : Subgroup G) (hXS : X ≤ (data.sylowIntersection : Subgroup G))
    (hc : subgroupCentralizerIn (data.sylowIntersection : Subgroup G) X ≤ X)
    (haut : ¬ IsPGroup 2 (MulAut X))
    (hout : ¬ X.subgroupOf (data.sylowIntersection : Subgroup G) ≤
      gTwoCard64TransferSubgroup data)
    (hsmall : GTwoCard64SmallException X) :
    ∃ (e : data.sylowIntersection ≃* C4SquareSignSwap.Model) (i : Fin 32),
      (gTwoCard64TransferSubgroup data).map e.toMonoidHom = C4SquareSignSwap.transfer ∧
      (X.subgroupOf (data.sylowIntersection : Subgroup G)).map e.toMonoidHom =
        C4SquareSignSwap.centricCandidate i ∧
      (i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 26 ∨ i = 28 ∨ i = 29 ∨ i = 30) := by
  let := data.groupK
  let := data.finiteK
  obtain ⟨e, hU, _, _⟩ := gTwo_card64_marked_equiv data hcard
  let S := (data.sylowIntersection : Subgroup G)
  let Y := (X.subgroupOf S).map e.toMonoidHom
  let eX : X ≃* Y := (Subgroup.subgroupOfEquivOfLe hXS).symm.trans
    ((X.subgroupOf S).equivMapOfInjective e.toMonoidHom e.injective)
  have hcY : Subgroup.centralizer (Y : Set C4SquareSignSwap.Model) ≤ Y := by
    intro y hy
    have hx : (e.symm y : G) ∈ X := by
      apply hc
      refine ⟨(e.symm y).property, ?_⟩
      intro x hx
      have h := hy (e ⟨x, hXS hx⟩) (Subgroup.mem_map_of_mem e.toMonoidHom hx)
      have h' := congrArg (fun z => (e.symm z : G)) h
      simpa using h'
    exact ⟨e.symm y, hx, e.apply_symm_apply y⟩
  have houtY : ¬ Y ≤ C4SquareSignSwap.transfer := by
    intro h
    apply hout
    apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    simpa only [hU] using h
  obtain ⟨i, g, hY⟩ := C4SquareSignSwap.centricCandidate_complete Y hcY houtY
  let c : C4SquareSignSwap.Model ≃* C4SquareSignSwap.Model := MulAut.conj g
  let eY : Y ≃* C4SquareSignSwap.centricCandidate i :=
    (Y.equivMapOfInjective c.toMonoidHom c.injective).trans (MulEquiv.subgroupCongr hY)
  have hi : C4SquareSignSwap.centricExceptionalIndex i := by
    by_contra hi
    exact haut ((C4SquareSignSwap.centricCandidate_isPGroup_mulAut i hi).of_equiv
      (MulAut.congr (eX.trans eY)).symm)
  have hsize : Nat.card (C4SquareSignSwap.centricCandidate i) = 8 ∨
      Nat.card (C4SquareSignSwap.centricCandidate i) = 16 := by
    rw [← Nat.card_congr (eX.trans eY).toEquiv]
    rcases hsmall with hEA | hCP
    · exact Or.inl hEA.2
    · exact Or.inr (SectionEight.eight_six_c4_quaternion_card hCP)
  refine ⟨e.trans c, i, ?_, ?_, ?_⟩
  · rw [show (e.trans c).toMonoidHom = c.toMonoidHom.comp e.toMonoidHom from rfl, ← Subgroup.map_map, hU]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (inferInstance : C4SquareSignSwap.transfer.Normal).conj_mem y hy g
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, ?_⟩
      · change g⁻¹ * x * g ∈ C4SquareSignSwap.transfer
        simpa only [inv_inv] using
          (inferInstance : C4SquareSignSwap.transfer.Normal).conj_mem x hx g⁻¹
      · simp [c, MulAut.conj_apply, mul_assoc]
  · rw [show (e.trans c).toMonoidHom = c.toMonoidHom.comp e.toMonoidHom from rfl, ← Subgroup.map_map]
    exact hY
  · rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [C4SquareSignSwap.centricCandidate_eleven, C4SquareSignSwap.card_inverterCore] at hsize
      omega
    all_goals try simp
    rw [C4SquareSignSwap.centricCandidate_thirty_one,
      C4SquareSignSwap.card_extraspecialCore] at hsize
    omega

/-- Every small exceptional candidate has at least 32 elements in its
normalizer inside the actual Sylow subgroup. -/
public theorem gTwo_card64_small_sylow_normalizer_card
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64)
    (X : Subgroup G) (hXS : X ≤ (data.sylowIntersection : Subgroup G))
    (hc : subgroupCentralizerIn (data.sylowIntersection : Subgroup G) X ≤ X)
    (haut : ¬ IsPGroup 2 (MulAut X))
    (hout : ¬ X.subgroupOf (data.sylowIntersection : Subgroup G) ≤
      gTwoCard64TransferSubgroup data)
    (hsmall : GTwoCard64SmallException X) :
    32 ≤ Nat.card ((data.sylowIntersection : Subgroup G) ⊓
      Subgroup.normalizer (X : Set G) : Subgroup G) := by
  obtain ⟨e, i, _, hY, hi⟩ :=
    gTwo_card64_small_marked_candidate data hcard X hXS hc haut hout hsmall
  have hbound := C4SquareSignSwap.smallCandidate_normalizer_card i hi
  rw [← hY, ← Subgroup.map_equiv_normalizer_eq,
    Subgroup.card_map_of_injective e.injective,
    ← Subgroup.subgroupOf_normalizer_eq hXS] at hbound
  rw [← Subgroup.inf_subgroupOf_left,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at hbound
  exact hbound

/-- The actual small-subgroup normalizer is solvable with trivial odd core,
and its action kernel is a two-group. -/
public theorem gTwo_card64_small_normalizer_properties
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (hodd : ∀ L : Subgroup G, IsTwoLocal L → pPrimeCore 2 L = ⊥)
    (data : GTwoTwoDerivedTypeData G)
    (X : Subgroup G) (hX : HuppertExtremal data.sylowIntersection X)
    (hc : subgroupCentralizerIn (data.sylowIntersection : Subgroup G) X ≤ X)
    (hsmall : GTwoCard64SmallException X) :
    Group.IsSolvable (Subgroup.normalizer (X : Set G)) ∧
      pPrimeCore 2 (Subgroup.normalizer (X : Set G)) = ⊥ ∧
      Subgroup.centralizer (X : Set G) ≤ X ∧
      IsPGroup 2 X.normalizerMonoidHom.ker := by
  have hXne : X ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card X = 1 := Subgroup.card_eq_one.mpr hbot
    rcases hsmall with hEA | hCP
    · omega
    · have := SectionEight.eight_six_c4_quaternion_card hCP
      omega
  have hlocal : IsTwoLocal (Subgroup.normalizer (X : Set G)) :=
    ⟨X, hXne, IsPGroup.to_le data.sylowIntersection.isPGroup' hX.1, rfl⟩
  have hs := hN _ hlocal
  have ho := hodd _ hlocal
  exact ⟨hs, ho, ABG.centralizer_le_of_extremal_centric
    data.sylowIntersection X hX hc hs ho,
    ABG.normalizer_action_kernel_isPGroup data.sylowIntersection X hX hc hs ho⟩

/-- A two-group actual automizer reduces to conjugacy inside the Sylow. -/
public theorem gTwo_card64_step_of_range_isPGroup
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64)
    (X : Subgroup G) (hX : HuppertExtremal data.sylowIntersection X)
    (hRange : IsPGroup 2 (Subgroup.normalizerMonoidHom (H := X)).range) :
    GTwoCard64NormalizerStep data X := by
  intro g hg x y _ _ hx hxy
  have hconj := ABG.extremal_normalizer_fusion_control_of_range_isPGroup
    data.sylowIntersection X hX hRange g hg x y hx hxy
  obtain ⟨s, hs⟩ := isConj_iff.mp hconj
  have hnormal := (gTwo_card64_transfer_structure data hcard).1
  constructor
  · intro hxU
    exact hs ▸ hnormal.conj_mem x hxU s
  · intro hyU
    have h := hnormal.conj_mem y hyU s⁻¹
    simpa [← hs, mul_assoc] using h

/-- Normalizing a subgroup inside U cannot move its elements outside U. -/
public theorem gTwo_card64_step_of_le_transfer
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (X : Subgroup G)
    (hXU : X.subgroupOf (data.sylowIntersection : Subgroup G) ≤
      gTwoCard64TransferSubgroup data) :
    GTwoCard64NormalizerStep data X := by
  intro g hg x y _ _ hx hxy
  have hy : (y : G) ∈ X := by
    rw [← hxy]
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (X : Set G)).inv_mem hg) (x : G)).mp hx
  exact iff_of_true (hXU hx) (hXU hy)

/-- An extremal normalizer action extends to its actual two-core. -/
public theorem gTwo_card64_step_of_normalizerPCore
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (X : Subgroup G) (hX : HuppertExtremal data.sylowIntersection X)
    (hR : GTwoCard64NormalizerStep data (ABG.normalizerPCore 2 X)) :
    GTwoCard64NormalizerStep data X := by
  intro g hg x y hx2 hy2 hx hxy
  exact hR g (ABG.normalizer_le_normalizerPCore_normalizer 2 X hg) x y hx2 hy2
    (ABG.le_normalizerPCore 2 X
      (IsPGroup.to_le data.sylowIntersection.isPGroup' hX.1) hx) hxy

/-- Once the normalizer two-core has order at least 32, centric
classification reduces the step to the two vertex-core actions. -/
public theorem gTwo_card64_step_of_large_normalizerPCore
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64)
    (hCore : GTwoCard64CoreControl data)
    (X : Subgroup G) (hX : HuppertExtremal data.sylowIntersection X)
    (hc : subgroupCentralizerIn (data.sylowIntersection : Subgroup G) X ≤ X)
    (hlarge : 32 ≤ Nat.card (ABG.normalizerPCore 2 X)) :
    GTwoCard64NormalizerStep data X := by
  let := data.groupK
  let := data.finiteK
  let R := ABG.normalizerPCore 2 X
  have hRS := ABG.normalizerPCore_le_sylow data.sylowIntersection X hX
  have hcR := ABG.normalizerPCore_centric data.sylowIntersection X hX hc
  let T := R.subgroupOf (data.sylowIntersection : Subgroup G)
  have hTcard : Nat.card T = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRS).toEquiv
  have hcount : Nat.card T * T.index = 64 := by
    simpa only [hcard] using T.card_mul_index
  have hi0 : T.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hlargeT : 32 ≤ Nat.card T := hTcard.symm ▸ hlarge
  have hi : T.index = 1 ∨ T.index = 2 := by
    have : T.index ≤ 2 := by nlinarith
    omega
  have hTN : T.Normal := by
    rcases hi with hi | hi
    · rw [Subgroup.index_eq_one.mp hi]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two hi
  have hSNR : (data.sylowIntersection : Subgroup G) ≤
      Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRS).mp hTN
  have hRext := ABG.extremal_of_sylow_le_normalizer data.sylowIntersection R hRS hSNR
  apply gTwo_card64_step_of_normalizerPCore data X hX
  by_cases hRU : T ≤ gTwoCard64TransferSubgroup data
  · exact gTwo_card64_step_of_le_transfer data R hRU
  by_cases haut : IsPGroup 2 (MulAut R)
  · exact gTwo_card64_step_of_range_isPGroup data hcard R hRext (haut.to_subgroup _)
  rcases gTwo_card64_centric_classification data hcard R hRS hcR haut hRU with
    hEA | hCP | hQa | hQb
  · have hsmall := hEA.2
    change 32 ≤ Nat.card R at hlarge
    omega
  · have hsmall := SectionEight.eight_six_c4_quaternion_card hCP
    change 32 ≤ Nat.card R at hlarge
    omega
  · exact hCore R (Or.inl hQa) hRext hcR
  · exact hCore R (Or.inr hQb) hRext hcR

/-- A marked equivalence to candidate 28 controls all ambient normalizer
actions, since centrality characterizes transfer membership on involutions. -/
public theorem gTwo_card64_step_of_candidate28
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (X : Subgroup G) (hXS : X ≤ (data.sylowIntersection : Subgroup G))
    (e : X ≃* C4SquareSignSwap.centricCandidate 28)
    (hmark : ∀ x : X,
      (⟨(x : G), hXS x.property⟩ : data.sylowIntersection) ∈
          gTwoCard64TransferSubgroup data ↔
        (e x : C4SquareSignSwap.Model) ∈ C4SquareSignSwap.transfer) :
    GTwoCard64NormalizerStep data X := by
  intro g hg x y hx2 _ hx hxy
  let xX : X := ⟨x, hx⟩
  let a : MulAut X := Subgroup.normalizerMonoidHom (H := X)
    ⟨g⁻¹, (Subgroup.normalizer (X : Set G)).inv_mem hg⟩
  have hay : ((a xX : X) : G) = (y : G) := by
    simpa [a, xX, Subgroup.normalizerMonoidHom_apply_apply_coe] using hxy
  have hxX : xX ^ 2 = 1 := by
    have hxpow : x ^ 2 = 1 := by simpa only [hx2] using pow_orderOf_eq_one x
    apply Subtype.ext
    exact congrArg (fun z : data.sylowIntersection => (z : G)) hxpow
  have hex : (e xX) ^ 2 = 1 := by rw [← map_pow, hxX, map_one]
  have h := C4SquareSignSwap.candidate28_automorphism_preserves_transfer
    (MulAut.congr e a) (e xX) hex
  have hea : (MulAut.congr e a) (e xX) = e (a xX) := by
    change e (a (e.symm (e xX))) = e (a xX)
    rw [e.symm_apply_apply]
  rw [hea, ← hmark (a xX), ← hmark xX] at h
  have hyS : (⟨((a xX : X) : G), hXS (a xX).property⟩ : data.sylowIntersection) = y :=
    Subtype.ext hay
  rw [hyS] at h
  exact h.symm

/-- The preceding control applies directly to a candidate in the marked
Sylow model; its marking need not be supplied separately on each element. -/
public theorem gTwo_card64_step_of_model_candidate28
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (X : Subgroup G) (hXS : X ≤ (data.sylowIntersection : Subgroup G))
    (e : data.sylowIntersection ≃* C4SquareSignSwap.Model)
    (hU : (gTwoCard64TransferSubgroup data).map e.toMonoidHom =
      C4SquareSignSwap.transfer)
    (hY : (X.subgroupOf (data.sylowIntersection : Subgroup G)).map e.toMonoidHom =
      C4SquareSignSwap.centricCandidate 28) :
    GTwoCard64NormalizerStep data X := by
  let eX : X ≃* C4SquareSignSwap.centricCandidate 28 :=
    (Subgroup.subgroupOfEquivOfLe hXS).symm.trans
      (((X.subgroupOf (data.sylowIntersection : Subgroup G)).equivMapOfInjective
        e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hY))
  apply gTwo_card64_step_of_candidate28 data X hXS eX
  intro x
  have heX : (eX x : C4SquareSignSwap.Model) =
      e (⟨(x : G), hXS x.property⟩ : data.sylowIntersection) := rfl
  rw [heX, ← hU, Subgroup.mem_map_equiv]
  simp only [e.symm_apply_apply]

private theorem gTwo_card64_central_product_center_cyclic
    {G : Type*} [Group G] (X : Subgroup G)
    (hCP : Later.IsCentralProductModel X Later.C4 Later.Q8) :
    IsCyclic (Subgroup.center X) := by
  obtain ⟨B, C, ⟨eB⟩, ⟨eC⟩, rfl, hinter, hcomm, _⟩ := hCP
  have hZ := (Subgroup.cyclicFour_quaternion_product_geometry B C
    ⟨eB⟩ ⟨eC⟩ hinter hcomm).1
  let eZ := ((Subgroup.center (B ⊔ C : Subgroup G)).equivMapOfInjective
    (B ⊔ C).subtype (Subgroup.subtype_injective _)).trans
      ((MulEquiv.subgroupCongr hZ).trans eB)
  exact eZ.isCyclic.mpr inferInstance

private theorem gTwo_card64_central_product_candidate_core_card
    {G : Type*} [Group G] [Finite G]
    (data : GTwoTwoDerivedTypeData G)
    (X : Subgroup G) (hXS : X ≤ (data.sylowIntersection : Subgroup G))
    (hCP : Later.IsCentralProductModel X Later.C4 Later.Q8)
    (hker : IsPGroup 2 X.normalizerMonoidHom.ker)
    (e : data.sylowIntersection ≃* C4SquareSignSwap.Model)
    (i : Fin 32) (hi : i = 17 ∨ i = 26)
    (hY : (X.subgroupOf (data.sylowIntersection : Subgroup G)).map e.toMonoidHom =
      C4SquareSignSwap.centricCandidate i) :
    32 ≤ Nat.card (ABG.normalizerPCore 2 X) := by
  let S := (data.sylowIntersection : Subgroup G)
  let R₀ := C4SquareSignSwap.extraspecialCore.map e.symm.toMonoidHom
  let R := R₀.map S.subtype
  obtain ⟨hRN, htriv⟩ := C4SquareSignSwap.smallCentralProduct_extraspecialCore_action i hi
  have hnormal : R ≤ Subgroup.normalizer (X : Set G) := by
    rintro g ⟨s, hs, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hs
    have hzN := hRN hz
    rw [← hY, ← Subgroup.map_equiv_normalizer_eq, Subgroup.mem_map_equiv,
      ← Subgroup.subgroupOf_normalizer_eq hXS] at hzN
    exact hzN
  let : IsCyclic (Subgroup.center X) := gTwo_card64_central_product_center_cyclic X hCP
  have hXp := IsPGroup.to_le data.sylowIntersection.isPGroup' hXS
  have hRle : R ≤ ABG.normalizerPCore 2 X := by
    apply ABG.le_normalizerPCore_of_central_quotient_trivial X R hXp hker
      (hXp.to_subgroup (Subgroup.center X)).mulAut_of_isCyclic_two hnormal
    rintro g ⟨s, hs, rfl⟩ x hx y hy
    obtain ⟨z, hz, rfl⟩ := hs
    let xS : data.sylowIntersection := ⟨x, hXS hx⟩
    let yS : data.sylowIntersection := ⟨y, hXS hy⟩
    have hxM : e xS ∈ C4SquareSignSwap.centricCandidate i := by
      rw [← hY]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hx
    have hyM : e yS ∈ C4SquareSignSwap.centricCandidate i := by
      rw [← hY]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hy
    have h := htriv z hz (e xS) hxM (e yS) hyM
    have h' := congrArg (fun t => (e.symm t : G)) h
    simpa [xS, yS] using h'
  have hRcard : Nat.card R = 32 := by
    rw [Subgroup.card_map_of_injective S.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, C4SquareSignSwap.card_extraspecialCore]
  rw [← hRcard]
  exact Nat.card_le_card_of_injective (Subgroup.inclusion hRle)
    (Subgroup.inclusion_injective hRle)

/-- For a small central-product exception, either its ambient normalizer
preserves the marked involution partition, or its actual normalizer two-core
has order at least 32. -/
public theorem gTwo_card64_central_product_core_alternative
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (hodd : ∀ L : Subgroup G, IsTwoLocal L → pPrimeCore 2 L = ⊥)
    (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64)
    (X : Subgroup G) (hX : HuppertExtremal data.sylowIntersection X)
    (hc : subgroupCentralizerIn (data.sylowIntersection : Subgroup G) X ≤ X)
    (hCP : Later.IsCentralProductModel X Later.C4 Later.Q8) :
    GTwoCard64NormalizerStep data X ∨ 32 ≤ Nat.card (ABG.normalizerPCore 2 X) := by
  by_cases haut : IsPGroup 2 (MulAut X)
  · exact Or.inl (gTwo_card64_step_of_range_isPGroup data hcard X hX
      (haut.to_subgroup _))
  by_cases hout : X.subgroupOf (data.sylowIntersection : Subgroup G) ≤
      gTwoCard64TransferSubgroup data
  · exact Or.inl (gTwo_card64_step_of_le_transfer data X hout)
  obtain ⟨e, i, hU, hY, hi⟩ := gTwo_card64_small_marked_candidate
    data hcard X hX.1 hc haut hout (Or.inr hCP)
  have hsize : Nat.card (C4SquareSignSwap.centricCandidate i) = 16 := by
    rw [← hY, Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX.1).toEquiv]
    exact SectionEight.eight_six_c4_quaternion_card hCP
  have hiCP : i = 17 ∨ i = 26 ∨ i = 28 := by
    by_contra h
    have hiEA : i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 29 ∨ i = 30 := by
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    have h8 := (C4SquareSignSwap.centricCandidate_elementary i hiEA).2
    omega
  have hker :=
    (gTwo_card64_small_normalizer_properties hN hodd data X hX hc (Or.inr hCP)).2.2.2
  rcases hiCP with hi | hi | rfl
  · exact Or.inr (gTwo_card64_central_product_candidate_core_card
      data X hX.1 hCP hker e i (Or.inl hi) hY)
  · exact Or.inr (gTwo_card64_central_product_candidate_core_card
      data X hX.1 hCP hker e i (Or.inr hi) hY)
  · exact Or.inl (gTwo_card64_step_of_model_candidate28 data X hX.1 e hU hY)

/-- An elementary-eight exception either already has the normalizer step,
or its solvable automizer has a two-core of order at least four. The action
kernel has order eight, so the ambient normalizer two-core has order at least 32. -/
public theorem gTwo_card64_elementary_eight_core_alternative
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (hodd : ∀ L : Subgroup G, IsTwoLocal L → pPrimeCore 2 L = ⊥)
    (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64)
    (X : Subgroup G) (hX : HuppertExtremal data.sylowIntersection X)
    (hc : subgroupCentralizerIn (data.sylowIntersection : Subgroup G) X ≤ X)
    (hEA : IsElementaryAbelian 2 X) (h8 : Nat.card X = 8) :
    GTwoCard64NormalizerStep data X ∨ 32 ≤ Nat.card (ABG.normalizerPCore 2 X) := by
  by_cases haut : IsPGroup 2 (MulAut X)
  · exact Or.inl (gTwo_card64_step_of_range_isPGroup data hcard X hX
      (haut.to_subgroup _))
  by_cases hout : X.subgroupOf (data.sylowIntersection : Subgroup G) ≤
      gTwoCard64TransferSubgroup data
  · exact Or.inl (gTwo_card64_step_of_le_transfer data X hout)
  let := hEA
  let N := Subgroup.normalizer (X : Set G)
  let M := (data.sylowIntersection : Subgroup G) ⊓ N
  obtain ⟨hsolv, hoddN, hcent, _⟩ :=
    gTwo_card64_small_normalizer_properties hN hodd data X hX hc (Or.inl ⟨hEA, h8⟩)
  have hcentEq : Subgroup.centralizer (X : Set G) = X :=
    le_antisymm hcent (Subgroup.le_centralizer X)
  have hker : Nat.card X.normalizerMonoidHom.ker = 8 := by
    rw [Subgroup.normalizerMonoidHom_ker, hcentEq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe X.le_normalizer).toEquiv, h8]
  have hMlarge : 32 ≤ Nat.card M :=
    gTwo_card64_small_sylow_normalizer_card data hcard X hX.1 hc haut hout
      (Or.inl ⟨hEA, h8⟩)
  have hMdiv : Nat.card M ∣ 2 ^ 6 := by
    have h := Subgroup.card_dvd_of_le (show M ≤ (data.sylowIntersection : Subgroup G)
      from inf_le_left)
    simpa [hcard] using h
  have h32M : 32 ∣ Nat.card M := by
    obtain ⟨k, hk, hMk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hMdiv
    interval_cases k <;> rw [hMk] at hMlarge ⊢ <;> norm_num at *
  have h32N : 32 ∣ Nat.card N :=
    dvd_trans h32M (Subgroup.card_dvd_of_le (show M ≤ N from inf_le_right))
  have hcount := X.normalizerMonoidHom.ker.card_mul_index
  rw [Subgroup.index_ker, hker] at hcount
  have hfour : 4 ∣ Nat.card X.normalizerMonoidHom.range := by
    rw [← hcount] at h32N
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 8)).mp h32N
  let : Group.IsSolvable N := hsolv
  let : Group.IsSolvable X.normalizerMonoidHom.range :=
    Group.isSolvable_of_surjective X.normalizerMonoidHom.rangeRestrict_surjective
  have hcore := four_le_card_pCore_of_solvable_elementary_eight_automorphisms
    X h8 X.normalizerMonoidHom.range hfour
  right
  rw [ABG.normalizerPCore_card_eq data.sylowIntersection X hX hc hsolv hoddN, hker]
  omega

/-- The small centric exceptions either preserve the marked involution
partition under their ambient normalizers, or extend to an actual normalizer
two-core of order at least 32. No vertex-core action hypothesis is needed. -/
public theorem gTwo_card64_small_core_alternative
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (hodd : ∀ L : Subgroup G, IsTwoLocal L → pPrimeCore 2 L = ⊥)
    (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64)
    (X : Subgroup G) (hX : HuppertExtremal data.sylowIntersection X)
    (hc : subgroupCentralizerIn (data.sylowIntersection : Subgroup G) X ≤ X)
    (hsmall : GTwoCard64SmallException X) :
    GTwoCard64NormalizerStep data X ∨ 32 ≤ Nat.card (ABG.normalizerPCore 2 X) := by
  rcases hsmall with ⟨hEA, h8⟩ | hCP
  · exact gTwo_card64_elementary_eight_core_alternative hN hodd data hcard X hX hc hEA h8
  · exact gTwo_card64_central_product_core_alternative hN hodd data hcard X hX hc hCP

end Stellmacher.Recognition
