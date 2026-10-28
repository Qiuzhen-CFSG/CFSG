module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialResidual

/-!
# The original residual image is the extraspecial center

The original third-local residual acts on the full six-space with a
cyclic-three image. Two-perfectness places this image in the extraspecial
residual, and the proper Sylow-containing intersection places it in the
residual center. Equality follows from the common order three.

The original intersection core consequently centralizes that literal center.
A kernel of order coprime to three also lets Sylow-three centralization of
any contained residual subgroup lift to the original group.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Chapter14.SourcePreliminaries
variable {G : Type*} [Group G] [Finite G]

/-- The actual action image of the literal third residual is exactly the
mapped center of the original extraspecial residual. -/
theorem PreparedChosenModule.extraspecial_third_residual_action_image
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    let D := internalActionImage M V h.normalized
    ((sourceResidual N Mc).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict =
      (center (pResidual 2 D)).map (pResidual 2 D).subtype := by
  let := h.elementary
  let D := internalActionImage M V h.normalized
  let f : M →* D := (actionHom M V h.normalized).rangeRestrict
  let S := (T.subtype hM.1.2).mapSurjective (f := f)
    (actionHom M V h.normalized).rangeRestrict_surjective
  let Y := sourceResidual N Mc
  let B := (Y.subgroupOf M).map f
  let A := ((M ⊓ N).subgroupOf M).map f
  obtain ⟨hle,_,hp,_,_,_⟩ :=
    h.extraspecial_third_residual hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc
  obtain ⟨hker,⟨e⟩⟩ :=
    h.extraspecial_third_residual_original_kernel hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc
  have hYM : Y ≤ M := hle.trans inf_le_left
  let a := f.comp (inclusion hYM)
  have hrange : a.range = B := by rw [MonoidHom.range_comp,inclusion_range]
  have hk : a.ker = pCore 2 Y := by
    ext y
    constructor
    · intro hy
      have hyf : inclusion hYM y ∈ (actionHom M V h.normalized).ker :=
        congrArg Subtype.val hy
      rw [actionHom_ker] at hyf
      have hyy : (y : G) ∈ Y.pCoreIn 2 := hker ▸ ⟨y.property,hyf⟩
      obtain ⟨z,hz,he⟩ := hyy
      exact (show z = y from Subtype.ext he) ▸ hz
    · intro hy
      have hyy : (y : G) ∈ Y ⊓ centralizer (V : Set G) :=
        hker.symm ▸ mem_map_of_mem Y.subtype hy
      apply Subtype.ext
      change actionHom M V h.normalized (inclusion hYM y) = 1
      change inclusion hYM y ∈ (actionHom M V h.normalized).ker
      rw [actionHom_ker]
      exact hyy.2
  let eqv := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange a)
  have hBc : Nat.card B = 3 := by
    rw [←hrange]
    exact (Nat.card_congr eqv.toEquiv).symm.trans ((Nat.card_congr e.toEquiv).trans (by simp))
  have hBP : B ≤ pResidual 2 D := by
    have hh := map_pResidual_le 2 a
    rw [(pResidual_eq_top_iff 2 Y).mpr hp,←MonoidHom.range_eq_map,hrange] at hh
    exact hh
  obtain ⟨_,_,hne⟩ := h.third_maximal_action_constraints hG T hempty hM hJ hu hN hNM hNMc
  obtain ⟨_,_,_,hP,_,_,_,hI⟩ := hex
  let : IsExtraspecial 3 (pResidual 2 D) := hP
  have hBA : B ≤ A := map_mono (subgroupOf_mono M hle)
  have hZ := SourceExtraspecialModel.proper_intersection_le_center S hI A
    (map_mono (subgroupOf_mono M (le_inf hM.1.2 hN.2))) hne
  apply eq_of_le_of_card_ge ((le_inf hBP hBA).trans hZ)
  rw [hBc,card_map_of_injective (pResidual 2 D).subtype_injective,
    IsExtraspecial.center_order_p 3 (pResidual 2 D)]

/-- Every actor from the original intersection two-core fixes the
center of the extraspecial residual pointwise. -/
theorem PreparedChosenModule.extraspecial_intersection_core_centralizes_center
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    let D := internalActionImage M V h.normalized
    (((M ⊓ N).pCoreIn 2).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict ≤
      centralizer ((center (pResidual 2 D)).map (pResidual 2 D).subtype : Set D) := by
  let D := internalActionImage M V h.normalized
  let f : M →* D := (actionHom M V h.normalized).rangeRestrict
  have he := h.extraspecial_third_residual_action_image
    hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc
  change ((sourceResidual N Mc).subgroupOf M).map f =
    (center (pResidual 2 D)).map (pResidual 2 D).subtype at he
  change (((M ⊓ N).pCoreIn 2).subgroupOf M).map f ≤
    centralizer ((center (pResidual 2 D)).map (pResidual 2 D).subtype : Set D)
  rw [←he]
  have hcore : pCore 2 D = ⊥ := by
    subst V
    exact source_localAction_twoCore hG T hM
  have hfk : pCore 2 M ≤ f.ker := by
    have hi : (pCore 2 M).map f ≤ pCore 2 D :=
      le_sSup ⟨Normal.map inferInstance f (actionHom M V h.normalized).rangeRestrict_surjective,
        pCore_isPGroup.map f⟩
    rw [hcore] at hi
    exact (Subgroup.map_eq_bot_iff _).mp (bot_unique hi)
  have hcomm := h.extraspecial_third_residual_intersection_core_commutator
    hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc
  rintro _ ⟨r,hr,rfl⟩ y ⟨y,hy,rfl⟩
  have hrc : ⁅r,y⁆ ∈ pCore 2 M := by
    obtain ⟨z,hz,he⟩ := hcomm (commutator_mem_commutator hr hy)
    have he' : ⁅r,y⁆ = z := Subtype.ext he.symm
    rwa [he']
  have hh : ⁅f r,f y⁆ = 1 := by
    rw [←map_commutatorElement]
    exact hfk hrc
  exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm

/-- If the original action kernel has order coprime to three, every
Sylow-three subgroup containing a subgroup of Y₂ centralizes that subgroup. -/
theorem PreparedChosenModule.extraspecial_third_threeSylow_centralizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc)
    (hcop : Nat.Coprime 3 (Nat.card (actionHom M V h.normalized).rangeRestrict.ker))
    (P₃ : Sylow 3 M) (X : Subgroup M) (hXY : X ≤ (sourceResidual N Mc).subgroupOf M)
    (hXP : X ≤ (P₃ : Subgroup M)) :
    (P₃ : Subgroup M) ≤ centralizer (X : Set M) := by
  let D := internalActionImage M V h.normalized
  let f : M →* D := (actionHom M V h.normalized).rangeRestrict
  have he := h.extraspecial_third_residual_action_image
    hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc
  change ((sourceResidual N Mc).subgroupOf M).map f =
    (center (pResidual 2 D)).map (pResidual 2 D).subtype at he
  have hi := injective_comp_subtype_of_coprime_ker f hcop (P₃ : Subgroup M) P₃.isPGroup'
  have h3 : IsPGroup 3 ((P₃ : Subgroup M).map f) := P₃.isPGroup'.map f
  intro p hp x hx
  have hxZ : f x ∈ (center (pResidual 2 D)).map (pResidual 2 D).subtype :=
    he ▸ mem_map_of_mem f (hXY hx)
  have hpP : f p ∈ pResidual 2 D := by
    apply mem_pResidual_of_orderOf_coprime
    have hc := h3.orderOf_coprime (by decide : Nat.Coprime 3 2)
      ⟨f p,mem_map_of_mem f hp⟩
    simpa only [←Subgroup.orderOf_coe] using hc.symm
  obtain ⟨z,hz,hzfx⟩ := hxZ
  have hc := congrArg (pResidual 2 D).subtype (mem_center_iff.mp hz ⟨f p,hpP⟩)
  change f p * (z : D) = (z : D) * f p at hc
  change (z : D) = f x at hzfx
  rw [hzfx] at hc
  have hcomm : (⟨x,hXP hx⟩ : P₃) * ⟨p,hp⟩ = ⟨p,hp⟩ * ⟨x,hXP hx⟩ := by
    apply hi
    change f (x*p) = f (p*x)
    simpa only [map_mul] using hc.symm
  exact congrArg (P₃ : Subgroup M).subtype hcomm

end CFSG.Quasithin.Chapter15.Section01
