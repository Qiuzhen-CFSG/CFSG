module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.Basic
public import Theory.SpecificGroups.MinusExtraspecial.CentralStructure
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.SingleInvolutionClassSylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Elementary local consequences of the I.4.7 hypotheses

The generalized Fitting subgroup is the two-core and has order 32; the
centralizer has order 1920. Its central involution belongs to the two-core,
whose center is exactly that involution line. The characteristic center
therefore forces the ambient normalizer of the two-core to equal the given
involution centralizer. Non-weak-closure makes this a proper subgroup and
forces the ambient group to have trivial center.

For the single-class branch the centralizer has odd index, giving Sylow
subgroups of order 128. These arguments do not assume simplicity and do not
assert either global recognition theorem.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.4.7,
printed p. 418, with the standard characteristic-center normalizer argument.
-/

namespace CFSG.Quasithin.Janko23

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G]

public theorem OneInvolutionClass.isConj (h : OneInvolutionClass G)
    {z t : G} (hz : orderOf z = 2) (ht : orderOf t = 2) : IsConj t z := by
  obtain ⟨a, _, ha⟩ := h
  exact (ha t ht).trans (ha z hz).symm

/-- Either chosen involution can represent the first of the two classes. -/
public theorem TwoInvolutionClasses.representatives (h : TwoInvolutionClasses G)
    {z : G} (hz : orderOf z = 2) :
    ∃ t : G, orderOf t = 2 ∧ ¬ IsConj z t ∧
      ∀ u : G, orderOf u = 2 → IsConj u z ∨ IsConj u t := by
  obtain ⟨a, b, ha, hb, hab, hcover⟩ := h
  rcases hcover z hz with hza | hzb
  · refine ⟨b, hb, fun hzb => hab (hza.symm.trans hzb), ?_⟩
    intro u hu
    exact (hcover u hu).imp (fun hua => hua.trans hza.symm) id
  · refine ⟨a, ha, fun hza => hab (hza.symm.trans hzb), ?_⟩
    intro u hu
    exact (hcover u hu).symm.imp (fun hub => hub.trans hzb.symm) id

variable {z : G}

public theorem ambientCore_le (z : G) : ambientCore z ≤ involutionCentralizer z :=
  map_subtype_le _

public theorem ambientCore_subgroupOf (z : G) :
    (ambientCore z).subgroupOf (involutionCentralizer z) = localCore z :=
  comap_map_eq_self_of_injective (involutionCentralizer z).subtype_injective _

variable [Finite G]

namespace HTypeAt

public theorem core_card (h : HTypeAt z) : Nat.card (localCore z) = 32 :=
  (Nat.card_congr h.core_equiv.some.toEquiv).trans MinusExtraspecial.card_model

public theorem core_isPGroup (h : HTypeAt z) : IsPGroup 2 (localCore z) :=
  IsPGroup.of_card (n := 5) h.core_card

public theorem core_isExtraspecial (h : HTypeAt z) : IsExtraspecial 2 (localCore z) :=
  IsExtraspecial.of_mulEquiv h.core_equiv.some.symm inferInstance

public theorem core_eq_pCore (h : HTypeAt z) :
    localCore z = pCore 2 (involutionCentralizer z) := by
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, h.core_isPGroup⟩
  · exact (pCore_le_fitting (involutionCentralizer z) 2).trans
      (fitting_le_generalizedFitting _)

public theorem quotient_card (h : HTypeAt z) :
    Nat.card (involutionCentralizer z ⧸ localCore z) = 60 := by
  rw [Nat.card_congr h.quotient_equiv.some.toEquiv, nat_card_alternatingGroup]
  norm_num

public theorem quotient_isSimpleGroup (h : HTypeAt z) :
    IsSimpleGroup (involutionCentralizer z ⧸ localCore z) := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact (MulEquiv.isSimpleGroup_congr h.quotient_equiv.some).mpr this

public theorem centralizer_card (h : HTypeAt z) : Nat.card (involutionCentralizer z) = 1920 := by
  rw [card_eq_card_quotient_mul_card_subgroup (localCore z), h.quotient_card, h.core_card]

public theorem ambientCore_card (h : HTypeAt z) : Nat.card (ambientCore z) = 32 := by
  rw [ambientCore, card_map_of_injective (involutionCentralizer z).subtype_injective]
  exact h.core_card

public theorem ambientCore_isExtraspecial (h : HTypeAt z) : IsExtraspecial 2 (ambientCore z) :=
  IsExtraspecial.of_mulEquiv
    ((localCore z).equivMapOfInjective _ (involutionCentralizer z).subtype_injective)
    h.core_isExtraspecial

omit [Finite G] in
/-- The center of the centralizer lies in its intrinsic generalized Fitting subgroup. -/
public theorem center_le_core : center (involutionCentralizer z) ≤ localCore z := by
  have hnil : Group.IsNilpotent (center (involutionCentralizer z)) := by
    refine ⟨1, ?_⟩
    rw [Subgroup.upperCentralSeries_one_eq_top_iff]
    infer_instance
  exact (show center (involutionCentralizer z) ≤ fittingSubgroup (involutionCentralizer z)
    from le_sSup ⟨inferInstance, hnil⟩).trans (fitting_le_generalizedFitting _)

omit [Finite G] in
public theorem involution_mem_core : z ∈ ambientCore z := by
  have hzH : z ∈ involutionCentralizer z := mem_centralizer_singleton_iff.mpr rfl
  have hzZ : (⟨z, hzH⟩ : involutionCentralizer z) ∈ center (involutionCentralizer z) :=
    mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.property)
  exact mem_map_of_mem (involutionCentralizer z).subtype (center_le_core hzZ)

public theorem core_center_image (h : HTypeAt z) :
    (center (ambientCore z)).map (ambientCore z).subtype = zpowers z := by
  let := h.ambientCore_isExtraspecial
  have hzQ : z ∈ ambientCore z := involution_mem_core
  have hzZ : (⟨z, hzQ⟩ : ambientCore z) ∈ center (ambientCore z) := by
    apply mem_center_iff.mpr
    intro q
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (ambientCore_le z q.property))
  apply (eq_of_le_of_card_ge (zpowers_le.mpr (mem_map_of_mem _ hzZ)) ?_).symm
  rw [card_map_of_injective (ambientCore z).subtype_injective,
    IsExtraspecial.center_order_p 2 (ambientCore z), Nat.card_zpowers]
  change 2 ≤ orderOf z
  exact h.involution.ge

public theorem centralizer_center_image (h : HTypeAt z) :
    (center (involutionCentralizer z)).map (involutionCentralizer z).subtype = zpowers z := by
  apply le_antisymm
  · rw [← h.core_center_image]
    rintro x ⟨a, ha, rfl⟩
    have haQ : (a : G) ∈ ambientCore z := mem_map_of_mem _ (center_le_core ha)
    refine mem_map.mpr ⟨⟨a, haQ⟩, mem_center_iff.mpr ?_, rfl⟩
    intro q
    exact Subtype.ext (congrArg (fun a : involutionCentralizer z => (a : G))
      (mem_center_iff.mp ha ⟨q, ambientCore_le z q.property⟩))
  · apply zpowers_le.mpr
    exact mem_map.mpr ⟨⟨z, mem_centralizer_singleton_iff.mpr rfl⟩,
      mem_center_iff.mpr (fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.property)), rfl⟩

public theorem normalizer_core (h : HTypeAt z) :
    normalizer (ambientCore z : Set G) = involutionCentralizer z := by
  apply le_antisymm
  · exact normalizer_le_centralizer_of_characteristic_involution
      (ambientCore z) (center (ambientCore z)) z h.involution h.core_center_image
  · apply (normal_subgroupOf_iff_le_normalizer (ambientCore_le z)).mp
    rw [ambientCore_subgroupOf]
    infer_instance

public theorem normalizer_centralizer (h : HTypeAt z) :
    normalizer (involutionCentralizer z : Set G) = involutionCentralizer z := by
  apply le_antisymm
  · exact normalizer_le_centralizer_of_characteristic_involution
      (involutionCentralizer z) (center (involutionCentralizer z)) z h.involution
      h.centralizer_center_image
  · exact le_normalizer

public theorem exists_returning_conjugate (h : HTypeAt z) :
    ∃ t ∈ ambientCore z, IsConj z t ∧ t ≠ z := by
  have hw := h.not_weakly_closed
  push Not at hw
  exact hw

public theorem exists_conjugator_outside (h : HTypeAt z) :
    ∃ g : G, g ∉ involutionCentralizer z ∧ g * z * g⁻¹ ∈ ambientCore z := by
  obtain ⟨t, htQ, ht, htz⟩ := h.exists_returning_conjugate
  obtain ⟨g, hg⟩ := isConj_iff.mp ht
  refine ⟨g, ?_, hg ▸ htQ⟩
  intro hgH
  exact htz (hg.symm.trans
    (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hgH)))

public theorem centralizer_ne_top (h : HTypeAt z) : involutionCentralizer z ≠ ⊤ := by
  obtain ⟨g, hg, _⟩ := h.exists_conjugator_outside
  intro he
  exact hg (he ▸ mem_top g)

public theorem core_not_normal (h : HTypeAt z) : ¬ (ambientCore z).Normal := by
  intro hn
  exact h.centralizer_ne_top (h.normalizer_core.symm.trans (normalizer_eq_top_iff.mpr hn))

public theorem center_eq_bot (h : HTypeAt z) : center G = ⊥ := by
  apply (eq_bot_iff_forall _).mpr
  intro x hx
  have hxH : x ∈ involutionCentralizer z :=
    mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hx z).symm
  have hxZ : (⟨x, hxH⟩ : involutionCentralizer z) ∈ center (involutionCentralizer z) :=
    mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp hx g)
  have hxline : x ∈ zpowers z := h.centralizer_center_image ▸ mem_map_of_mem _ hxZ
  have hcases : x = 1 ∨ x = z := by
    classical
    rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hxline
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hxline
    have hn2 := Finset.mem_range.mp hn
    interval_cases n <;> simp_all
  rcases hcases with he | rfl
  · exact he
  · exfalso
    apply h.centralizer_ne_top
    exact top_unique fun g _ => mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hx g)

public theorem centralizer_odd_index (h : HTypeAt z) (hc : OneInvolutionClass G) :
    Odd (involutionCentralizer z).index :=
  odd_index_centralizer_of_one_involution_class z h.involution
    (fun _ ht => hc.isConj h.involution ht)

public theorem centralizer_sylow_card (h : HTypeAt z)
    (S : Sylow 2 (involutionCentralizer z)) : Nat.card S = 128 := by
  rw [S.card_eq_multiplicity, h.centralizer_card]
  decide +kernel

public theorem sylow_card_of_one_class (h : HTypeAt z) (hc : OneInvolutionClass G)
    (S : Sylow 2 G) : Nat.card S = 128 := by
  let T : Sylow 2 (involutionCentralizer z) := Classical.choice inferInstance
  obtain ⟨e⟩ := sylow_equiv_of_odd_index (involutionCentralizer z) (h.centralizer_odd_index hc)
    (MulEquiv.refl _) S T
  exact (Nat.card_congr e.toEquiv).trans (h.centralizer_sylow_card T)

end HTypeAt
end CFSG.Quasithin.Janko23
