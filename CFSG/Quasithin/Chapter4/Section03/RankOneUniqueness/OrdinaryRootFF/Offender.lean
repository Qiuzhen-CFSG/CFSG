module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF.Kernel
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootCore
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.OrthogonalCover
public import Theory.Representation.NormalElementaryQuotient.FixedIndex
public import Theory.GroupTheory.PerfectSmallNormalizer
import Mathlib.Tactic.FinCases

/-!
# The actual ordinary-root failure-of-factorization module

The two marked radicals have equal order. Their mutual centralizers are their
intersection, using self-centralization inside the same symplectic carrier.
The supplied equality Q = R C_Q(W) therefore bounds |U:C_U(W)| by the order
of W's image in N/C_N(U). Reducedness kills R in that action, while normal
generation of J by W proves that W's image is nontrivial. This constructs an
offender on the faithful representation already defined in Action.

The final application restricts an actual best offender inside W's image to
the actual K_Z image. It proves the FF premise needed for B.5.1 without a
classification callback. The remaining odd-cubic exclusion and model-image
comparison remain with the ordinary-root classification owner.

Source: Aschbacher–Smith 4.3.6, printed p.615, following (*) and (**).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
open Theory.SpecificGroups.SymplecticFour

private def pointCoordinates {F : Type*} [Field F] [CharP F 2] :
    pointRadical (F := F) ≃ (Fin 3 → F) where
  toFun q := ![q.val.val.val (.inl 1) (.inr 0), q.val.val.val (.inr 1) (.inr 0),
    q.val.val.val (.inl 0) (.inr 0)]
  invFun v := ⟨pointRadicalElement (v 0) (v 1) (v 2), pointRadicalElement_mem _ _ _⟩
  left_inv q := Subtype.ext (pointRadical_eq_element q.val q.property).symm
  right_inv v := by funext i; fin_cases i <;> rfl

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} (m : OrdinarySymplecticMarking c n)

omit [Finite G] in
theorem secondCore_card_eq_fullModule (hn : 1 < n) :
    Nat.card (m.second.pCoreIn 2) = Nat.card c.ordinaryModule := by
  rw [← m.pointRadical_image hn, ← m.planeRadical_image hn,
    card_map_of_injective m.modelEmbedding_injective,
    card_map_of_injective m.modelEmbedding_injective,
    card_map_of_injective pointLocal.subtype_injective,
    card_map_of_injective planeLocal.subtype_injective,
    Nat.card_congr (pointCoordinates (F := m.Field)),
    Nat.card_congr (Plane.OrthogonalCover.radicalCoordinates (F := m.Field)).toEquiv]
  rfl

include m in
omit [Finite G] in
theorem fullModule_elementary (hn : 1 < n) : IsElementaryAbelian 2 c.ordinaryModule := by
  rw [← m.planeRadical_image hn]
  let := Plane.radical_elementaryAbelian (F := m.Field)
  let := IsElementaryAbelian.map_subtype (p := 2) (H := Plane.radical (F := m.Field))
  exact IsElementaryAbelian.map m.modelEmbedding

omit [Finite G] in
theorem fullModule_inf_centralizer_secondCore (hn : 1 < n) :
    c.ordinaryModule ⊓ centralizer (m.second.pCoreIn 2 : Set G) =
      c.ordinaryModule ⊓ m.second.pCoreIn 2 := by
  let R : Subgroup (Sp m.Field) := pointRadicalAmbient
  let W : Subgroup (Sp m.Field) := planeRadicalAmbient
  have hc : W ⊓ centralizer (R : Set (Sp m.Field)) = W ⊓ R := by
    apply le_antisymm (inf_le_inf_left W (pointRadicalAmbient_selfCentralizing m.card hn))
    apply le_inf inf_le_left
    intro x hx r hr
    let := IsElementaryAbelian.map_subtype (p := 2) (H := pointRadical (F := m.Field))
    exact congrArg Subtype.val (mul_comm (⟨r, hr⟩ : R) ⟨x, hx.2⟩)
  have he := map_inf_centralizer_of_injective m.modelEmbedding m.modelEmbedding_injective W R
  rw [hc, map_inf _ _ _ m.modelEmbedding_injective] at he
  simpa only [show W.map m.modelEmbedding = c.ordinaryModule from m.planeRadical_image hn,
    show R.map m.modelEmbedding = m.second.pCoreIn 2 from m.pointRadical_image hn] using he

omit [Finite G] in
theorem secondCore_inf_centralizer_fullModule (hn : 1 < n) :
    m.second.pCoreIn 2 ⊓ centralizer (c.ordinaryModule : Set G) =
      m.second.pCoreIn 2 ⊓ c.ordinaryModule := by
  let R : Subgroup (Sp m.Field) := pointRadicalAmbient
  let W : Subgroup (Sp m.Field) := planeRadicalAmbient
  have hc : R ⊓ centralizer (W : Set (Sp m.Field)) = R ⊓ W := by
    apply le_antisymm (inf_le_inf_left R (planeRadicalAmbient_selfCentralizing m.card hn))
    apply le_inf inf_le_left
    intro x hx w hw
    let := IsElementaryAbelian.map_subtype (p := 2) (H := Plane.radical (F := m.Field))
    exact congrArg Subtype.val (mul_comm (⟨w, hw⟩ : W) ⟨x, hx.2⟩)
  have he := map_inf_centralizer_of_injective m.modelEmbedding m.modelEmbedding_injective R W
  rw [hc, map_inf _ _ _ m.modelEmbedding_injective] at he
  simpa only [show W.map m.modelEmbedding = c.ordinaryModule from m.planeRadical_image hn,
    show R.map m.modelEmbedding = m.second.pCoreIn 2 from m.pointRadical_image hn] using he

omit [Finite G] in
theorem image_card (hUN : m.rootSpan ≤ m.rootNormalizer)
    (A : Subgroup G) (hAN : A ≤ m.rootNormalizer) :
    Nat.card (image m A) = (centralizer (m.rootSpan : Set G)).relIndex A := by
  rw [image, ← relIndex_ker, projection_kernel m hUN, relIndex_subgroupOf hAN]

theorem fixedCodim_index (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (A : Subgroup G)
    (hAN : A ≤ m.rootNormalizer) :
    letI := hr.elementary
    (centralizer (A : Set G)).relIndex m.rootSpan =
      2 ^ fixedCodim (representation m hr) (image m A) := by
  let := hr.elementary
  have hc : centralizer (A.subgroupOf m.rootNormalizer : Set m.rootNormalizer) =
      (centralizer (A : Set G)).subgroupOf m.rootNormalizer := by
    ext x
    constructor
    · intro hx a ha
      exact congrArg Subtype.val (hx ⟨a, hAN ha⟩ ha)
    · intro hx a ha
      exact Subtype.ext (hx a ha)
  have he := Representation.NormalElementaryQuotient.centralizer_index_eq_fixedCodim
    (moduleSubgroup m) (projection m) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) (A.subgroupOf m.rootNormalizer)
  rw [hc, relIndex_subgroupOf hUN] at he
  exact he

omit [Finite G] in
theorem fullModule_image_ne_bot (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer)
    (hcore : m.second.pCoreIn 2 ≤ m.rootSpan) : image m c.ordinaryModule ≠ ⊥ := by
  intro he
  have hWN := (m.fullModule_le_second hn).trans m.second_le_rootNormalizer
  have hker := (Subgroup.map_eq_bot_iff _).mp he
  rw [projection_kernel m hUN] at hker
  have hWR : c.ordinaryModule ≤ m.second.pCoreIn 2 := by
    intro w hw
    have hc : w ∈ centralizer (m.second.pCoreIn 2 : Set G) :=
      centralizer_le hcore (hker (show (⟨w, hWN hw⟩ : m.rootNormalizer) ∈
        c.ordinaryModule.subgroupOf m.rootNormalizer from hw))
    exact ((fullModule_inf_centralizer_secondCore m hn).le ⟨hw,hc⟩).2
  have hJR : m.second ≤ m.second.pCoreIn 2 := by
    conv_lhs => rw [← m.fullModule_conjugateSpan_second hn]
    exact conjugateSpanBy_le hWR (m.second.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hi := image_mono m (hJR.trans (hcore.trans (span_le_core m hr hUN)))
  rw [core_image_eq_bot m hr] at hi
  exact second_image_ne_bot m hn hUN hcore (bot_unique hi)

theorem fullModule_isOffender (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer)
    (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G))) :
    letI := hr.elementary
    IsOffender (representation m hr) (image m c.ordinaryModule) := by
  let := hr.elementary
  let W := c.ordinaryModule
  let R := m.second.pCoreIn 2
  let CW := centralizer (W : Set G)
  let C := m.rootCore ⊓ CW
  have hRQ : R ≤ m.rootCore := hcore.trans (span_le_core m hr hUN)
  have hnC : C ≤ normalizer (R : Set G) := inf_le_left.trans
    (((core_centralizes_span m hr hUN).trans (centralizer_le hcore)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hidx : CW.relIndex m.rootCore = CW.relIndex R := by
    have he := relIndex_sup_of_normalizes_left R C hnC
    change C.relIndex (R ⊔ C) = C.relIndex R at he
    rw [← hQ] at he
    have hleft : C.relIndex m.rootCore = CW.relIndex m.rootCore :=
      inf_relIndex_left _ _
    have hright : C.relIndex R = CW.relIndex R := by
      rw [← inf_relIndex_right C R, ← inf_relIndex_right CW R]
      congr 1
      ext x
      exact ⟨fun h => ⟨h.1.2,h.2⟩, fun h => ⟨⟨hRQ h.2,h.1⟩,h.2⟩⟩
    exact hleft.symm.trans (he.trans hright)
  have hsymm : CW.relIndex R = (centralizer (R : Set G)).relIndex W := by
    have hR := relIndex_mul_card_of_le (show R ⊓ CW ≤ R from inf_le_left)
    have hW := relIndex_mul_card_of_le
      (show W ⊓ centralizer (R : Set G) ≤ W from inf_le_left)
    rw [inf_relIndex_left, secondCore_inf_centralizer_fullModule m hn,
      secondCore_card_eq_fullModule m hn] at hR
    rw [inf_relIndex_left, fullModule_inf_centralizer_secondCore m hn, inf_comm W R] at hW
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := (R ⊓ W : Subgroup G)))
      (hR.trans hW.symm)
  have hbound : (centralizer (W : Set G)).relIndex m.rootSpan ≤
      Nat.card (image m W) := by
    rw [image_card m hUN W ((m.fullModule_le_second hn).trans m.second_le_rootNormalizer)]
    calc
      _ ≤ CW.relIndex m.rootCore := relIndex_le_of_le_right
        (span_le_core m hr hUN) index_ne_zero_of_finite
      _ = (centralizer (R : Set G)).relIndex W := hidx.trans hsymm
      _ ≤ _ := relIndex_le_of_le_left (centralizer_le hcore) index_ne_zero_of_finite
  let := fullModule_elementary m hn
  let := IsElementaryAbelian.subgroupOf (p := 2)
    ((m.fullModule_le_second hn).trans m.second_le_rootNormalizer)
  have ha : IsElementaryTwo (image m W) :=
    ⟨fullModule_image_ne_bot m hn hr hUN hcore, IsElementaryAbelian.map (projection m)⟩
  refine ⟨ha, ?_⟩
  rw [fixedCodim_index m hr hUN W
    ((m.fullModule_le_second hn).trans m.second_le_rootNormalizer), ha.card_eq_two_pow_rank] at hbound
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hbound

theorem exists_fullModule_bestOffender (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer)
    (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G))) :
    letI := hr.elementary
    ∃ A ≤ image m c.ordinaryModule, IsBestOffender (representation m hr) A := by
  let := hr.elementary
  exact (fullModule_isOffender m hn hr hUN hcore hQ).exists_bestOffender _

theorem secondary_isFFModule (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer)
    (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hJK : m.second ≤ KZ) :
    letI := hr.elementary
    IsFFModule ((representation m hr).comp (image m KZ).subtype) := by
  let := hr.elementary
  obtain ⟨A, hAW, hA⟩ := exists_fullModule_bestOffender m hn hr hUN hcore hQ
  have hAK : A ≤ image m KZ := hAW.trans (image_mono m ((m.fullModule_le_second hn).trans hJK))
  exact ⟨A.subgroupOf (image m KZ), (hA.subgroupOf (representation m hr) hAK).isOffender _⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
