module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalAction
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry

/-!
# Core-intersection geometry in the numerical branch

The first-isomorphism count on the original V-action gives
|V intersected with O₂(H)| times |V*| = 16. Once 6.2.8 excludes V in O₂(H),
the intersection has order four or eight. In the order-four branch, all
three intersections with the core, action kernel and U are exactly Z_S.
The actual image V* has order four, fixes the marked image of Z_S pointwise,
and has every displacement in that line of order two.

The minimal H-star subgroup inside an escaping C_G(z), together with its
unique maximal overgroup of T and generation parameter one, is also
constructed here for the original coset-graph argument. The graph exclusion
and the ambient A₇ contradiction remain source obligations; this module
does not assert the order-eight conclusion.

Source: Aschbacher--Smith, 6.2.8 and the beginning of 6.2.11, pp.684--686.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace LocalQuotientAction
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

theorem layer_image_card (h : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (T : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G)) :
    Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) *
      Nat.card (((layer L R).subgroupOf (Centralizer z)).map (action (T : Subgroup G) L R z)) = 16 := by
  let H := Centralizer z
  let B := (layer L R).subgroupOf H
  let f := action (T : Subgroup G) L R z
  let b := f.subgroupMap B
  let j : B →* G := H.subtype.comp B.subtype
  have hj : Function.Injective j := H.subtype_injective.comp B.subtype_injective
  have hk : b.ker.map j = layer L R ⊓ H.pCoreIn 2 := by
    rw [← layer_inf_kernel h hnatural hz ho hT hplane]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property, ?_⟩
      have hy' : (y : H) ∈ f.ker := congrArg Subtype.val hy
      rw [action_ker] at hy'
      exact hy'
    · intro hx
      let y : B := ⟨⟨x, layer_le_involution_centralizer h hz hx.1⟩, hx.1⟩
      have hy : (y : H) ∈ f.ker := by
        rw [action_ker]
        exact hx.2
      exact ⟨y, Subtype.ext hy, rfl⟩
  have hc := b.ker.card_mul_index
  rw [index_ker, b.range_eq_top_of_surjective (f.subgroupMap_surjective B), card_top] at hc
  rw [← hk, card_map_of_injective hj]
  exact hc.trans ((Nat.card_congr
    (subgroupOfEquivOfLe (layer_le_involution_centralizer h hz)).toEquiv).trans hnatural.2.1.card)

theorem four_intersection_geometry (h : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (T : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    layer L R ⊓ (Centralizer z).pCoreIn 2 = ZS (T : Subgroup G) L R ∧
    layer L R ⊓ kernel (T : Subgroup G) L R z = ZS (T : Subgroup G) L R ∧
    layer L R ⊓ sourceClosure (T : Subgroup G) L R z = ZS (T : Subgroup G) L R ∧
    ⁅layer L R, sourceClosure (T : Subgroup G) L R z⁆ ≤ ZS (T : Subgroup G) L R ∧
    Nat.card (((layer L R).subgroupOf (Centralizer z)).map (action (T : Subgroup G) L R z)) = 4 := by
  have hU := (local_closure_core h hnatural hz ho hT).1
  have hS := ZS_le_sourceClosure_intersection h hz
  have hSI : ZS (T : Subgroup G) L R ≤ layer L R ⊓ (Centralizer z).pCoreIn 2 :=
    le_inf inf_le_left ((hS.trans inf_le_left).trans hU)
  have hI : layer L R ⊓ (Centralizer z).pCoreIn 2 = ZS (T : Subgroup G) L R :=
    (eq_of_le_of_card_ge hSI (by rw [hcard, (h.natural_ZS_geometry hnatural).2.1])).symm
  have hIU : layer L R ⊓ sourceClosure (T : Subgroup G) L R z = ZS (T : Subgroup G) L R :=
    le_antisymm ((inf_le_inf_left _ hU).trans_eq hI)
      (le_inf (hS.trans inf_le_right) (hS.trans inf_le_left))
  refine ⟨hI, (layer_inf_kernel h hnatural hz ho hT hplane).trans hI, hIU, ?_, ?_⟩
  · exact (local_layer_closure_commutator h hnatural hz ho hT hplane).trans_eq hIU
  · have hc := layer_image_card h hnatural hz ho hT hplane
    rw [hcard] at hc
    omega

theorem core_card_dichotomy (h : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ Centralizer z)
    (hescape : ¬ layer L R ≤ (Centralizer z).pCoreIn 2) :
    Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4 ∨
    Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 8 := by
  let I := layer L R ⊓ (Centralizer z).pCoreIn 2
  change Nat.card I = 4 ∨ Nat.card I = 8
  have hSI : ZS (T : Subgroup G) L R ≤ I :=
    le_inf inf_le_left (((ZS_le_sourceClosure_intersection h hz).trans inf_le_left).trans
      (local_closure_core h hnatural hz ho hT).1)
  have hlo : 4 ≤ Nat.card I := (h.natural_ZS_geometry hnatural).2.1 ▸ card_le_of_le hSI
  have hhi : Nat.card I < 16 := by
    by_contra hh
    have he : I = layer L R := eq_of_le_of_card_ge inf_le_left
      (by rw [hnatural.2.1.card]; omega)
    exact hescape (he.symm.le.trans inf_le_right)
  have hdvd : Nat.card I ∣ 2 ^ 4 := by
    simpa only [hnatural.2.1.card] using card_dvd_of_le (show I ≤ layer L R from inf_le_left)
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases k <;> norm_num only [Nat.reducePow] at he <;> omega

end LocalQuotientAction

variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The minimal subgroup used at the start of 6.2.8 is an actual H-star
member inside the escaping involution centralizer. -/
theorem local_exists_hstar_in_centralizer
    (h : Hypothesis611 κ T L M R n) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hescape : ¬ centralizer ({z} : Set G) ≤ M) :
    ∃ Y ∈ Chapter3.HStar (T : Subgroup G) M,
      Y ≤ centralizer ({z} : Set G) ∧ ChapterE.generationParameter Y = 1 ∧
      (T : Subgroup G) ≤ Y ⊓ M ∧ Y ⊓ M ⋖ Y ∧
      (∀ X : Subgroup G, (T : Subgroup G) ≤ X → X ⋖ Y → X = Y ⊓ M) := by
  classical
  let S : Set (Subgroup G) := {Y | Y ∈ Chapter1.HOver G (T : Set G) ∧
    ¬ Y ≤ M ∧ Y ≤ centralizer ({z} : Set G)}
  have hS : S.Nonempty := ⟨centralizer ({z} : Set G),
    ⟨Chapter1.mem_H_of_isTwoLocal (isTwoLocal_involution_centralizer ho), hT⟩,
    hescape, le_rfl⟩
  obtain ⟨Y, hY⟩ := (Set.toFinite S).exists_minimalFor id S hS
  have hstar : Y ∈ Chapter3.HStar (T : Subgroup G) M := by
    refine ⟨⟨hY.1.1, hY.1.2.1⟩, ?_⟩
    intro X hX hXY
    exact hY.2 ⟨hX.1, hX.2, hXY.trans hY.1.2.2⟩ hXY
  exact ⟨Y, hstar, hY.1.2.2, h.generation_one Y hstar,
    Chapter3.HStar.unique_maximal T h.sylow_le hstar⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition


@[expose] public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
variable {G : Type*} [Group G]

/-- The marked center line is the literal image of Z_S in U/⟨z⟩. -/
def seedLine (T L R : Subgroup G) (z : G) : Subgroup (space T L R z) :=
  (((ZS T L R).subgroupOf (Centralizer z)).map (projection z)).subgroupOf (space T L R z)

variable [Finite G] {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

theorem seedLine_card (h : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ Centralizer z) :
    Nat.card (seedLine (T : Subgroup G) L R z) = 2 := by
  let S := (ZS (T : Subgroup G) L R).subgroupOf (Centralizer z)
  have hSH : ZS (T : Subgroup G) L R ≤ Centralizer z := h.ZS_le_T.trans hT
  have hZH : zpowers z ≤ Centralizer z := (zpowers_le.mpr hz).trans hSH
  have hZS : line z ≤ S := comap_mono (zpowers_le.mpr hz)
  have hZ : Nat.card (line z) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZH).toEquiv).trans (by rw [Nat.card_zpowers, ho])
  have hS : Nat.card S = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hSH).toEquiv).trans (h.natural_ZS_geometry hnatural).2.1
  have hc := ((line z).subgroupOf S).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hZS).toEquiv, hZ, hS] at hc
  change 2 * (line z).relIndex S = 4 at hc
  have hk : (projection z).ker = line z := QuotientGroup.ker_mk' _
  rw [← hk, relIndex_ker] at hc
  have hs : S.map (projection z) ≤ space (T : Subgroup G) L R z := le_normalClosure
  change Nat.card ((S.map (projection z)).subgroupOf _) = 2
  rw [Nat.card_congr (subgroupOfEquivOfLe hs).toEquiv]
  omega

/-- In the order-four branch the actual layer image fixes its marked line
pointwise and every displacement lies on that line. Together with the
order-four image this is the common-center transvection configuration. -/
theorem four_image_common_center (h : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (T : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    Nat.card (seedLine (T : Subgroup G) L R z) = 2 ∧
    Nat.card (((layer L R).subgroupOf (Centralizer z)).map (action (T : Subgroup G) L R z)) = 4 ∧
    ∀ a ∈ ((layer L R).subgroupOf (Centralizer z)).map (action (T : Subgroup G) L R z),
      (∀ c ∈ seedLine (T : Subgroup G) L R z, a c = c) ∧
      ∀ w, a w * w⁻¹ ∈ seedLine (T : Subgroup G) L R z := by
  have hg := four_intersection_geometry h hnatural hz ho hT hplane hcard
  refine ⟨seedLine_card h hnatural hz ho hT, hg.2.2.2.2, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  constructor
  · intro c hc
    obtain ⟨s, hs, he⟩ := hc
    change projection z s = (c : SpaceAmbient z) at he
    apply Subtype.ext
    change projection z a * (c : SpaceAmbient z) * (projection z a)⁻¹ = c
    rw [← he, ← map_inv, ← map_mul, ← map_mul]
    apply congrArg (projection z)
    apply Subtype.ext
    change a.val * s.val * a.val⁻¹ = s.val
    exact mul_inv_eq_iff_eq_mul.mpr (h.layer_centralizes_ZS ha s hs).symm
  · intro w
    have hw : (w : SpaceAmbient z) ∈
        ((sourceClosure (T : Subgroup G) L R z).subgroupOf (Centralizer z)).map (projection z) :=
      (closure_image (T : Subgroup G) L R z).symm ▸ w.property
    obtain ⟨u, hu, he⟩ := hw
    have hcomm : ⁅(a : G), (u : G)⁆ ∈ ZS (T : Subgroup G) L R :=
      hg.2.2.2.1 (commutator_mem_commutator ha hu)
    change ((action (T : Subgroup G) L R z a w : space (T : Subgroup G) L R z) * w⁻¹).val ∈
      ((ZS (T : Subgroup G) L R).subgroupOf (Centralizer z)).map (projection z)
    refine ⟨⁅a, u⁆, hcomm, ?_⟩
    change projection z ⁅a, u⁆ = projection z a * w.val * (projection z a)⁻¹ * w.val⁻¹
    rw [map_commutatorElement, commutatorElement_def, he]

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
