module

public import Stellmacher.Recognition.Parrott.CoreCentralizerCounts
public import Stellmacher.Recognition.Parrott.DerivedCentralizer

/-!
# Centers of centralizers of derived-core involutions

Put H=C_G(z), J=O₂(H), and let E be the ambient image of J′. For every
t in E outside ⟨z⟩, the core centralizer has order 256. Every subgroup
between C_J(t) and C_H(t) has center with ambient image ⟨z,t⟩. In
particular this applies to the centralizer in the supplied Sylow subgroup.

The commutator-pairing formula |U| |C_J(U)|=1024 first computes C_J(t)
by taking U=⟨z,t⟩. A centralizer containing C_J(t) contains E, so its
center lies in C_G(E)=E. Apply the same formula to this center: its
centralizer in J contains C_J(t), forcing its order to be at most four.
It already contains the four-group ⟨z,t⟩, giving equality.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674, property (d) and the local-centralizer paragraph.
-/

open Subgroup

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem card_subgroupOf_eq_inf (A K : Subgroup G) :
    Nat.card (A.subgroupOf K) = Nat.card (K ⊓ A : Subgroup G) := by
  rw [← card_map_of_injective (K := A.subgroupOf K) K.subtype_injective,
    subgroupOf_map_subtype, inf_comm]

/-- The pairing count expressed entirely by ambient subgroup intersections. -/
public theorem parrott_core_inf_centralizer_card
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ U : Subgroup G, zpowers z ≤ U → U ≤ E →
      Nat.card U * Nat.card (J.map H.subtype ⊓ centralizer (U : Set G) : Subgroup G) =
        1024 := by
  intro H J E U hzU hUE
  have hc := parrott_core_subgroup_centralizer_card z h U hzU hUE
  rwa [card_subgroupOf_eq_inf] at hc

private theorem derived_basic (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    IsElementaryAbelian 2 E ∧ z ∈ E ∧ E ≤ J.map H.subtype ∧ J.map H.subtype ≤ H := by
  intro H J E
  obtain ⟨hZ, _, _, _, hUpper, hElem, _, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 (commutator J) := hElem
  have hZD : center J ≤ commutator J := by
    rw [hUpper, ← Subgroup.upperCentralSeries_one]
    exact Subgroup.upperCentralSeries_mono J (by decide : 1 ≤ 2)
  refine ⟨IsElementaryAbelian.map (H.subtype.comp J.subtype), ?_, ?_, map_subtype_le J⟩
  · apply map_mono hZD
    rw [hZ]
    exact mem_zpowers z
  · rw [show E = ((commutator J).map J.subtype).map H.subtype from
      (map_map _ _ _).symm]
    exact map_mono (map_subtype_le _)

/-- All noncentral elements of the derived core are involutions commuting with z. -/
public theorem parrott_derived_noncentral_involution
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    ∀ t : G, t ∈ E → t ∉ zpowers z → orderOf t = 2 ∧ Commute z t := by
  intro H E t ht htz
  obtain ⟨hElem, _, hEK, hKH⟩ := derived_basic z h
  let : IsElementaryAbelian 2 E := hElem
  refine ⟨orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t ht) ?_, ?_⟩
  · intro heq
    exact htz (heq ▸ (zpowers z).one_mem)
  · exact (mem_centralizer_singleton_iff.mp (hKH (hEK ht))).symm

omit [Finite G] in
private theorem pair_eq_sup (z t : G) :
    closure ({z, t} : Set G) = zpowers z ⊔ zpowers t := by
  rw [show ({z, t} : Set G) = {z} ∪ {t} from rfl, Subgroup.closure_union,
    ← zpowers_eq_closure, ← zpowers_eq_closure]

/-- The original central involution and a noncentral derived element generate a four-group. -/
public theorem parrott_derived_pair_card
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    ∀ t : G, t ∈ E → t ∉ zpowers z → Nat.card (closure ({z, t} : Set G)) = 4 := by
  intro H E t ht htz
  obtain ⟨ht2, hzt⟩ := parrott_derived_noncentral_involution z h t ht htz
  have hnorm : t ∈ normalizer (zpowers z : Set G) := by
    apply centralizer_le_normalizer
    rw [zpowers_eq_closure, centralizer_closure]
    exact mem_centralizer_singleton_iff.mpr hzt.symm.eq
  rw [pair_eq_sup, card_sup_zpowers_of_normalizing_involution (zpowers z) t
    (ht2 ▸ pow_orderOf_eq_one t) htz hnorm, Nat.card_zpowers, h.involution]

/-- Every noncentral element of E has core centralizer of order 256. -/
public theorem parrott_derived_core_centralizer_card
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ t : G, t ∈ E → t ∉ zpowers z →
      Nat.card (J.map H.subtype ⊓ centralizer ({t} : Set G) : Subgroup G) = 256 := by
  intro H J E t ht htz
  obtain ⟨_, hzE, _, hKH⟩ := derived_basic z h
  let U := closure ({z, t} : Set G)
  have hzU : zpowers z ≤ U := zpowers_le.mpr (subset_closure (by simp))
  have hUE : U ≤ E := (Subgroup.closure_le E).mpr (by
    simpa only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      using And.intro (show z ∈ E from hzE) ht)
  have hC : J.map H.subtype ⊓ centralizer (U : Set G) =
      J.map H.subtype ⊓ centralizer ({t} : Set G) := by
    rw [show centralizer (U : Set G) = centralizer ({z, t} : Set G) from centralizer_closure _]
    ext x
    simp only [mem_inf, mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq]
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩,
      fun hx => ⟨hx.1, (mem_centralizer_singleton_iff.mp (hKH hx.1)).symm, hx.2⟩⟩
  have hc := parrott_core_inf_centralizer_card z h U hzU hUE
  rw [hC, show Nat.card U = 4 from parrott_derived_pair_card z h t ht htz] at hc
  omega

/-- The center formula holds in every intermediate subgroup between the core
centralizer and the full local centralizer. -/
public theorem parrott_derived_intermediate_centralizer_center
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ t : G, t ∈ E → t ∉ zpowers z →
      ∀ C : Subgroup G,
        J.map H.subtype ⊓ centralizer ({t} : Set G) ≤ C →
        C ≤ H ⊓ centralizer ({t} : Set G) →
        (center C).map C.subtype = closure ({z, t} : Set G) := by
  intro H J E t ht htz C hKC hCH
  obtain ⟨hElem, hzE, hEK, hKH⟩ := derived_basic z h
  let : IsElementaryAbelian 2 E := hElem
  let K := J.map H.subtype
  let W := (center C).map C.subtype
  have hEC : E ≤ C := by
    intro e he
    apply hKC
    exact ⟨hEK he, mem_centralizer_singleton_iff.mpr (setLike_mul_comm he ht)⟩
  have hWE : W ≤ E := by
    rw [← show centralizer (E : Set G) = E from parrott_derived_centralizer z h]
    rintro w ⟨wC, hw, rfl⟩ e he
    exact congrArg C.subtype (mem_center_iff.mp hw ⟨e, hEC he⟩)
  have hzW : z ∈ W := by
    refine ⟨⟨z, hEC hzE⟩, mem_center_iff.mpr ?_, rfl⟩
    intro c
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hCH c.property).1)
  have htW : t ∈ W := by
    refine ⟨⟨t, hEC ht⟩, mem_center_iff.mpr ?_, rfl⟩
    intro c
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hCH c.property).2)
  have hLW : closure ({z, t} : Set G) ≤ W :=
    (Subgroup.closure_le W).mpr (by
      simpa only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
        using And.intro hzW htW)
  have hcentral : K ⊓ centralizer ({t} : Set G) ≤ K ⊓ centralizer (W : Set G) := by
    intro c hc
    refine ⟨hc.1, ?_⟩
    rintro w ⟨wC, hw, rfl⟩
    exact (congrArg C.subtype (mem_center_iff.mp hw ⟨c, hKC hc⟩)).symm
  have hbound := card_le_of_le hcentral
  rw [parrott_derived_core_centralizer_card z h t ht htz] at hbound
  have hc := parrott_core_inf_centralizer_card z h W (zpowers_le.mpr hzW) hWE
  change Nat.card W * Nat.card (K ⊓ centralizer (W : Set G) : Subgroup G) = 1024 at hc
  have hWcard : Nat.card W ≤ 4 := by nlinarith
  exact (eq_of_le_of_card_ge hLW (by
    rw [parrott_derived_pair_card z h t ht htz]
    exact hWcard)).symm

/-- For every supplied local Sylow subgroup, the center of a noncentral
derived involution centralizer maps to the specified four-group. -/
public theorem parrott_derived_sylow_centralizer_center
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ (T : Sylow 2 H) (t : G), t ∈ E → t ∉ zpowers z →
      let C := (T : Subgroup H).map H.subtype ⊓ centralizer ({t} : Set G)
      (center C).map C.subtype = closure ({z, t} : Set G) := by
  intro H J E T t ht htz C
  apply parrott_derived_intermediate_centralizer_center z h t ht htz C
  · exact inf_le_inf_right _ (map_mono (pCore_isPGroup.le_sylow_of_normal T))
  · exact inf_le_inf_right _ (map_subtype_le _)

end Stellmacher.Recognition
