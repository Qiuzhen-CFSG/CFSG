module

public import Theory.GroupTheory.SylowCentralizerConjugacy
public import Theory.GroupTheory.PGroup.NormalExtraspecialDerivedCenter

/-!
# Nonfusion from a saturated common centralizer

Let `z` be central in a Sylow subgroup and let `E` be the Sylow centralizer
of `t`. If `E` is proper, maximal among p-subgroups of the common centralizer,
and its ambient normalizer fixes `z`, then `z` and `t` are not conjugate.
Indeed a Sylow subgroup of `C_G(t)` containing `E` cannot properly contain it:
the p-group normalizer condition would contradict maximality. Conjugacy would
then give `E` the same order as the original Sylow subgroup.

A companion lemma transports a characteristic derived-center line through an
injective homomorphism. The common centralizer itself need not be a p-group.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, case (b)(i), printed p.391.
-/

open Subgroup

namespace Subgroup

/-- A derived-center line controls the normalizer after any injective embedding. -/
public theorem normalizer_image_le_centralizer_of_derived_center_line
    {P G : Type*} [Group P] [Group G] [Finite G]
    (f : P →* G) (hf : Function.Injective f) (C : Subgroup P)
    (z : P) (hz : orderOf z = 2)
    (hline : (_root_.commutator C ⊓ center C).map C.subtype = zpowers z) :
    normalizer (C.map f : Set G) ≤ centralizer ({f z} : Set G) := by
  let e := C.equivMapOfInjective f hf
  let K := _root_.commutator C ⊓ center C
  let L := K.map e.toMonoidHom
  let : L.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨y, hy, rfl⟩ := hx
    let b : MulAut C := (e.trans a).trans e.symm
    have hb : b y ∈ K := characteristic_iff_le_comap.mp inferInstance b hy
    exact ⟨b y, hb, e.apply_symm_apply _⟩
  have hL : L.map (C.map f).subtype = zpowers (f z) := by
    have hcomp : (C.map f).subtype.comp e.toMonoidHom = f.comp C.subtype := rfl
    rw [show L = K.map e.toMonoidHom from rfl, map_map, hcomp, ← map_map,
      show K.map C.subtype = zpowers z from hline, MonoidHom.map_zpowers]
  exact normalizer_le_centralizer_of_characteristic_involution _ L _
    ((orderOf_injective f hf z).trans hz) hL

end Subgroup

namespace Sylow

/-- Normalizer control excludes fusion for a saturated proper Sylow centralizer. -/
public theorem not_isConj_of_saturated_common_centralizer_normalizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (z t : S) (hzc : z ∈ center S)
    (hproper : centralizer ({t} : Set S) ≠ ⊤)
    (hsat : ∀ V : Subgroup G, IsPGroup p V →
      (centralizer ({t} : Set S)).map (S : Subgroup G).subtype ≤ V →
      V ≤ centralizer ({(z : G), (t : G)} : Set G) →
      V = (centralizer ({t} : Set S)).map (S : Subgroup G).subtype)
    (hnorm : normalizer ((centralizer ({t} : Set S)).map
      (S : Subgroup G).subtype : Set G) ≤ centralizer ({(z : G)} : Set G)) :
    ¬ IsConj (z : G) (t : G) := by
  intro hconj
  let D := centralizer ({(t : G)} : Set G)
  let N := centralizer ({(z : G)} : Set G)
  let E := (centralizer ({t} : Set S)).map (S : Subgroup G).subtype
  have hED : E ≤ D := by
    dsimp only [E, D]
    rw [map_subtype_centralizer_singleton]
    exact inf_le_right
  have hSN : (S : Subgroup G) ≤ N := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hzc ⟨s, hs⟩))
  let R := S.subtype hSN
  have hEp : IsPGroup p E := (S.isPGroup'.to_subgroup _).map _
  obtain ⟨T, hET⟩ := (hEp.comap_subtype (K := D)).exists_le_sylow
  let K := E.subgroupOf D
  have hKT : K ≤ (T : Subgroup D) := hET
  have hKtop : K.subgroupOf (T : Subgroup D) = ⊤ := by
    by_contra hne
    let : Group.IsNilpotent T := T.isPGroup'.isNilpotent
    let U := normalizer (K.subgroupOf (T : Subgroup D) : Set T)
    obtain ⟨u, hu, hun⟩ := SetLike.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent
        (K.subgroupOf (T : Subgroup D)) (lt_top_iff_ne_top.mpr hne))
    let V := (U.map (T : Subgroup D).subtype).map D.subtype
    have hUV : ∀ v : T, v ∈ U → ((v : D) : G) ∈ V := by
      intro v hv
      exact mem_map_of_mem D.subtype (mem_map_of_mem (T : Subgroup D).subtype hv)
    have hEV : E ≤ V := by
      intro x hx
      let y : T := ⟨⟨x, hED hx⟩, hET hx⟩
      exact hUV y (le_normalizer (show y ∈ K.subgroupOf (T : Subgroup D) from hx))
    have hVC : V ≤ centralizer ({(z : G), (t : G)} : Set G) := by
      rintro x ⟨d, ⟨v, hv, rfl⟩, rfl⟩
      have hvN : (v : D) ∈ normalizer (K : Set D) := by
        change v ∈ normalizer (K.subgroupOf (T : Subgroup D) : Set T) at hv
        rw [← subgroupOf_normalizer_eq hKT] at hv
        exact hv
      have hvE : ((v : D) : G) ∈ normalizer (E : Set G) := by
        rw [← map_subgroupOf_eq_of_le hED]
        exact K.le_normalizer_map D.subtype (mem_map_of_mem D.subtype hvN)
      intro a ha
      rcases Set.mem_insert_iff.mp ha with rfl | ha
      · exact (mem_centralizer_singleton_iff.mp (hnorm hvE)).symm
      · have ha' : a = (t : G) := Set.mem_singleton_iff.mp ha
        subst a
        exact (mem_centralizer_singleton_iff.mp (v : D).property).symm
    have hV := hsat V (((T.isPGroup'.to_subgroup U).map _).map _) hEV hVC
    have huV := hUV u hu
    rw [hV] at huV
    exact hun huV
  have hTK : (T : Subgroup D) = K :=
    le_antisymm (subgroupOf_eq_top.mp hKtop) hKT
  have hTcard : Nat.card T = Nat.card E :=
    (Nat.card_congr (MulEquiv.subgroupCongr hTK).toEquiv).trans
      (Nat.card_congr (subgroupOfEquivOfLe hED).toEquiv)
  have hDN : Nat.card D = Nat.card N := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    let f : G ≃* G := MulAut.conj g
    have hfz : f z = t := hg
    apply (Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)).symm
    intro a
    change a ∈ N ↔ f a ∈ D
    simp only [N, D, mem_centralizer_singleton_iff]
    constructor
    · intro ha
      simpa only [map_mul, hfz] using congrArg f ha
    · intro ha
      apply f.injective
      simpa only [map_mul, hfz] using ha
  have hTR : Nat.card T = Nat.card R := by
    rw [T.card_eq_multiplicity, R.card_eq_multiplicity, hDN]
  have hRS : Nat.card R = Nat.card S :=
    Nat.card_congr (subgroupOfEquivOfLe hSN).toEquiv
  have hES : Nat.card (centralizer ({t} : Set S)) = Nat.card S := by
    rw [← card_map_of_injective (S : Subgroup G).subtype_injective]
    exact hTcard.symm.trans (hTR.trans hRS)
  apply hproper
  apply eq_of_le_of_card_ge le_top
  rw [Nat.card_congr (topEquiv (G := S)).toEquiv]
  exact hES.ge

end Sylow
