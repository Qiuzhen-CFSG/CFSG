module

public import Stellmacher.Recognition.Parrott.DerivedLocalFusion
public import Stellmacher.Recognition.Parrott.SecondNormalizerTransport
public import Stellmacher.Recognition.Parrott.ChosenCoreGrowthUnrestricted

/-!
# Core fusion from Parrott's actual derived normalizer identity

The t-representative obstruction uses N_G(E)=C_G(z) only to control the
normalizer of its computed omega image. The second representative is already
unrestricted. The chosen-involution exclusion then handles core elements
outside E, by transport of the supplied F and T. Thus the exact local identity
replaces the global N₂ premise throughout this core-fusion branch.

Source: Parrott (1972), Lemma 5, printed pp.676–677.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The literal derived-core normalizer identity suffices for this fusion step. -/
public theorem local_fusion_omega_derived_cases_of_derived_normalizer (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hnorm : normalizer (((commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype)) : Set G) =
      centralizer ({z} : Set G))
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G)) (t : G)
    (hlocal : centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) =
      (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G))
    (hsmall : Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) : Subgroup G) < 2048)
    (A : Subgroup G) (hA : (commutator A).map A.subtype = zpowers z) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let C := (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G)
    let W := (omega₁ (commutator C) (p := 2)).map (C.subtype.comp (commutator C).subtype)
    (W = E ∨ W = d.F ∨ W = A ∨ centralizer (W : Set G) = A) → ¬ IsConj z t := by
  intro H E C W hcases hconj
  have hAnorm : normalizer (A : Set G) ≤ H :=
    normalizer_le_centralizer_of_characteristic_involution A (commutator A)
      z h.involution hA
  apply d.local_fusion_omega_derived_obstruction h t hlocal hsmall hconj
  change normalizer (W : Set G) ≤ H
  rcases hcases with hE | hF | hWA | hCA
  · rw [hE]
    exact hnorm.le
  · rw [hF, hself]
    exact d.sylow_le_centralizer
  · rw [hWA]
    exact hAnorm
  · have hle := normalizer_le_normalizer_centralizer W
    rw [hCA] at hle
    exact hle.trans hAnorm

/-- The literal derived-core normalizer identity suffices for this fusion step. -/
public theorem derived_t_not_isConj_of_omega_bounds_of_derived_normalizer (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hnorm : normalizer (((commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype)) : Set G) =
      centralizer ({z} : Set G))
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G)) (t : G)
    (hlocal : centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) =
      (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G))
    (hcard : Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) : Subgroup G) = 1024) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let C := (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G)
    let W := (omega₁ (commutator C) (p := 2)).map (C.subtype.comp (commutator C).subtype)
    (IsConj z t → E ⊓ d.F ≤ W ∧ W ≤ E ⊔ d.F) → ¬ IsConj z t := by
  intro H J E C W hbounds hconj
  obtain ⟨hlow, hupp⟩ := hbounds hconj
  exact d.local_fusion_omega_derived_cases_of_derived_normalizer h hnorm hself t hlocal (by omega)
    (E ⊔ d.F) (d.elementary_join_commutator h)
    (d.omega_image_cases_of_bounds h (commutator C)
      (C.subtype.comp (commutator C).subtype) hlow hupp) hconj

/-- The literal derived-core normalizer identity suffices for this fusion step. -/
public theorem derived_t_not_isConj_of_derived_normalizer (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hnorm : normalizer (((commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype)) : Set G) =
      centralizer ({z} : Set G))
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ t ∈ E, t ∉ zpowers z → orderOf t = 2 → Commute z t →
      H ⊓ centralizer ({t} : Set G) =
        (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) →
      let C := (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G)
      Nat.card C = 1024 → (center C).map C.subtype = closure ({z, t} : Set G) →
      ¬ IsConj z t := by
  intro H J E t ht htz _htwo _hzt hlocal C hcard _hcenter
  exact d.derived_t_not_isConj_of_omega_bounds_of_derived_normalizer h hnorm hself t hlocal hcard
    (fun _ => d.derived_t_omega_bounds h t ht htz hcard)

end Stellmacher.Recognition.ParrottSecondElementaryData

namespace Stellmacher.Recognition

/-- Derived-core fusion under the actual local normalizer identity. -/
public theorem parrott_derived_not_isConj_of_second_normalizer_eq_of_derived_normalizer
    {G : Type*} [Group G] [Finite G]
    (z : G) (hnorm : normalizer (((commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype)) : Set G) =
      centralizer ({z} : Set G)) (h : ParrottCentralizerHypotheses z)
    (d : ParrottSecondElementaryData z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ u : G, u ∈ E → u ∉ zpowers z → ¬ IsConj z u := by
  intro H J E u hu huZ hconj
  obtain ⟨t, v, ht, htZ, hv, hvZ, ht2, hzt, hv2, hzv,
    htlocal, htcard, htcenter, hvlocal, hvcard, hvcenter, hcover⟩ :=
    parrott_derived_local_representatives z h d
  rcases hcover u hu huZ with ⟨a, ha⟩ | ⟨a, ha⟩
  · have htu : IsConj t u := isConj_iff.mpr ⟨(a : G), ha⟩
    exact d.derived_t_not_isConj_of_derived_normalizer h hnorm hself t ht htZ ht2 hzt
      htlocal htcard htcenter (hconj.trans htu.symm)
  · have hvu : IsConj v u := isConj_iff.mpr ⟨(a : G), ha⟩
    exact d.derived_v_fusion h hself v hv hvZ hv2 hzv
      hvlocal hvcard hvcenter (hconj.trans hvu.symm)

/-- Derived-core fusion under the actual local normalizer identity. -/
public theorem parrott_derived_fusion_eq_of_second_normalizer_eq_of_derived_normalizer
    {G : Type*} [Group G] [Finite G]
    (z : G)
    (hnorm : normalizer (((commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype)) : Set G) =
      centralizer ({z} : Set G)) (h : ParrottCentralizerHypotheses z)
    (d : ParrottSecondElementaryData z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ t : G, t ∈ E → IsConj z t → t = z := by
  classical
  intro H J E t ht hconj
  have htZ : t ∈ zpowers z := by
    by_contra htZ
    exact parrott_derived_not_isConj_of_second_normalizer_eq_of_derived_normalizer z hnorm h d hself
      t ht htZ hconj
  have htorder : orderOf t = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq z).trans h.involution
  have ht_cases : t = 1 ∨ t = z := by
    rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at htZ
    obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp htZ
    have hnlt : n < 2 := Finset.mem_range.mp hn
    interval_cases n
    · exact Or.inl (by simpa using heq.symm)
    · exact Or.inr (by simpa using heq.symm)
  rcases ht_cases with rfl | rfl
  · simp at htorder
  · rfl

/-- Transport the unrestricted chosen-involution exclusion to every core involution. -/
public theorem parrott_not_isConj_of_core_not_mem_derived_of_second_normalizer_eq_unrestricted
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z)
    (d : ParrottSecondElementaryData z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ u : G, u ∈ J.map H.subtype → u ∉ E → ¬ IsConj z u := by
  intro H J E u huJ huE hconj
  obtain ⟨a, haJ, rfl⟩ := huJ
  change IsConj z (a : G) at hconj
  have ha2G : orderOf (a : G) = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq z).trans h.involution
  have ha2 : orderOf a = 2 := (Subgroup.orderOf_coe a).symm.trans ha2G
  have haD : a ∉ (commutator J).map J.subtype := by
    intro haD
    apply huE
    have hmap : ((commutator J).map J.subtype).map H.subtype = E := map_map _ _ _
    exact hmap ▸ mem_map_of_mem H.subtype haD
  obtain ⟨e, hea⟩ := parrott_second_elementary_of_core_involution z h a haJ ha2 haD
  have heself : normalizer (e.F : Set G) = (e.sylow : Subgroup G) :=
    d.normalizer_eq_sylow_of_normalizer_eq_sylow e h hself
  apply parrott_not_isConj_second_involution_of_normalizer_eq_unrestricted z h e heself hderived
  simpa only [hea] using hconj

/-- The entire centralizer core is weakly closed under the actual derived normalizer identity. -/
public theorem parrott_core_fusion_eq_of_second_normalizer_eq_of_derived_normalizer
    {G : Type*} [Group G] [Finite G]
    (z : G)
    (hnorm : normalizer (((commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype)) : Set G) =
      centralizer ({z} : Set G)) (h : ParrottCentralizerHypotheses z)
    (d : ParrottSecondElementaryData z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    ∀ t : G, t ∈ J.map H.subtype → IsConj z t → t = z := by
  classical
  intro H J t ht hconj
  let E := (commutator J).map (H.subtype.comp J.subtype)
  have hderived := parrott_derived_fusion_eq_of_second_normalizer_eq_of_derived_normalizer z hnorm h d hself
  by_cases htE : t ∈ E
  · exact hderived t htE hconj
  · exact (parrott_not_isConj_of_core_not_mem_derived_of_second_normalizer_eq_unrestricted
      z h d hself hderived t ht htE hconj).elim

end Stellmacher.Recognition
