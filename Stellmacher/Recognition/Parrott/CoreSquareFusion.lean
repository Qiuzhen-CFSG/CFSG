module

public import Stellmacher.Recognition.Parrott.CoreQuotientAction
public import Stellmacher.Recognition.Parrott.DerivedCoreConjugacy
public import Stellmacher.Recognition.Parrott.LocalGeneratorData
public import Theory.GroupAction.FiveFourSixteenOrbitCensus
public import Theory.GroupTheory.ElementarySecondCenterSquares

/-!
# Noncentral squares in Parrott's original core

Put H = C_G(z) and J = O₂(H). Every square in J outside ⟨z⟩ is conjugate
to the supplied normalizer-frame element v. All frame coordinates are preserved.

The faithful action of H/J on J/J′ has two nonidentity orbits. The frame
involution a lies outside J′, since its commutator with w ∈ J′ is z ≠ 1.
Every lift in its quotient orbit has central square: changing a lift by the
elementary subgroup J′ = Z₂(J) preserves its square modulo Z(J). The other
orbit contains b, whose square is v ∉ ⟨z⟩, and therefore contains the quotient
of every element with noncentral square. Conjugating its square leaves at
most a factor z. The existing derived-core conjugator fuses v with zv.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and the assertion (c*)² ∼_H v immediately before equation (4), p.678.
-/

open Subgroup MulAction
open scoped IsMulCommutative

namespace Stellmacher.Recognition

private theorem same_orbit_of_two_orbits
    {A X : Type*} [Group A] [MulAction A X]
    (u v a b c : X)
    (ha : a ∈ orbit A u ∨ a ∈ orbit A v)
    (hb : b ∈ orbit A u ∨ b ∈ orbit A v)
    (hc : c ∈ orbit A u ∨ c ∈ orbit A v)
    (hba : b ∉ orbit A a) (hca : c ∉ orbit A a) : c ∈ orbit A b := by
  rcases ha with hau | hav
  · have hueq : orbit A u = orbit A a := (orbit_eq_iff.mpr hau).symm
    have hbv : b ∈ orbit A v := hb.resolve_left (by rwa [hueq])
    have hcv : c ∈ orbit A v := hc.resolve_left (by rwa [hueq])
    rwa [orbit_eq_iff.mpr hbv]
  · have hveq : orbit A v = orbit A a := (orbit_eq_iff.mpr hav).symm
    have hbu : b ∈ orbit A u := hb.resolve_right (by rwa [hveq])
    have hcu : c ∈ orbit A u := hc.resolve_right (by rwa [hveq])
    rwa [orbit_eq_iff.mpr hbu]

private theorem core_square_conjugate_mod_center
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let embed := H.subtype.comp J.subtype
    ∀ a b : J, a ^ 2 = 1 → QuotientGroup.mk' (commutator J) a ≠ 1 →
      embed b ^ 2 ∉ zpowers z →
      ∀ j : J, embed j ^ 2 ∉ zpowers z →
        ∃ g : H, embed j ^ 2 / ((g : G) * embed b ^ 2 * (g : G)⁻¹) ∈ zpowers z := by
  classical
  intro H J embed a b ha2 han hbnon
  let D := commutator J
  have hinj : Function.Injective embed := H.subtype_injective.comp J.subtype_injective
  obtain ⟨hZmap, _, _, _, hUpper, hElem, _, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 D := hElem
  obtain ⟨hVelem, hVcard⟩ := parrott_core_abelianization_structure z h
  let : IsElementaryAbelian 2 (J ⧸ D) := hVelem
  let q := QuotientGroup.mk' D
  have hcenter (j : J) : j ∈ center J ↔ embed j ∈ zpowers z := by
    rw [← hZmap]
    exact ⟨mem_map_of_mem embed, fun ⟨k, hk, he⟩ => hinj he ▸ hk⟩
  have hnonzero (j : J) (hj : embed j ^ 2 ∉ zpowers z) : q j ≠ 1 := by
    intro hjq
    have hjD : j ∈ D := (QuotientGroup.eq_one_iff j).mp hjq
    have hj2 : j ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian j hjD
    apply hj
    rw [← map_pow, hj2, map_one]
    exact one_mem _
  have hbn : q b ≠ 1 := hnonzero b hbnon
  let ι : H →* normalizer (J : Set H) :=
    (MonoidHom.id H).codRestrict _ (by intro g; rw [normalizer_eq_top]; trivial)
  let jAct : H →* MulAut J := J.normalizerMonoidHom.comp ι
  let : MulDistribMulAction H J := MulDistribMulAction.compHom J jAct
  have hact (g : H) (j : J) : embed (g • j) = (g : G) * embed j * (g : G)⁻¹ := rfl
  obtain ⟨ρ, hρ, hcompat⟩ := parrott_core_quotient_action z h
  let : MulDistribMulAction H (J ⧸ D) :=
    MulDistribMulAction.compHom (J ⧸ D) (ρ.comp (QuotientGroup.mk' J))
  have hqact (g : H) (j : J) : g • q j = q (g • j) := hcompat g j (g • j) rfl
  have hbad (j : J) (hj : q j ∈ orbit H (q a)) : embed j ^ 2 ∈ zpowers z := by
    obtain ⟨g, hg⟩ := hj
    have heq : q j = q (g • a) := hg.symm.trans (hqact g a)
    have hs := sq_eq_mod_center_of_eq_mod_elementary D hUpper.le j (g • a) heq
    have hga : (g • a) ^ 2 = 1 := by rw [← smul_pow', ha2, smul_one]
    rw [hga, map_one] at hs
    have hjc : j ^ 2 ∈ center J := (QuotientGroup.eq_one_iff _).mp hs
    simpa only [map_pow] using (hcenter (j ^ 2)).mp hjc
  obtain ⟨φ, hφ, ⟨model⟩⟩ := h.quotient_model
  let modelMap := ρ.comp model.symm.toMonoidHom
  obtain ⟨u, v, hu, hv, _, _, hcover⟩ :=
    Theory.GroupAction.five_four_sixteen_orbit_census hVcard φ hφ modelMap
      (hρ.comp model.symm.injective)
  have hrange (w : J ⧸ D) : Set.range (fun g => modelMap g w) = orbit H w := by
    ext w'
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨gH, hgH⟩ := QuotientGroup.mk'_surjective J (model.symm g)
      exact ⟨gH, by change ρ (QuotientGroup.mk' J gH) w = _; rw [hgH]; rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨model (QuotientGroup.mk' J g), by simp [modelMap]; rfl⟩
  have hcover' (w : J ⧸ D) (hw : w ≠ 1) : w ∈ orbit H u ∨ w ∈ orbit H v := by
    simpa only [hrange, Set.mem_union] using hcover w hw
  have hbavoid : q b ∉ orbit H (q a) := fun hh => hbnon (hbad b hh)
  intro j hj
  have hsame : q j ∈ orbit H (q b) :=
    same_orbit_of_two_orbits u v (q a) (q b) (q j)
      (hcover' (q a) han) (hcover' (q b) hbn) (hcover' (q j) (hnonzero j hj))
      hbavoid (fun hh => hj (hbad j hh))
  obtain ⟨g, hg⟩ := hsame
  have heq : q j = q (g • b) := hg.symm.trans (hqact g b)
  have hs := sq_eq_mod_center_of_eq_mod_elementary D hUpper.le j (g • b) heq
  have hdiff : embed j ^ 2 / embed (g • b) ^ 2 ∈ zpowers z := by
    have hm := (hcenter (j ^ 2 / (g • b) ^ 2)).mp (QuotientGroup.eq_iff_div_mem.mp hs)
    simpa only [map_div, map_pow] using hm
  have hgb : embed (g • b) ^ 2 = (g : G) * embed b ^ 2 * (g : G)⁻¹ := by
    rw [hact, ← MulAut.conj_apply, ← map_pow]
    rfl
  exact ⟨g, hgb ▸ hdiff⟩

/-- Noncentral squares are fused to v using only an involution outside the
derived core and a square root of v. In particular, no equations (11)–(19)
are needed. -/
public theorem parrott_core_square_isConj_v_of_initial_elements
    {G : Type*} [Group G] [Finite G] {z : G}
    (h : ParrottCentralizerHypotheses z)
    {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
    (a₀ b₀ w₀ : G)
    (haJ : a₀ ∈ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype)
    (hbJ : b₀ ∈ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype)
    (hwE : w₀ ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype))
    (ha_sq : a₀ ^ 2 = 1) (hb_sq : b₀ ^ 2 = n.v)
    (haw_eq : Tits.parrottCommutator a₀ w₀ = z) :
    ∀ a : G, a ∈ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype → a ^ 2 ∉ zpowers z → IsConj (a ^ 2) n.v := by
  classical
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let embed : J →* G := H.subtype.comp J.subtype
  have hinj : Function.Injective embed := H.subtype_injective.comp J.subtype_injective
  obtain ⟨_, _, _, _, _, hElem, _, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 D := hElem
  let q := QuotientGroup.mk' D
  obtain ⟨aH, haH, hea⟩ := haJ
  obtain ⟨bH, hbH, heb⟩ := hbJ
  let a : J := ⟨aH, haH⟩
  let b : J := ⟨bH, hbH⟩
  have hea : embed a = a₀ := hea
  have heb : embed b = b₀ := heb
  have ha2 : a ^ 2 = 1 := hinj (by rw [map_pow, hea, ha_sq, map_one])
  have hb2 : embed b ^ 2 = n.v := by rw [heb, hb_sq]
  have hvz : n.v ∉ zpowers z := by
    intro hv
    apply n.v_not_mem_core_center
    rw [n.core_center_eq]
    exact mem_sup_left hv
  have han : q a ≠ 1 := by
    intro haq
    have haD : a ∈ D := (QuotientGroup.eq_one_iff a).mp haq
    have hw : w₀ ∈ D.map embed := hwE
    obtain ⟨w, hw, hew⟩ := hw
    have haw : Commute (embed a) (embed w) := by
      have hh := congrArg (fun d : D => embed d) (mul_comm (⟨a, haD⟩ : D) ⟨w, hw⟩)
      exact hh
    have hz : z = 1 := by
      rw [← haw_eq]
      exact (Tits.parrottCommutator_eq_one_iff _ _).mpr (by simpa [hea, hew] using haw)
    have hzorder := h.involution
    simp [hz] at hzorder
  intro c hc hcz
  obtain ⟨cH, hcH, rfl⟩ := hc
  let j : J := ⟨cH, hcH⟩
  change embed j ^ 2 ∉ zpowers z at hcz
  change IsConj (embed j ^ 2) n.v
  obtain ⟨g, hdiff⟩ := core_square_conjugate_mod_center z h a b ha2 han
    (by rwa [hb2]) j hcz
  change embed j ^ 2 / ((g : G) * embed b ^ 2 * (g : G)⁻¹) ∈ zpowers z at hdiff
  rw [hb2] at hdiff
  let v' := (g : G) * n.v * (g : G)⁻¹
  have hconj : IsConj n.v v' := isConj_iff.mpr ⟨g, rfl⟩
  rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hdiff
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hdiff
  have hi2 := Finset.mem_range.mp hi
  interval_cases i
  · have heq' : embed j ^ 2 = v' := div_eq_one.mp (by simpa using he.symm)
    rw [heq']
    exact hconj.symm
  · have heq' : embed j ^ 2 = z * v' :=
      div_eq_iff_eq_mul.mp (by simpa using he.symm)
    obtain ⟨k, _, hk⟩ := parrott_derived_central_twist_conjugator z h n.v n.v_mem_inf.1 hvz
    have htwist : IsConj n.v (z * n.v) := isConj_iff.mpr ⟨k, hk⟩
    have hgz : (g : G) * z = z * (g : G) := mem_centralizer_singleton_iff.mp g.property
    have hlast : IsConj (z * n.v) (embed j ^ 2) := by
      apply isConj_iff.mpr
      refine ⟨g, ?_⟩
      rw [heq']
      change (g : G) * (z * n.v) * (g : G)⁻¹ = z * ((g : G) * n.v * (g : G)⁻¹)
      calc
        (g : G) * (z * n.v) * (g : G)⁻¹ = ((g : G) * z) * n.v * (g : G)⁻¹ := by group
        _ = z * ((g : G) * n.v * (g : G)⁻¹) := by rw [hgz]; group
    exact (htwist.trans hlast).symm

/-- Every noncentral square in the original two-core belongs to the conjugacy
class of the supplied v. The witnesses and coordinates of the supplied frame
are retained literally. -/
public theorem ParrottSylowGeneratorData.core_square_isConj_v
    {G : Type*} [Group G] [Finite G] {z : G}
    (h : ParrottCentralizerHypotheses z)
    {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
    (f : ParrottSylowGeneratorData n) :
    ∀ a : G, a ∈ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype → a ^ 2 ∉ zpowers z → IsConj (a ^ 2) n.v := by
  exact parrott_core_square_isConj_v_of_initial_elements h f.a f.b f.w
    (by rw [← f.core_generators]; exact subset_closure (by simp))
    (by rw [← f.core_generators]; exact subset_closure (by simp))
    (by rw [← f.derived_basis]; exact subset_closure (by simp))
    f.a_sq f.eq03_b f.eq02_aw

end Stellmacher.Recognition
