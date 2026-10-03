module

public import Stellmacher.Recognition.Parrott.DerivedCoreConjugacy
public import Stellmacher.Recognition.Parrott.DerivedLocalCenters
public import Stellmacher.Recognition.Parrott.DerivedQuotientAction
public import Theory.GroupAction.FiveFourSixteenOrbitCensus

/-!
# The two conjugacy classes in Parrott's derived core

For H=C_G(z), J=O₂(H), and E the ambient image of J′, the elements of
E outside ⟨z⟩ form two H-conjugacy classes. Their centralizers in H have
orders 1024 and 512. The faithful action on J′/Z(J) has orbits of sizes
five and ten, and the two lifts of each nonidentity point are J-conjugate.
Thus their inverse images are H-orbits of sizes ten and twenty;
orbit–stabilizer and |H|=10240 give the asserted centralizer orders.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
p.674, the local-centralizer paragraph.
-/

open Subgroup MulAction

namespace Stellmacher.Recognition

/-- The noncentral derived-core elements have exactly two H-conjugacy classes,
with the indicated centralizer orders. Conjugators are actual elements of H. -/
public theorem parrott_derived_conjugacy_census
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∃ t v : G, t ∈ E ∧ t ∉ zpowers z ∧ v ∈ E ∧ v ∉ zpowers z ∧
      Nat.card (H ⊓ centralizer ({t} : Set G) : Subgroup G) = 1024 ∧
      Nat.card (H ⊓ centralizer ({v} : Set G) : Subgroup G) = 512 ∧
      ∀ u : G, u ∈ E → u ∉ zpowers z →
        (∃ a : H, (a : G) * t * (a : G)⁻¹ = u) ∨
        (∃ a : H, (a : G) * v * (a : G)⁻¹ = u) := by
  classical
  intro H J E
  let D := commutator J
  let Z := (center J).subgroupOf D
  let embed : D →* G := (H.subtype.comp J.subtype).comp D.subtype
  have hinj : Function.Injective embed :=
    H.subtype_injective.comp (J.subtype_injective.comp D.subtype_injective)
  have hmem (d : D) : embed d ∈ E := ⟨d, d.property, rfl⟩
  obtain ⟨hZmap, _, _, _, _, _, hDcard, _⟩ := parrott_centralizer_structure z h
  obtain ⟨hElem, hQcard⟩ := parrott_derived_quotient_structure z h
  let : IsElementaryAbelian 2 (D ⧸ Z) := hElem
  let q := QuotientGroup.mk' Z
  have hzero (d : D) : q d = 1 ↔ embed d ∈ zpowers z := by
    change (d : D ⧸ Z) = 1 ↔ embed d ∈ zpowers z
    rw [QuotientGroup.eq_one_iff, ← hZmap]
    constructor
    · intro hd
      exact mem_map_of_mem (H.subtype.comp J.subtype) hd
    · rintro ⟨j, hj, heq⟩
      have hjd : j = (d : J) :=
        (H.subtype_injective.comp J.subtype_injective) heq
      change (d : J) ∈ center J
      exact hjd ▸ hj
  have hZcard : Nat.card Z = 2 := by
    have hc := Z.index_mul_card
    change Nat.card (D ⧸ Z) * Nat.card Z = Nat.card D at hc
    rw [hQcard, hDcard] at hc
    omega
  let ι : H →* normalizer (J : Set H) :=
    (MonoidHom.id H).codRestrict _ (by intro a; rw [normalizer_eq_top]; trivial)
  let jAct : H →* MulAut J := J.normalizerMonoidHom.comp ι
  let : MulDistribMulAction H J := MulDistribMulAction.compHom J jAct
  let : IsInvariant H J D := isInvariant_of_characteristic D
  have hact (a : H) (d : D) :
      embed (a • d) = (a : G) * embed d * (a : G)⁻¹ := rfl
  have hfiber (d d' : D) (hd : q d ≠ 1) (heq : q d = q d') :
      ∃ a : H, a • d = d' := by
    have hz : embed d' / embed d ∈ zpowers z := by
      rw [← hZmap]
      have hc := QuotientGroup.eq_iff_div_mem.mp heq.symm
      exact mem_map_of_mem (H.subtype.comp J.subtype)
        (show (d' : J) / (d : J) ∈ center J from hc)
    rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hz
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hz
    have hn2 := Finset.mem_range.mp hn
    interval_cases n
    · have heq' : embed d' = embed d := div_eq_one.mp (by simpa using he.symm)
      exact ⟨1, by simpa using hinj heq'.symm⟩
    · have heq' : embed d' = z * embed d :=
        div_eq_iff_eq_mul.mp (by simpa using he.symm)
      obtain ⟨a, _, ha⟩ := parrott_derived_central_twist_conjugator z h
        (embed d) (hmem d) (by simpa only [← hzero] using hd)
      exact ⟨a, hinj ((hact a d).trans (ha.trans heq'.symm))⟩
  obtain ⟨f, hf, hcompat⟩ := parrott_derived_quotient_action z h
  have hqact (a : H) (d : D) : f (QuotientGroup.mk' J a) (q d) = q (a • d) :=
    hcompat a d (a • d) rfl
  have horbit (d : D) (hd : q d ≠ 1) :
      orbit H d = q ⁻¹' Set.range (fun b : H ⧸ J => f b (q d)) := by
    ext d'
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨QuotientGroup.mk' J a, hqact a d⟩
    · rintro ⟨b, hb⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective J b
      have heq : q (a • d) = q d' := (hqact a d).symm.trans hb
      have hne : q (a • d) ≠ 1 := by
        rw [← hqact]
        exact fun hh => hd ((f (QuotientGroup.mk' J a)).injective (hh.trans (map_one _).symm))
      obtain ⟨c, hc⟩ := hfiber (a • d) d' hne heq
      exact ⟨c * a, (mul_smul c a d).trans hc⟩
  have horbitcard (d : D) (hd : q d ≠ 1) :
      Nat.card (orbit H d) =
        2 * (Set.range (fun b : H ⧸ J => f b (q d))).ncard := by
    rw [horbit d hd]
    exact (QuotientGroup.card_preimage_mk Z _).trans (by rw [hZcard, Nat.card_coe_set_eq])
  have hcentral (d : D) :
      Nat.card (stabilizer H d) =
        Nat.card (H ⊓ centralizer ({embed d} : Set G) : Subgroup G) := by
    have heq : (stabilizer H d).map H.subtype =
        H ⊓ centralizer ({embed d} : Set G) := by
      ext a
      constructor
      · rintro ⟨b, hb, rfl⟩
        refine ⟨b.property, mem_centralizer_singleton_iff.mpr ?_⟩
        have hh := congrArg embed hb
        rw [hact] at hh
        exact mul_inv_eq_iff_eq_mul.mp hh
      · rintro ⟨haH, ha⟩
        refine ⟨⟨a, haH⟩, ?_, rfl⟩
        apply hinj
        rw [hact]
        exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp ha)
    rw [← heq, card_map_of_injective H.subtype_injective]
  have hcount (d : D) (hd : q d ≠ 1) :
      (2 * (Set.range (fun b : H ⧸ J => f b (q d))).ncard) *
        Nat.card (H ⊓ centralizer ({embed d} : Set G) : Subgroup G) = 10240 := by
    rw [← horbitcard d hd, ← hcentral, ← Nat.card_prod,
      Nat.card_congr (orbitProdStabilizerEquivGroup H d)]
    exact (h.card_and_solvable z).1
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h.quotient_model
  let modelMap := f.comp e.symm.toMonoidHom
  obtain ⟨x, y, hx, hy, hxc, hyc, hcover⟩ :=
    Theory.GroupAction.five_four_sixteen_orbit_census hQcard φ hφ modelMap
      (hf.comp e.symm.injective)
  have hrange (w : D ⧸ Z) :
      Set.range (fun b => modelMap b w) = Set.range (fun b : H ⧸ J => f b w) := by
    ext v
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨e.symm b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨e b, by simp [modelMap]⟩
  rw [hrange] at hxc hyc
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective Z x
  obtain ⟨d', rfl⟩ := QuotientGroup.mk'_surjective Z y
  refine ⟨embed d, embed d', hmem d, (hzero d).not.mp hx,
    hmem d', (hzero d').not.mp hy, ?_, ?_, ?_⟩
  · have hc := hcount d hx
    rw [hxc] at hc
    omega
  · have hc := hcount d' hy
    rw [hyc] at hc
    omega
  · rintro u ⟨j, hj, rfl⟩ hu
    let w : D := ⟨j, hj⟩
    have hw : q w ≠ 1 := (hzero w).not.mpr hu
    have hh := hcover (q w) hw
    rw [hrange, hrange] at hh
    rcases hh with hh | hh
    · left
      have hm : w ∈ orbit H d := by rw [horbit d hx]; exact hh
      obtain ⟨a, ha⟩ := hm
      exact ⟨a, (hact a d).symm.trans (congrArg embed ha)⟩
    · right
      have hm : w ∈ orbit H d' := by rw [horbit d' hy]; exact hh
      obtain ⟨a, ha⟩ := hm
      exact ⟨a, (hact a d').symm.trans (congrArg embed ha)⟩

end Stellmacher.Recognition
