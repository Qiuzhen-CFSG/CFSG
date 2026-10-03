module

public import Stellmacher.Recognition.Parrott.DerivedVHyperplane
public import Stellmacher.Recognition.Parrott.DerivedCoreConjugacy
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# Noninvariance of the derived-core centralizer hyperplane

Put H=C_G(z), J=O₂(H), and let v lie in the ambient image of J′ outside
⟨z⟩, with |C_H(v)|=512. No element of order four in H/J preserves the
image of C_J(v) in J/J′.

Indeed, such invariance makes a representative normalize C_J(v), hence
its center ⟨z,v⟩. The representative fixes z, so sends v to v or zv.
A conjugation in J interchanges these two lifts. Adjusting the representative
therefore puts its quotient in the image of C_H(v), which has order two.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and the first paragraph of p.677.
-/

open Subgroup

namespace Stellmacher.Recognition

/-- An order-four quotient element moves some point of the actual hyperplane
obtained from the core centralizer of a derived-core involution. -/
public theorem parrott_derived_core_centralizer_hyperplane_noninvariant
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let i := H.subtype.comp J.subtype
    let E := (commutator J).map i
    ∀ v : G, v ∈ E → v ∉ zpowers z →
      ∀ V : Subgroup G, H ⊓ centralizer ({v} : Set G) = V → Nat.card V = 512 →
      let q := QuotientGroup.mk' (commutator J)
      let C := (centralizer ({v} : Set G)).comap i
      let U := C.map q
      ∀ f : (H ⧸ J) →* MulAut (J ⧸ commutator J), Function.Injective f →
        (∀ (a : H) (d d' : J), (d' : H) = a * (d : H) * a⁻¹ →
          f (QuotientGroup.mk' J a) (q d) = q d') →
        ∀ g : H ⧸ J, orderOf g = 4 → ∃ u ∈ U, f g u ∉ U := by
  classical
  intro H J i E v hv hvz V hV hVcard q C U f _hf heval g hg
  by_contra hnone
  have hinv : ∀ u ∈ U, f g u ∈ U := by
    simpa only [not_exists, not_and, not_not] using hnone
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective J g
  obtain ⟨hDC, _, _⟩ := parrott_derived_core_centralizer_hyperplane z h v hv hvz
  have hpre : U.comap q = C := by
    apply comap_map_eq_self
    change (QuotientGroup.mk' (commutator J)).ker ≤ C
    rw [QuotientGroup.ker_mk']
    exact hDC
  let K := C.map i
  have hK : K = J.map H.subtype ⊓ centralizer ({v} : Set G) := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨mem_map_of_mem H.subtype c.property, hc⟩
    · rintro ⟨⟨xH, hxJ, rfl⟩, hxv⟩
      exact ⟨⟨xH, hxJ⟩, hxv, rfl⟩
  let α := MulAut.conj (a : G)
  have hmap : K.map α.toMonoidHom ≤ K := by
    rintro x ⟨y, ⟨c, hc, rfl⟩, rfl⟩
    let c' : J := ⟨a * (c : H) * a⁻¹,
      (inferInstance : J.Normal).conj_mem c c.property a⟩
    have hc' : c' ∈ C := by
      rw [← hpre]
      change q c' ∈ U
      rw [← heval a c c' rfl]
      exact hinv (q c) (mem_map_of_mem q hc)
    exact ⟨c', hc', rfl⟩
  have hnorm : (a : G) ∈ normalizer (K : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact eq_of_le_of_card_ge hmap
      (card_map_of_injective (K := K) α.injective).ge
  have hcenter : (center K).map K.subtype = closure ({z, v} : Set G) := by
    apply parrott_derived_intermediate_centralizer_center z h v hv hvz K
    · exact hK.ge
    · rw [hK]
      exact inf_le_inf_right _ (map_subtype_le _)
  have hvcenter : v ∈ (center K).map K.subtype := by
    rw [hcenter]
    exact subset_closure (by simp)
  obtain ⟨vK, hvK, hvKeq⟩ := hvcenter
  let β := K.normalizerMonoidHom ⟨(a : G), hnorm⟩
  have hvpair : α v ∈ closure ({z, v} : Set G) := by
    rw [← hcenter, ← hvKeq]
    have hchar := characteristic_iff_map_le.mp
      (inferInstance : (center K).Characteristic) β
    exact mem_map_of_mem K.subtype (hchar (mem_map_of_mem β.toMonoidHom hvK))
  have haz : α z = z :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp a.property)
  have hvne : v ≠ 1 := fun heq => hvz (heq ▸ (zpowers z).one_mem)
  have hvnez : v ≠ z := fun heq => hvz (heq ▸ mem_zpowers z)
  obtain ⟨hv2, hzv⟩ := parrott_derived_noncentral_involution z h v hv hvz
  have hzsq : z * z = 1 := by simpa only [h.involution, pow_two] using pow_orderOf_eq_one z
  have hvsq : v * v = 1 := by simpa only [hv2, pow_two] using pow_orderOf_eq_one v
  have hav : α v = v ∨ α v = z * v := by
    rcases (mem_closure_pair_iff z v hzsq hvsq hzv (α v)).mp hvpair with
      hh | hh | hh | hh
    · exact (hvne (α.injective (hh.trans α.map_one.symm))).elim
    · exact (hvnez (α.injective (hh.trans haz.symm))).elim
    · exact Or.inl hh
    · exact Or.inr hh
  have hlift : ∃ b : H, (b : G) * v * (b : G)⁻¹ = v ∧
      QuotientGroup.mk' J b = QuotientGroup.mk' J a := by
    rcases hav with ha | ha
    · exact ⟨a, ha, rfl⟩
    · obtain ⟨j, hj, hjv⟩ := parrott_derived_central_twist_conjugator z h v hv hvz
      refine ⟨j⁻¹ * a, ?_, ?_⟩
      · change ((j : G)⁻¹ * (a : G)) * v * ((j : G)⁻¹ * (a : G))⁻¹ = v
        calc
          _ = (j : G)⁻¹ * ((a : G) * v * (a : G)⁻¹) * (j : G) := by group
          _ = (j : G)⁻¹ * ((j : G) * v * (j : G)⁻¹) * (j : G) := by
            change (j : G)⁻¹ * α v * (j : G) = _
            rw [ha, hjv]
          _ = v := by group
      · have hjq : QuotientGroup.mk' J j = 1 := (QuotientGroup.eq_one_iff j).mpr hj
        rw [map_mul, map_inv, hjq, inv_one, one_mul]
  obtain ⟨b, hb, hba⟩ := hlift
  let W := (V.subgroupOf H).map (QuotientGroup.mk' J)
  have hWcard : Nat.card W = 2 :=
    parrott_derived_local_centralizer_quotient_card z h v hv hvz V hV hVcard
  have haW : QuotientGroup.mk' J a ∈ W := by
    rw [← hba]
    apply mem_map_of_mem
    change (b : G) ∈ V
    rw [← hV]
    exact ⟨b.property, mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hb)⟩
  have hdiv := orderOf_dvd_natCard (⟨QuotientGroup.mk' J a, haW⟩ : W)
  rw [← orderOf_submonoid, hg, hWcard] at hdiv
  norm_num at hdiv

end Stellmacher.Recognition
