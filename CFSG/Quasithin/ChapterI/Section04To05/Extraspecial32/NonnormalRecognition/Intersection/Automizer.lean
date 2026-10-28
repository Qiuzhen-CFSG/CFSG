module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Intersection.Cardinality
public import Theory.GroupAction.ElementaryEightPointEnlargement
public import Theory.GroupTheory.EmbeddedCenterMap
public import Theory.SpecificGroups.PSL3Two.InvolutionConjugacy

/-!
# The intersection automizer and its involution fusion

Let E = Q ∩ Qᵍ for the literal left conjugate Qᵍ. Assuming E is normal
in H = C_G(z) and C_G(E) = E, conjugation identifies N_G(E)/E with
Aut(E). Indeed, H has image of order 24, hence prime index seven in the
automorphism group of order 168. The second core normalizes E and cannot
centralize z, so its image strictly enlarges the image of H.

This constructs the quotient equivalence with the actual PSL₃(2). A nontrivial
coset in Q/E is an involution because squares in Q lie in ⟨z⟩ ≤ E. The
unique involution class of PSL₃(2), lifted through the literal quotient map,
then conjugates every involution of H into Q by an element of N_G(E).

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), Lemmas 2.5(2) and 2.6(2), pp.34–35. These are conditional local
action steps: the separate normality and centralizer producer supplies the
two premises for the source-theorem assembly.
-/

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition
open Subgroup
variable {G : Type*} [Group G] [Finite G] {z : G}

private theorem conjugate_core_not_le_centralizer (h : Hypotheses z) (g : G)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z) :
    ¬ (coreInG z).map (MulAut.conj g).toMonoidHom ≤ Centralizer z := by
  classical
  intro hle
  let Qg := (coreInG z).map (MulAut.conj g).toMonoidHom
  have hzQg : z ∈ Qg := (involution_mem_coreIntersection h g hgQ hg).2
  have hzZ : (⟨z, hzQg⟩ : Qg) ∈ center Qg := by
    apply mem_center_iff.mpr
    intro q
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hle q.property))
  have hzline : z ∈ zpowers (g * z * g⁻¹) := by
    have hc := map_embeddedCenter (coreInG z) (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective
    rw [h.coreInG_center_image, MonoidHom.map_zpowers] at hc
    change z ∈ zpowers ((MulAut.conj g).toMonoidHom z)
    rw [hc]
    exact ⟨⟨z, hzQg⟩, hzZ, rfl⟩
  have hs : orderOf (g * z * g⁻¹) = 2 :=
    ((MulAut.conj g).orderOf_eq z).trans h.involution
  rw [mem_zpowers_iff_mem_range_orderOf, hs] at hzline
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hzline
  have hnlt : n < 2 := Finset.mem_range.mp hn
  interval_cases n
  · have hz1 : z = 1 := by simpa using he.symm
    have ho := h.involution
    simp [hz1] at ho
  · exact hg (by simpa using he)

private theorem intersection_action_surjective (h : Hypotheses z) (g : G)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (hNormal : ((coreIntersection z g).subgroupOf (Centralizer z)).Normal)
    (hCentral : centralizer (coreIntersection z g : Set G) = coreIntersection z g) :
    Function.Surjective (coreIntersection z g).normalizerMonoidHom := by
  let E := coreIntersection z g
  let N := normalizer (E : Set G)
  let f := E.normalizerMonoidHom
  have hEH : E ≤ Centralizer z := (coreIntersection_le z g).trans (coreInG_le z)
  have hHN : Centralizer z ≤ N := (normal_subgroupOf_iff_le_normalizer hEH).mp hNormal
  have hker : f.ker = E.subgroupOf N := by
    rw [normalizerMonoidHom_ker, hCentral]
  let fH := f.comp (inclusion hHN)
  have hkerH : fH.ker = E.subgroupOf (Centralizer z) := by
    ext x
    change inclusion hHN x ∈ f.ker ↔ _
    rw [hker]
    rfl
  have hE : Nat.card E = 8 := coreIntersection_card h g hgQ hg
  have hHcard : Nat.card fH.range = 24 := by
    have hh := fH.ker.card_mul_index
    rw [index_ker, hkerH, Nat.card_congr (subgroupOfEquivOfLe hEH).toEquiv,
      hE, h.centralizer_card] at hh
    omega
  have hHR : fH.range ≤ f.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨inclusion hHN x, rfl⟩
  have hproper : fH.range ≠ f.range := by
    intro he
    apply conjugate_core_not_le_centralizer h g hgQ hg
    intro q hq
    let qN : N := ⟨q, conjugate_core_normalizes_intersection h g hgQ hg hq⟩
    have hqR : f qN ∈ fH.range := he ▸ (show f qN ∈ f.range from ⟨qN, rfl⟩)
    obtain ⟨a, ha⟩ := hqR
    have hk : (inclusion hHN a)⁻¹ * qN ∈ E.subgroupOf N := by
      rw [← hker]
      exact (f.eq_iff).mp ha.symm
    have hm := (Centralizer z).mul_mem a.property (hEH hk)
    change (a : G) * ((a : G)⁻¹ * q) ∈ Centralizer z at hm
    simpa only [mul_inv_cancel_left] using hm
  let : IsElementaryAbelian 2 E := coreIntersection_elementary h g hg
  have hAut : Nat.card (MulAut E) = 168 := card_mulAut_of_elementary_eight E hE
  have hHindex : fH.range.index = 7 := by
    have hh := fH.range.card_mul_index
    rw [hHcard, hAut] at hh
    omega
  have hRindex : f.range.index ∣ 7 := hHindex ▸ index_dvd_of_le hHR
  rcases (show Nat.Prime 7 by decide).eq_one_or_self_of_dvd _ hRindex with h1 | h7
  · exact MonoidHom.range_eq_top.mp (index_eq_one.mp h1)
  · have hRcard : Nat.card f.range = 24 := by
      have hh := f.range.card_mul_index
      rw [h7, hAut] at hh
      omega
    exact (hproper (eq_of_le_of_card_ge hHR (by omega))).elim

/-- Under relative normality in H and ambient self-centralization, the literal
normalizer quotient is the genuine PSL₃(2), via its conjugation action on E. -/
public theorem coreIntersection_normalizer_quotient (h : Hypotheses z) (g : G)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (hNormal : ((coreIntersection z g).subgroupOf (Centralizer z)).Normal)
    (hCentral : centralizer (coreIntersection z g : Set G) = coreIntersection z g) :
    Nonempty ((normalizer (coreIntersection z g : Set G) ⧸
      (coreIntersection z g).subgroupOf (normalizer (coreIntersection z g : Set G))) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  let E := coreIntersection z g
  have hker : E.normalizerMonoidHom.ker = E.subgroupOf (normalizer (E : Set G)) := by
    rw [normalizerMonoidHom_ker, hCentral]
  let : IsElementaryAbelian 2 E := coreIntersection_elementary h g hg
  let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective E.normalizerMonoidHom
      (intersection_action_surjective h g hgQ hg hNormal hCentral))
  exact ⟨e.trans (MulAut.elementaryEight_equiv_PSL3 (coreIntersection_card h g hgQ hg)).some⟩

/-- Every involution in H is fused into Q by left conjugation inside the
literal normalizer of E; no ambient simplicity or fusion premise is needed. -/
public theorem coreIntersection_involution_fusion (h : Hypotheses z) (g : G)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (hNormal : ((coreIntersection z g).subgroupOf (Centralizer z)).Normal)
    (hCentral : centralizer (coreIntersection z g : Set G) = coreIntersection z g) :
    ∀ t : G, t ∈ Centralizer z → orderOf t = 2 →
      ∃ m : normalizer (coreIntersection z g : Set G),
        (m : G) * t * (m : G)⁻¹ ∈ coreInG z := by
  classical
  let E := coreIntersection z g
  let N := normalizer (E : Set G)
  let EN := E.subgroupOf N
  let π := QuotientGroup.mk' EN
  have hEH : E ≤ Centralizer z := (coreIntersection_le z g).trans (coreInG_le z)
  have hHN : Centralizer z ≤ N := (normal_subgroupOf_iff_le_normalizer hEH).mp hNormal
  have hQN : coreInG z ≤ N := core_normalizes_intersection h g hgQ hg
  have hker : π.ker = EN := QuotientGroup.ker_mk' EN
  have hzE : z ∈ E := involution_mem_coreIntersection h g hgQ hg
  have hlt : E < coreInG z := by
    refine lt_of_le_of_ne (coreIntersection_le z g) ?_
    intro he
    have hc := coreIntersection_card h g hgQ hg
    change Nat.card E = 8 at hc
    rw [he, h.coreInG_card] at hc
    omega
  obtain ⟨a, haQ, haE⟩ := SetLike.exists_of_lt hlt
  let aN : N := ⟨a, hQN haQ⟩
  have haπ : orderOf (π aN) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      change a ^ 2 ∈ E
      rcases core_square_eq_one_or_involution h haQ with hs | hs
      · exact hs ▸ E.one_mem
      · exact hs ▸ hzE
    · intro he
      exact haE ((QuotientGroup.eq_one_iff aN).mp he)
  obtain ⟨e⟩ := coreIntersection_normalizer_quotient h g hgQ hg hNormal hCentral
  intro t htH ht
  by_cases htE : t ∈ E
  · refine ⟨1, ?_⟩
    simpa using (coreIntersection_le z g htE)
  let tN : N := ⟨t, hHN htH⟩
  have htπ : orderOf (π tN) = 2 := by
    apply orderOf_eq_prime
    · have ht2 : tN ^ 2 = 1 := Subtype.ext (ht ▸ pow_orderOf_eq_one t)
      rw [← map_pow, ht2, map_one]
    · intro he
      exact htE ((QuotientGroup.eq_one_iff tN).mp he)
  obtain ⟨c, hc⟩ := Matrix.PSL3Two.involutions_conjugate (e (π tN)) (e (π aN))
    ((e.orderOf_eq _).trans htπ) ((e.orderOf_eq _).trans haπ)
  obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective EN (e.symm c)
  have hm' : π m = e.symm c := hm
  have hc' : π (m * tN * m⁻¹) = π aN := by
    apply e.injective
    simpa only [map_mul, map_inv, hm', MulEquiv.apply_symm_apply, MulAut.conj_apply] using hc
  have hk : aN⁻¹ * (m * tN * m⁻¹) ∈ EN := by
    rw [← hker]
    exact π.eq_iff.mp hc'
  have hq := (coreInG z).mul_mem haQ (coreIntersection_le z g hk)
  refine ⟨m, ?_⟩
  change a * (a⁻¹ * ((m : G) * t * (m : G)⁻¹)) ∈ coreInG z at hq
  simpa only [mul_inv_cancel_left] using hq

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition
