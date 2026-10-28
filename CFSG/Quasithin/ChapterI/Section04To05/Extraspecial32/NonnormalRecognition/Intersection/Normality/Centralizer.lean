module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Intersection.Cardinality
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupTheory.SylowCentralizerConjugacy

/-!
# Ambient self-centralization of the fusion intersection

Write s = g * z * g⁻¹ and E = Q ∩ Qᵍ. Sylow conjugacy and C_Q(X) = ⟨z⟩
exclude three from |C_H(s)|. Since s is noncentral in Q, the quotient of H
by Q then bounds |C_H(s)| by 32. The two subgroups C_Q(s) and C_{Qᵍ}(z),
each of order at least sixteen and with intersection E of order eight,
therefore generate C_H(s).

An element centralizing E is a product of elements of these two subgroups.
Its two induced commutators on E agree, but lie respectively in ⟨z⟩ and
⟨s⟩. The lines are distinct, so both commutators vanish. Self-centralization
of an elementary eight inside either extraspecial core finishes the proof.
No quaternion normality or choice of a normalizer-of-X actor is needed.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemma 2.5(1), using Hypothesis 2.1 and Lemma 2.4.
-/

open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition
variable {G : Type*} [Group G] [Finite G] {z : G}
private theorem line_mem {x w : G} (hw : orderOf w = 2) (hx : x ∈ zpowers w) :
    x = 1 ∨ x = w := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hw] at hx
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  have hnlt : n < 2 := Finset.mem_range.mp hn
  interval_cases n <;> simp

/-- No cubic subgroup centralizes a noncentral element of the core. -/
public theorem core_commonCentralizer_not_three_dvd (h : Hypotheses z) (s : G) (hsQ : s ∈ coreInG z)
    (hs1 : s ≠ 1) (hsz : s ≠ z) :
    ¬ 3 ∣ Nat.card (Centralizer z ⊓ Centralizer s : Subgroup G) := by
  let H := Centralizer z
  let N := H ⊓ Centralizer s
  let sH : H := ⟨s, coreInG_le z hsQ⟩
  have hsCore : sH ∈ Core z := by
    rw [← coreInG_subgroupOf]
    exact hsQ
  intro hd
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := N) 3 hd
  let vH : H := ⟨v, v.property.1⟩
  have hvH : orderOf vH = 3 := by
    rw [← orderOf_injective H.subtype H.subtype_injective, ← hv]
    exact orderOf_injective N.subtype N.subtype_injective v
  let Y : Sylow 3 H := Sylow.ofCard (zpowers vH) (by
    rw [Nat.card_zpowers, hvH, h.centralizer_card]
    decide +kernel)
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq H h.X Y
  have hxY {x : H} (hx : x ∈ (h.X : Subgroup H)) : a * x * a⁻¹ ∈ zpowers vH := by
    have hm : a * x * a⁻¹ ∈ ((a • h.X : Sylow 3 H) : Subgroup H) :=
      mem_map_of_mem (MulAut.conj a).toMonoidHom hx
    rw [ha] at hm
    exact hm
  have hvC : vH ∈ centralizer ({sH} : Set H) :=
    mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp v.property.2))
  have hYC : zpowers vH ≤ centralizer ({sH} : Set H) := zpowers_le.mpr hvC
  let t := (MulAut.conj a).symm sH
  have htQ : t ∈ Core z := by
    simpa only [t, MulAut.conj_symm_apply, inv_inv] using
      (inferInstance : (Core z).Normal).conj_mem sH hsCore a⁻¹
  have htC : t ∈ centralizer (h.X : Set H) := by
    intro x hx
    apply (MulAut.conj a).injective
    simpa only [map_mul, t, MulEquiv.apply_symm_apply, MulAut.conj_apply] using
      mem_centralizer_singleton_iff.mp (hYC (hxY hx))
  have htline : t ∈ zpowers (distinguished z) := h.fixed ▸ ⟨htQ, htC⟩
  rcases line_mem h.distinguished_order htline with ht | ht
  · have he : sH = 1 := (MulAut.conj a).symm.injective (ht.trans (map_one _).symm)
    exact hs1 (congrArg Subtype.val he)
  · have haz : (MulAut.conj a) (distinguished z) = distinguished z := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp a.property)
    have he := congrArg (MulAut.conj a) ht
    rw [MulEquiv.apply_symm_apply, haz] at he
    exact hsz (congrArg Subtype.val he)

/-- The common centralizer of z and a noncentral core element has order at most 32. -/
public theorem core_commonCentralizer_card_le_thirty_two (h : Hypotheses z) (s : G) (hsQ : s ∈ coreInG z)
    (hs1 : s ≠ 1) (hsz : s ≠ z) :
    Nat.card (Centralizer z ⊓ Centralizer s : Subgroup G) ≤ 32 := by
  let Q := coreInG z
  let N := Centralizer z ⊓ Centralizer s
  have hn : N ≤ normalizer (Q : Set G) := h.normalizer_core.symm ▸ inf_le_left
  have hDne : Q ⊓ N ≠ Q := by
    intro he
    have hscenter : (⟨s, hsQ⟩ : Q) ∈ center Q := by
      apply mem_center_iff.mpr
      intro q
      have hq : (q : G) ∈ N := (he.ge q.property).2
      exact Subtype.ext (mem_centralizer_singleton_iff.mp hq.2)
    have hm : s ∈ zpowers z := h.coreInG_center_image ▸
      mem_map_of_mem Q.subtype hscenter
    exact (line_mem h.involution hm).elim hs1 hsz
  have hDsmall : Nat.card (Q ⊓ N : Subgroup G) ≤ 16 := by
    have hd : Nat.card (Q ⊓ N : Subgroup G) ∣ 32 :=
      h.coreInG_card ▸ card_dvd_of_le inf_le_left
    have hne : Nat.card (Q ⊓ N : Subgroup G) ≠ 32 := by
      intro he
      exact hDne (eq_of_le_of_card_ge inf_le_left (by rw [he, h.coreInG_card]))
    have hb := Nat.le_of_dvd (by decide : 0 < 32) hd
    interval_cases hd' : Nat.card (Q ⊓ N : Subgroup G) <;> norm_num at *
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes Q N hn
  have hdiv : Nat.card (Q ⊔ N : Subgroup G) ∣ 192 :=
    h.centralizer_card ▸ card_dvd_of_le (sup_le (coreInG_le z) inf_le_left)
  have h3 := core_commonCentralizer_not_three_dvd h s hsQ hs1 hsz
  have hQcard : Nat.card Q = 32 := h.coreInG_card
  have hsupdiv : 32 ∣ Nat.card (Q ⊔ N : Subgroup G) :=
    hQcard ▸ card_dvd_of_le le_sup_left
  obtain ⟨k, hk⟩ := hsupdiv
  have hk6 : k ∣ 6 := by
    rw [hk] at hdiv
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 32)).mp hdiv
  have hkpos : 0 < k := by
    have hp := Nat.card_pos (α := (Q ⊔ N : Subgroup G))
    omega
  have hkle : k ≤ 6 := Nat.le_of_dvd (by decide) hk6
  rw [hQcard, hk] at hc
  have hNk : Nat.card N = Nat.card (Q ⊓ N : Subgroup G) * k := by nlinarith
  have h3k : ¬ 3 ∣ k := fun hd => h3 (hNk ▸ dvd_mul_of_dvd_right hd _)
  have hk2 : k ≤ 2 := by interval_cases k <;> norm_num at *
  nlinarith

private theorem centralizer_lower (Q : Subgroup G) [IsExtraspecial 2 Q]
    (hQ : Nat.card Q = 32) (x : Q) :
    16 ≤ Nat.card (Q ⊓ Centralizer (x : G) : Subgroup G) := by
  rw [← map_subtype_centralizer_singleton Q x, card_map_of_injective Q.subtype_injective]
  exact IsExtraspecial.centralizer_card_ge_sixteen_of_card_thirty_two hQ x

private theorem centralizer_eight (Q E : Subgroup G) [IsExtraspecial 2 Q]
    [IsElementaryAbelian 2 E] (hQ : Nat.card Q = 32)
    (hE : Nat.card E = 8) (hle : E ≤ Q) :
    Q ⊓ centralizer (E : Set G) ≤ E := by
  let F := E.subgroupOf Q
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.subgroupOf hle
  have hc : Nat.card F = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans hE
  have hz : center Q ≤ F :=
    (IsExtraspecial.elementary_eight_normal_and_center_le_of_card_thirty_two hQ F hc).2
  have hf : centralizer (F : Set Q) = F :=
    extraspecial_two_centralizer_eq_of_card_sq F hz (by rw [hc, hQ]; decide)
  rintro x ⟨hxQ, hxC⟩
  have hx : (⟨x, hxQ⟩ : Q) ∈ centralizer (F : Set Q) :=
    fun y hy => Subtype.ext (hxC y hy)
  rw [hf] at hx
  exact hx

/-- Source 2.5(1) for the literal intersection, without a quaternion-normality premise. -/
public theorem coreIntersection_self_centralizing (h : Hypotheses z) (g : G)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z) :
    centralizer (coreIntersection z g : Set G) = coreIntersection z g := by
  let Q := coreInG z
  let Qg := Q.map (MulAut.conj g).toMonoidHom
  let E := coreIntersection z g
  let s := g * z * g⁻¹
  let N := Centralizer z ⊓ Centralizer s
  let D := Q ⊓ Centralizer s
  let F := Qg ⊓ Centralizer z
  let : IsExtraspecial 2 Q := h.coreInG_extraspecial
  let : IsExtraspecial 2 Qg := IsExtraspecial.of_mulEquiv
    ((MulAut.conj g).subgroupMap Q) h.coreInG_extraspecial
  let : IsElementaryAbelian 2 E := coreIntersection_elementary h g hg
  have hEcard : Nat.card E = 8 := coreIntersection_card h g hgQ hg
  have hzE : z ∈ E := involution_mem_coreIntersection h g hgQ hg
  have hsE : s ∈ E := conjugate_mem_coreIntersection h g hgQ
  have hsord : orderOf s = 2 := (MulAut.conj g).orderOf_eq z |>.trans h.involution
  have hs1 : s ≠ 1 := by intro he; rw [he, orderOf_one] at hsord; omega
  have hNcard : Nat.card N ≤ 32 := core_commonCentralizer_card_le_thirty_two h s hgQ hs1 hg
  have hQgcard : Nat.card Qg = 32 := by
    rw [card_map_of_injective (MulAut.conj g).injective, h.coreInG_card]
  have hQgH : Qg ≤ Centralizer s := conjugate_core_le_centralizer g
  have hDcard : 16 ≤ Nat.card D := centralizer_lower Q h.coreInG_card ⟨s, hgQ⟩
  have hFcard : 16 ≤ Nat.card F := centralizer_lower Qg hQgcard ⟨z, hzE.2⟩
  have hDN : D ≤ N := le_inf (inf_le_left.trans (coreInG_le z)) inf_le_right
  have hFN : F ≤ N := le_inf inf_le_right (inf_le_left.trans hQgH)
  have hFn : F ≤ normalizer (D : Set G) := by
    apply le_trans (le_inf ?_ ?_) inf_normalizer_le_normalizer_inf
    · exact h.normalizer_core.symm ▸ inf_le_right
    · exact (inf_le_left.trans hQgH).trans (Centralizer s).le_normalizer
  have hDF : D ⊓ F = E := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    · intro x hx
      exact ⟨⟨hx.1, hQgH hx.2⟩, hx.2, coreInG_le z hx.1⟩
  have hprod : D ⊔ F = N := by
    apply eq_of_le_of_card_ge (sup_le hDN hFN)
    have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes D F hFn
    rw [hDF, hEcard] at hc
    have hlarge : 256 ≤ Nat.card D * Nat.card F := by nlinarith
    nlinarith
  have hcomm : ⁅Q, Q⁆ ≤ zpowers z := by
    rw [← h.coreInG_center_image, ← map_subtype_commutator,
      IsExtraspecial.commutator_eq_center (p := 2)]
  have hcommg : ⁅Qg, Qg⁆ ≤ zpowers s := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hcomm
    rwa [map_commutator, MonoidHom.map_zpowers] at hh
  apply le_antisymm ?_ E.le_centralizer
  intro x hx
  have hxN : x ∈ N := ⟨mem_centralizer_singleton_iff.mpr (hx z hzE).symm,
    mem_centralizer_singleton_iff.mpr (hx s hsE).symm⟩
  have hxprod : x ∈ (D : Set G) * (F : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left D F hFn, hprod]
    exact hxN
  obtain ⟨q, hq, r, hr, hqr⟩ := hxprod
  have hfix (e : G) (he : e ∈ E) : ⁅q⁻¹, e⁆ = 1 ∧ ⁅r, e⁆ = 1 := by
    have hqe : ⁅q⁻¹, e⁆ ∈ zpowers z :=
      hcomm (commutator_mem_commutator (Q.inv_mem hq.1) he.1)
    have hre : ⁅r, e⁆ ∈ zpowers s :=
      hcommg (commutator_mem_commutator hr.1 he.2)
    have heq : ⁅q⁻¹, e⁆ = ⁅r, e⁆ := by
      have hc : e * (q * r) = (q * r) * e := by simpa only [hqr] using hx e he
      have hh : q⁻¹ * e * q = r * e * r⁻¹ := by
        have hh := congrArg (fun y => q⁻¹ * y * r⁻¹) hc
        simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using hh
      simpa only [commutatorElement_def, inv_inv] using congrArg (fun y => y * e⁻¹) hh
    have heone : ⁅q⁻¹, e⁆ = 1 := by
      rcases line_mem h.involution hqe with ht | ht
      · exact ht
      rcases line_mem hsord hre with ht' | ht'
      · exact heq.trans ht'
      · exact (hg (ht'.symm.trans (heq.symm.trans ht))).elim
    exact ⟨heone, heq.symm.trans heone⟩
  have hqC : q ∈ centralizer (E : Set G) := by
    apply inv_mem_iff.mp
    intro e he
    exact (commutatorElement_eq_one_iff_mul_comm.mp (hfix e he).1).symm
  have hrC : r ∈ centralizer (E : Set G) := by
    intro e he
    exact (commutatorElement_eq_one_iff_mul_comm.mp (hfix e he).2).symm
  have hqE : q ∈ E := (core_centralizer_intersection h g hgQ hg).le ⟨hq.1, hqC⟩
  have hrE : r ∈ E := centralizer_eight Qg E hQgcard hEcard inf_le_right ⟨hr.1, hrC⟩
  exact hqr ▸ E.mul_mem hqE hrE
end CFSG.Quasithin.Extraspecial32.NonnormalRecognition
