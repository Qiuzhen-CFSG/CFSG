module

public import Stellmacher.Recognition.Parrott.NormalizerFusion
public import Theory.GroupTheory.SylowInvolutionCentralizerNormal

/-!
# Separated involutions in Parrott's second transfer quotient

The actual elementary subgroup F has order 32, while Z(Ω₁(O₂(N))) has
order eight. Choose u outside that center. In a subgroup containing F,
the images of z and u modulo the specified central involution v remain
nonconjugate: a lifted conjugacy would fuse z with u or vu. Both latter
elements belong to F outside Z(O₂(N)), hence belong to the v-class.

Together with involution-centralizer containment in the same quotient,
this proves normality of the second-transfer Sylow subgroup. The normalizer
fusion package supplies every fusion and cardinality input; no ambient
N₂ or solvability premise is used.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
printed p. 683, the final paragraph of Lemma 8.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottNormalizerFusionData

variable {G : Type*} [Group G] [Finite G] {z : G}
  {d : ParrottSecondElementaryData z} (n : ParrottNormalizerFusionData d)

private theorem mem_zpowers_two {A : Type*} [Group A] [Finite A]
    {v x : A} (hv : orderOf v = 2) (hx : x ∈ zpowers v) : x = 1 ∨ x = v := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hv] at hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  have hi2 : i < 2 := Finset.mem_range.mp hi
  interval_cases i <;> simp

/-- The two separated classes survive the exact quotient by the chosen v,
with representatives inside the actual supplied Sylow subgroup. -/
public theorem second_transfer_quotient_separated_involutions
    (h : ParrottCentralizerHypotheses z)
    {A B : Type*} [Group A] [Finite A] [Group B]
    (f : A →* G) (hf : Function.Injective f) (S : Sylow 2 A)
    (hFS : d.F ≤ (S : Subgroup A).map f)
    (v : A) (hv : f v = n.v) (q : A →* B) (hq : Function.Surjective q)
    (hker : q.ker = zpowers v) :
    ∃ a b : B, a ∈ (S : Subgroup A).map q ∧ b ∈ (S : Subgroup A).map q ∧
      orderOf a = 2 ∧ orderOf b = 2 ∧ ¬ IsConj a b := by
  let N := normalizer (d.F : Set G)
  let K := pCore 2 N
  let ZK := (center K).map (N.subtype.comp K.subtype)
  let W := omega₁ K (p := 2)
  let ZW := (center W).map ((N.subtype.comp K.subtype).comp W.subtype)
  have hvZW : n.v ∈ ZW := by
    change n.v ∈ (center (omega₁ (pCore 2 (normalizer (d.F : Set G))) (p := 2))).map _
    rw [n.omega_center_eq]
    exact mem_sup_right (mem_zpowers n.v)
  have hu : ∃ u : G, u ∈ d.F ∧ u ∉ ZW := by
    by_contra! hn
    have hc := card_le_of_le (show d.F ≤ ZW from hn)
    rw [d.card, n.ambient_omega_center_card] at hc
    omega
  obtain ⟨u, huF, huZ⟩ := hu
  obtain ⟨a, haS, ha⟩ := hFS d.z_mem_inf.2
  obtain ⟨b, hbS, hb⟩ := hFS huF
  have hv2 : orderOf v = 2 := by rw [← orderOf_injective f hf, hv]; exact n.v_order
  have hz1 : z ≠ 1 := by intro he; simpa [he] using h.involution
  have hzv : z ≠ n.v := fun he => n.not_isConj (he ▸ IsConj.refl z)
  have ha1 : q a ≠ 1 := by
    intro he
    have hm : a ∈ zpowers v := hker ▸ (MonoidHom.mem_ker.mpr he : a ∈ q.ker)
    rcases mem_zpowers_two hv2 hm with he | he
    · exact hz1 (ha.symm.trans (he ▸ f.map_one))
    · exact hzv (ha.symm.trans (congrArg f he |>.trans hv))
  have hb1 : q b ≠ 1 := by
    intro he
    have hm : b ∈ zpowers v := hker ▸ (MonoidHom.mem_ker.mpr he : b ∈ q.ker)
    rcases mem_zpowers_two hv2 hm with he | he
    · exact huZ (show u ∈ ZW from hb ▸ (he ▸ f.map_one) ▸ ZW.one_mem)
    · have huv : u = n.v := hb.symm.trans ((congrArg f he).trans hv)
      exact huZ (huv ▸ hvZW)
  let : IsElementaryAbelian 2 d.F := d.elementary
  have hasq : a ^ 2 = 1 := hf (by
    rw [map_pow, ha, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian z d.z_mem_inf.2)
  have hbsq : b ^ 2 = 1 := hf (by
    rw [map_pow, hb, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian u huF)
  refine ⟨q a, q b, mem_map_of_mem q haS, mem_map_of_mem q hbS,
    orderOf_eq_prime (by rw [← map_pow, hasq, map_one]) ha1,
    orderOf_eq_prime (by rw [← map_pow, hbsq, map_one]) hb1, ?_⟩
  intro hconj
  obtain ⟨gB, hgB⟩ := isConj_iff.mp hconj
  obtain ⟨g, rfl⟩ := hq gB
  have hmem : g * a * g⁻¹ / b ∈ zpowers v := by
    rw [← hker, MonoidHom.mem_ker]
    rw [map_div, map_mul, map_mul, map_inv, hgB, div_self']
  have hcases := mem_zpowers_two hv2 hmem
  have hclass (w : G) (hwF : w ∈ d.F) (hwZ : w ∉ ZK) : IsConj n.v w := by
    obtain ⟨c, hc⟩ := n.elementary_fusion w hwF hwZ
    exact isConj_iff.mpr ⟨c, hc⟩
  rcases hcases with he | he
  · have heq : f g * z * (f g)⁻¹ = u := by
      simpa only [map_mul, map_inv, ha, hb] using congrArg f (div_eq_one.mp he)
    exact n.not_isConj ((isConj_iff.mpr ⟨f g, heq⟩).trans
      (hclass u huF (fun hmem => huZ (n.core_center_le_omega_center hmem))).symm)
  · have heq : f g * z * (f g)⁻¹ = n.v * u := by
      simpa only [map_mul, map_inv, ha, hb, hv] using congrArg f
        (div_eq_iff_eq_mul.mp he)
    have hvuF : n.v * u ∈ d.F := d.F.mul_mem n.v_mem_inf.2 huF
    have hvuZ : n.v * u ∉ ZK := by
      intro hh
      exact huZ ((ZW.mul_mem_cancel_left hvZW).mp (n.core_center_le_omega_center hh))
    exact n.not_isConj ((isConj_iff.mpr ⟨f g, heq⟩).trans (hclass _ hvuF hvuZ).symm)

/-- Apply the unrestricted TI argument to the actual second-transfer
embedding and quotient; the fusion premises are all discharged. -/
public theorem second_transfer_sylow_normal_of_quotient_centralizers
    (h : ParrottCentralizerHypotheses z)
    {A B : Type*} [Group A] [Finite A] [Group B]
    (f : A →* G) (hf : Function.Injective f) (S : Sylow 2 A)
    (hFS : d.F ≤ (S : Subgroup A).map f)
    (v : A) (hv : f v = n.v) (q : A →* B) (hq : Function.Surjective q)
    (hker : q.ker = zpowers v)
    (hcent : ∀ x ∈ (S : Subgroup A).map q, orderOf x = 2 →
      centralizer ({x} : Set B) ≤ (S : Subgroup A).map q) :
    (S : Subgroup A).Normal := by
  obtain ⟨a, b, haS, hbS, ha, hb, hab⟩ :=
    n.second_transfer_quotient_separated_involutions h f hf S hFS v hv q hq hker
  have hvS : v ∈ (S : Subgroup A) := by
    obtain ⟨w, hw, he⟩ := hFS n.v_mem_inf.2
    exact hf (he.trans hv.symm) ▸ hw
  exact S.normal_of_quotient_involution_centralizers_le_of_not_isConj q hq
    (by rw [hker]; exact zpowers_le.mpr hvS) hcent a b haS hbS ha hb hab

end Stellmacher.Recognition.ParrottNormalizerFusionData
