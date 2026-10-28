module

public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.Quotient.FixedRoot

/-!
# The three-action on the literal second-transfer quotient

The supplied Sylow three-group lies in both transfer kernels and normalizes
Y. A generator lifts to L and retains order three in L/⟨v⟩. Its fixed cosets
in the image of Y are trivial: the coprime fixed-coset theorem lifts them to
C_Y(Q)=⟨v⟩, using the same Q and the excluded order-four root.

This supplies the actual actor for the core-center normalizer calculation.
No new action or quotient marking is chosen independently of the transfer data.

Source: Parrott (1972), Lemma 8, printed pp.682–683, C_Y(Q)=⟨v⟩
and observation (i).
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondTransferData
variable {G : Type*} [Group G] [Finite G] {z : G}
  {d : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData d}
  (t : ParrottSecondTransferData n)

/-- The image of the supplied three-group acts without nonidentity fixed points. -/
public theorem exists_quotient_three_actor :
    ∃ q : t.Quotient, orderOf q = 3 ∧
      q ∈ normalizer (t.quotientSylow : Set t.Quotient) ∧
      ∀ x ∈ t.quotientSylow, Commute q x → x = 1 := by
  let N := normalizer (d.F : Set G)
  let A := (n.Q : Subgroup N).map N.subtype
  let π := QuotientGroup.mk' (zpowers t.v)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := n.Q) 3
    (by rw [n.three_card])
  have haG : orderOf (a.val : G) = 3 :=
    (orderOf_injective N.subtype N.subtype_injective a.val).trans
      ((orderOf_injective (n.Q : Subgroup N).subtype
        (n.Q : Subgroup N).subtype_injective a).trans ha)
  have haA : (a.val : G) ∈ A := ⟨a.val, a.property, rfl⟩
  obtain ⟨q, hq⟩ := t.three_le_embedding_range haA
  have hq3 : orderOf q = 3 :=
    (orderOf_injective t.embedding t.embedding_injective q).symm.trans
      (by simpa only [hq] using haG)
  have hA : A = zpowers (t.embedding q) := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr (hq.symm ▸ haA)) _).symm
    rw [Nat.card_zpowers, orderOf_injective t.embedding t.embedding_injective,
      hq3, show Nat.card A = 3 from
        (card_map_of_injective N.subtype_injective).trans n.three_card]
  have hqS : q ∈ normalizer ((t.S : Subgroup t.L) : Set t.L) := by
    have hh := t.three_le_sylow_image_normalizer (hq.symm ▸ haA)
    have hc := le_normalizer_comap (H := (t.S : Subgroup t.L).map t.embedding)
      t.embedding hh
    simpa only [comap_map_eq_self_of_injective t.embedding_injective] using hc
  have hqπ : orderOf (π q) = 3 := by
    have hd : orderOf (π q) ∣ 3 := hq3 ▸ orderOf_map_dvd π q
    apply (Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 3) _ hd).resolve_left
    intro hone
    have hk : q ∈ zpowers t.v := by
      rw [← QuotientGroup.ker_mk' (zpowers t.v)]
      exact orderOf_eq_one_iff.mp hone
    have hv2 : orderOf t.v = 2 :=
      (orderOf_injective t.embedding t.embedding_injective t.v).symm.trans
        (by simpa only [t.v_image] using n.v_order)
    have hbad := orderOf_dvd_of_mem_zpowers hk
    rw [hq3, hv2] at hbad
    norm_num at hbad
  refine ⟨π q, hqπ, ?_, ?_⟩
  · exact (t.S : Subgroup t.L).le_normalizer_map π (mem_map_of_mem π hqS)
  · rintro _ ⟨s, hs, rfl⟩ hcomm
    have hsline : t.embedding s ∈ zpowers n.v := by
      apply t.sylow_image_mem_line_of_three_fixed_modulo ⟨s, hs, rfl⟩
      intro b hb
      change b ∈ A at hb
      rw [hA] at hb
      obtain ⟨k, rfl⟩ := hb
      have hk : MulAut.conj (q ^ k) s / s ∈ zpowers t.v := by
        rw [← QuotientGroup.ker_mk' (zpowers t.v)]
        change π (q ^ k * s * (q ^ k)⁻¹ / s) = 1
        simp only [map_div, map_mul, map_inv, map_zpow]
        rw [(hcomm.zpow_left k).eq, mul_inv_cancel_right]
        exact div_self' (π s)
      have himage := mem_map_of_mem t.embedding hk
      change t.embedding (q ^ k * s * (q ^ k)⁻¹ / s) ∈
        (zpowers t.v).map t.embedding at himage
      change t.embedding q ^ k * t.embedding s * (t.embedding q ^ k)⁻¹ /
        t.embedding s ∈ zpowers n.v
      simpa only [MonoidHom.map_zpowers, t.v_image, map_div, map_mul,
        map_inv, map_zpow] using himage
    have hsline' : s ∈ zpowers t.v := by
      have hm : t.embedding s ∈ (zpowers t.v).map t.embedding := by
        simpa only [MonoidHom.map_zpowers, t.v_image] using hsline
      obtain ⟨u, hu, he⟩ := hm
      exact t.embedding_injective he ▸ hu
    exact (QuotientGroup.eq_one_iff _).mpr hsline'

end Stellmacher.Recognition.ParrottSecondTransferData
