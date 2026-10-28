module

public import CFSG.Quasithin.Chapter14.Section01.SourcePreliminaries.ResidualSplitting.QuotientData
public import Stellmacher.SectionThree.SolvablePrimitiveTwoLocal.Residual
public import CFSG.Quasithin.Chapter14.Section01.SourcePreliminaries.ResidualSplitting.ResidualIdentification.Inverter

/-!
# Residual identification in the S₃ star quotient

An isomorphism from the star normal closure to S₃ identifies its two-residual
with A₃. Functoriality gives the image of the original residual, while
injectivity on the star normal closure identifies its action kernel with its
intersection with the normal two-subgroup. This proves the two-core equality
and the residual–reflection supplement without constructing an S₃ complement.
The intersection hypothesis makes the original two-subgroup Sylow in its
normal closure. The inverter theorem then supplies an actual order-three
element there, which lies in the two-residual because every two-group quotient
kills it.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), printed pp.980–981, Lemma 14.1.18.
-/

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter14.SourcePreliminaries

private theorem alternating_three_card : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [nat_card_alternatingGroup]
  norm_num

private theorem perm_three_residual :
    twoResidualAmbient (⊤ : Subgroup (Equiv.Perm (Fin 3))) = alternatingGroup (Fin 3) := by
  apply Stellmacher.SectionThree.twoResidualAmbient_top_eq_of_normal_pGroup_quotient_two
    Nat.prime_three (by decide) _ inferInstance
  · exact IsPGroup.of_card (n := 1) (by simpa using alternating_three_card)
  · apply IsPGroup.of_card (n := 1)
    rw [← Subgroup.index_eq_card, alternatingGroup.index_eq_two]
    norm_num

/-- The quotient normal-closure isomorphism determines the residual image. -/
public theorem residual_image_of_quotient_bijective
    {H : Type*} [Group H] [Finite H]
    (f : H →* Equiv.Perm (Fin 3)) (N Q : Subgroup H) [Q.Normal]
    (hQker : Q ≤ f.ker)
    (hb : Function.Bijective ((QuotientGroup.lift Q f hQker).domRestrict
      (N.map (QuotientGroup.mk' Q)))) :
    (twoResidualAmbient N).map f = alternatingGroup (Fin 3) := by
  have hN : N.map f = ⊤ := by
    apply top_unique
    intro t _
    obtain ⟨x, hx⟩ := hb.2 t
    obtain ⟨n, hn, hnq⟩ := x.property
    refine ⟨n, hn, ?_⟩
    change QuotientGroup.lift Q f hQker (x : H ⧸ Q) = t at hx
    rw [← hnq] at hx
    exact hx
  rw [map_twoResidualAmbient_of_subgroup_image N f ⊤ hN, perm_three_residual]

/-- The star residual maps isomorphically onto the alternating subgroup. -/
public theorem residual_quotient_equiv_alternating
    {H : Type*} [Group H] [Finite H]
    (f : H →* Equiv.Perm (Fin 3)) (N Q : Subgroup H) [Q.Normal]
    (hQker : Q ≤ f.ker)
    (hb : Function.Bijective ((QuotientGroup.lift Q f hQker).domRestrict
      (N.map (QuotientGroup.mk' Q)))) :
    Nonempty (((twoResidualAmbient N).map (QuotientGroup.mk' Q)) ≃*
      alternatingGroup (Fin 3)) := by
  let Y := twoResidualAmbient N
  let q := QuotientGroup.mk' Q
  let fs := QuotientGroup.lift Q f hQker
  have hYN : Y.map q ≤ N.map q := map_mono (map_subtype_le _)
  have hi : Function.Injective (fs.domRestrict (Y.map q)) := by
    intro x y hxy
    have he : (⟨x, hYN x.property⟩ : N.map q) = ⟨y, hYN y.property⟩ := hb.1 hxy
    exact Subtype.ext (congrArg (fun t : N.map q => (t : H ⧸ Q)) he)
  have hr : (fs.domRestrict (Y.map q)).range = alternatingGroup (Fin 3) := by
    rw [MonoidHom.domRestrict_range, map_map, QuotientGroup.lift_comp_mk']
    exact residual_image_of_quotient_bijective f N Q hQker hb
  exact ⟨(MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hr)⟩

/-- The star residual has order three. -/
public theorem residual_quotient_card
    {H : Type*} [Group H] [Finite H]
    (f : H →* Equiv.Perm (Fin 3)) (N Q : Subgroup H) [Q.Normal]
    (hQker : Q ≤ f.ker)
    (hb : Function.Bijective ((QuotientGroup.lift Q f hQker).domRestrict
      (N.map (QuotientGroup.mk' Q)))) :
    Nat.card ((twoResidualAmbient N).map (QuotientGroup.mk' Q)) = 3 := by
  obtain ⟨e⟩ := residual_quotient_equiv_alternating f N Q hQker hb
  exact (Nat.card_congr e.toEquiv).trans alternating_three_card

/-- Inside the residual, the action kernel is precisely the intersection with `Q`. -/
public theorem residual_inf_kernel_eq
    {H : Type*} [Group H] [Finite H]
    (f : H →* Equiv.Perm (Fin 3)) (N Q : Subgroup H) [Q.Normal]
    (hQker : Q ≤ f.ker)
    (hb : Function.Bijective ((QuotientGroup.lift Q f hQker).domRestrict
      (N.map (QuotientGroup.mk' Q)))) :
    twoResidualAmbient N ⊓ f.ker = twoResidualAmbient N ⊓ Q := by
  apply le_antisymm ?_ (inf_le_inf_left _ hQker)
  intro x hx
  refine ⟨hx.1, ?_⟩
  apply (QuotientGroup.eq_one_iff x).mp
  have hxn : x ∈ N := map_subtype_le _ hx.1
  have he := hb.1 (a₁ := ⟨QuotientGroup.mk' Q x, mem_map_of_mem _ hxn⟩)
    (a₂ := 1) (by simpa using (show f x = 1 from hx.2))
  exact congrArg Subtype.val he

/-- The kernel on the residual is exactly its ambient two-core. -/
public theorem residual_two_core_eq
    {H : Type*} [Group H] [Finite H]
    (f : H →* Equiv.Perm (Fin 3)) (N Q : Subgroup H) [Q.Normal]
    (hQker : Q ≤ f.ker) (hQ : IsPGroup 2 Q)
    (hb : Function.Bijective ((QuotientGroup.lift Q f hQker).domRestrict
      (N.map (QuotientGroup.mk' Q)))) :
    (twoResidualAmbient N).pCoreIn 2 = twoResidualAmbient N ⊓ f.ker := by
  let Y := twoResidualAmbient N
  have him := residual_image_of_quotient_bijective f N Q hQker hb
  have hmeet := residual_inf_kernel_eq f N Q hQker hb
  apply le_antisymm
  · apply le_inf (pCoreIn_le 2 _)
    apply (Subgroup.map_eq_bot_iff _).mp
    have hp := (isPGroup_pCoreIn 2 Y).map f
    have h3 : IsPGroup 3 (Y.map f) := by
      rw [him]
      exact IsPGroup.of_card (n := 1) (by simpa using alternating_three_card)
    have hle : (Y.pCoreIn 2).map f ≤ Y.map f := map_mono (pCoreIn_le 2 Y)
    have hp3 : IsPGroup 3 ((Y.pCoreIn 2).map f) :=
      h3.of_injective (inclusion hle) (inclusion_injective hle)
    exact disjoint_self.mp (IsPGroup.disjoint_of_ne 2 3 (by decide) _ _ hp hp3)
  · rw [hmeet]
    apply le_pCoreIn_of_normalizes
    · exact hQ.of_injective (inclusion inf_le_right) (inclusion_injective inf_le_right)
    · exact inf_le_left
    · exact le_normalizer_inf Y.le_normalizer le_normalizer_of_normal

private theorem reflection_image_card
    {H : Type*} [Group H] (f : H →* Equiv.Perm (Fin 3))
    (D : Subgroup H) (hD : IsPGroup 2 D) (hne : ¬ D ≤ f.ker) :
    Nat.card (D.map f) = 2 := by
  have hcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hd : Nat.card (D.map f) ∣ 6 := hcard ▸ (D.map f).card_subgroup_dvd_card
  have hcop : Nat.Coprime (Nat.card (D.map f)) 3 := by
    obtain ⟨n, hn⟩ := (hD.map f).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hd2 : Nat.card (D.map f) ∣ 2 := hcop.dvd_mul_right.mp hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with hc | hc
  · exact (hne ((Subgroup.map_eq_bot_iff D).mp (card_eq_one.mp hc))).elim
  · exact hc

private theorem alternating_sup_two_image
    {H : Type*} [Group H] (f : H →* Equiv.Perm (Fin 3))
    (D : Subgroup H) (hD : IsPGroup 2 D) (hne : ¬ D ≤ f.ker) :
    alternatingGroup (Fin 3) ⊔ D.map f = ⊤ := by
  let J := alternatingGroup (Fin 3) ⊔ D.map f
  have htwo : 2 ∣ Nat.card J :=
    reflection_image_card f D hD hne ▸ card_dvd_of_le (show D.map f ≤ J from le_sup_right)
  have hthree : 3 ∣ Nat.card J := by
    have hd := card_dvd_of_le (show alternatingGroup (Fin 3) ≤ J from le_sup_left)
    rwa [alternating_three_card] at hd
  have h6 : 6 ∣ Nat.card J := (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd htwo hthree
  have hcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  apply eq_top_of_card_eq
  exact Nat.dvd_antisymm J.card_subgroup_dvd_card (hcard ▸ h6)

/-- The reflection image supplements the residual in the star normal closure. -/
public theorem residual_quotient_sup_reflection
    {H : Type*} [Group H] [Finite H]
    (f : H →* Equiv.Perm (Fin 3)) (N D Q : Subgroup H) [Q.Normal]
    (hQker : Q ≤ f.ker) (hDN : D ≤ N)
    (hD : IsPGroup 2 D) (hne : ¬ D ≤ f.ker)
    (hb : Function.Bijective ((QuotientGroup.lift Q f hQker).domRestrict
      (N.map (QuotientGroup.mk' Q)))) :
    (twoResidualAmbient N).map (QuotientGroup.mk' Q) ⊔ D.map (QuotientGroup.mk' Q) =
      N.map (QuotientGroup.mk' Q) := by
  let q := QuotientGroup.mk' Q
  let fs := QuotientGroup.lift Q f hQker
  let J := (twoResidualAmbient N).map q ⊔ D.map q
  have hJN : J ≤ N.map q := sup_le (map_mono (map_subtype_le _)) (map_mono hDN)
  have hj : J.map fs = ⊤ := by
    rw [Subgroup.map_sup, map_map, map_map, QuotientGroup.lift_comp_mk',
      residual_image_of_quotient_bijective f N Q hQker hb]
    exact alternating_sup_two_image f D hD hne
  apply le_antisymm hJN
  intro x hx
  obtain ⟨j, hj, he⟩ := (show fs x ∈ J.map fs by rw [hj]; trivial)
  have heq : (⟨j, hJN hj⟩ : N.map q) = ⟨x, hx⟩ := hb.1 he
  have hjx : j = x := congrArg (fun t : N.map q => (t : H ⧸ Q)) heq
  exact hjx ▸ hj

/-- The star residual is an actual cyclic group of order three. -/
public noncomputable def residualQuotientCyclicEquiv
    {H : Type*} [Group H] [Finite H]
    (f : H →* Equiv.Perm (Fin 3)) (N Q : Subgroup H) [Q.Normal]
    (hQker : Q ≤ f.ker)
    (hb : Function.Bijective ((QuotientGroup.lift Q f hQker).domRestrict
      (N.map (QuotientGroup.mk' Q)))) :
    ((twoResidualAmbient N).map (QuotientGroup.mk' Q)) ≃* Multiplicative (ZMod 3) := by
  exact mulEquivOfPrimeCardEq (residual_quotient_card f N Q hQker hb) (by simp)

private theorem three_element_mem_residual
    {H : Type*} [Group H] [Finite H] (N : Subgroup H)
    (y : N) (hy : orderOf y = 3) : (y : H) ∈ twoResidualAmbient N := by
  refine mem_map.mpr ⟨y, ?_, rfl⟩
  rw [twoResidualSubgroup, mem_sInf]
  intro K hK
  let _ : K.Normal := hK.1
  obtain ⟨n, hn⟩ := hK.2
  have hp : IsPGroup 2 (N ⧸ K) := IsPGroup.of_card (by
    simpa only [← index_eq_card] using hn)
  let q := QuotientGroup.mk' K
  have hd : orderOf (q y) ∣ 3 := hy ▸ orderOf_map_dvd q y
  have hc := hp.orderOf_coprime (by decide : Nat.Coprime 2 3) (q y)
  have he : q y = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hc (dvd_refl _) hd)
  exact (QuotientGroup.eq_one_iff y).mp he

/-- The intersection hypothesis makes `D` Sylow in its normal closure,
so the faithful three-lift can be inverted by an actual element of `D`. -/
public theorem residual_normalClosure_inverted_three_lift
    {H : Type*} [Group H] [Finite H]
    (f : H →* Equiv.Perm (Fin 3)) (D Q : Subgroup H) [Q.Normal]
    (hQker : Q ≤ f.ker) (hQ : IsPGroup 2 Q)
    (hD : IsPGroup 2 D) (hne : ¬ D ≤ f.ker)
    (hmeet : D ⊓ f.ker = Q)
    (hb : Function.Bijective ((QuotientGroup.lift Q f hQker).domRestrict
      ((normalClosure (D : Set H)).map (QuotientGroup.mk' Q)))) :
    ∃ r ∈ D, ∃ y ∈ twoResidualAmbient (normalClosure (D : Set H)),
      orderOf y = 3 ∧ orderOf (f y) = 3 ∧ r * y * r⁻¹ = y⁻¹ := by
  let N := normalClosure (D : Set H)
  let g := f.domRestrict N
  have hDN : D ≤ N := le_normalClosure
  have hQD : Q ≤ D := by rw [← hmeet]; exact inf_le_left
  have hg : Function.Surjective g := by
    intro t
    obtain ⟨x, hx⟩ := hb.2 t
    obtain ⟨n, hn, he⟩ := x.property
    refine ⟨⟨n, hn⟩, ?_⟩
    change QuotientGroup.lift Q f hQker (x : H ⧸ Q) = t at hx
    rw [← he] at hx
    exact hx
  have hk : g.ker = Q.subgroupOf N := by
    ext x
    change f (x : H) = 1 ↔ (x : H) ∈ Q
    constructor
    · intro hx
      apply (QuotientGroup.eq_one_iff (x : H)).mp
      have he := hb.1 (a₁ := ⟨QuotientGroup.mk' Q (x : H), mem_map_of_mem _ x.property⟩)
        (a₂ := 1) (by simpa using hx)
      exact congrArg (fun z : N.map (QuotientGroup.mk' Q) => (z : H ⧸ Q)) he
    · exact fun hx => hQker hx
  have hkg : IsPGroup 2 g.ker := by rw [hk]; exact hQ.comap_subtype
  let E := D.subgroupOf N
  have hE : IsPGroup 2 E := hD.comap_subtype
  have hKE : g.ker ≤ E := by rw [hk]; exact comap_mono hQD
  have hmap : E.map g = D.map f := by
    change (D.subgroupOf N).map (f.comp N.subtype) = D.map f
    rw [← map_map, map_subgroupOf_eq_of_le hDN]
  have hcE : (D.map f).comap g = E := by
    rw [← hmap, comap_map_eq, sup_eq_left.mpr hKE]
  have hcard := reflection_image_card f D hD hne
  have hidx : E.index = 3 := by
    rw [← hcE, index_comap_of_surjective _ hg]
    have hh := (D.map f).index_mul_card
    rw [hcard] at hh
    have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    rw [h6] at hh
    omega
  let S : Sylow 2 N := hE.toSylow (by rw [hidx]; decide)
  obtain ⟨r, hr, y, hy, hfy, hinv⟩ := sylow_two_inverted_three_lift g hg hkg S
  refine ⟨(r : H), hr, (y : H), three_element_mem_residual N y hy, ?_, hfy, ?_⟩
  · exact (orderOf_injective N.subtype N.subtype_injective y).trans hy
  · exact congrArg N.subtype hinv

end CFSG.Quasithin.Chapter14.SourcePreliminaries
