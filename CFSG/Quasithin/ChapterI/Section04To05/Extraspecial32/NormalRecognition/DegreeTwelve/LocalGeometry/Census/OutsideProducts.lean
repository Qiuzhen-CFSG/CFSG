module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census.LocalData
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census.OutsideProducts.SelectedAction

public import Theory.GroupTheory.QuaternionCentralProductC2Rank
public import Theory.GroupTheory.QuaternionCentralProductInvolutionProducts
public import Theory.GroupTheory.PGroup.ExtraspecialInvolution

/-!
# Counting outside-core products by incidence

Write H = C_G(z), Q = F*(H), and F for the fusion eight. The literal relation
z ∈ ⟨bt⟩ between outside involutions b and the twelve involutions t of Q − F
is invariant under H. Counting its incidence set in both directions reduces
the requested sixteen to two calculations at the selected outside involution:
its centralizer in H has order eight, and it has eight partners in Q − F.

The symmetric-three quotient gives the centralizer order from four fixed
points on Q. The product criterion is transported through the actual core
inclusions: (bt)² is the intrinsic norm α(t)t. Its square lies in ⟨z⟩, and
excluding a nontrivial central norm makes z ∈ ⟨bt⟩ equivalent to a nonidentity
fourth power. F contributes no such norm because it is elementary and H-normal.

Relative quaternion normality and inversion of the original cubic make the
selected action outer on both quaternion factors. The intrinsic norm theorem
then supplies the central-norm exclusion and eight partners. Double counting
gives 24 · 8 = 12 · 16. The final theorem retains only the supplied orbit
profile as an independent local input, and applies to every core involution
not conjugate to z, using the profile's core transitivity.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 2.3, 2.7 and the product count in 4.3.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.Census
open Subgroup
variable {G : Type*} [Group G] {z u t : G}

/-- All involutions of the literal centralizer outside its core. -/
public abbrev OutsideInvolutions (z : G) :=
  {b : G // b ∈ Centralizer z ∧ b ∉ coreInG z ∧ orderOf b = 2}

/-- Long-core partners of an outside element, using literal cyclic membership. -/
public abbrev CorePartners (z b : G) :=
  {x : CoreSecond z // z ∈ zpowers (b * (x : G))}

private theorem cyclic_conj_iff (c : Centralizer z) (b t : G) :
    z ∈ zpowers (MulAut.conj (c : G) b * MulAut.conj (c : G) t) ↔
      z ∈ zpowers (b * t) := by
  let e := MulAut.conj (c : G)
  have hez : e z = z := mul_inv_eq_iff_eq_mul.mpr
    (mem_centralizer_singleton_iff.mp c.property)
  change z ∈ zpowers (e b * e t) ↔ _
  rw [← map_mul, mem_zpowers_iff, mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, e.injective ?_⟩
    rwa [map_zpow, hez]
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← map_zpow, hn, hez]⟩

private theorem outside_conj_iff [Finite G] (h : Hypotheses z)
    (c : Centralizer z) (b : G) :
    (MulAut.conj (c : G) b ∈ Centralizer z ∧
      MulAut.conj (c : G) b ∉ coreInG z ∧
      orderOf (MulAut.conj (c : G) b) = 2) ↔
      (b ∈ Centralizer z ∧ b ∉ coreInG z ∧ orderOf b = 2) := by
  have hH := mem_normalizer_iff.mp ((Centralizer z).le_normalizer c.property) b
  have hcQ : (c : G) ∈ normalizer (coreInG z : Set G) :=
    h.normalizer_core.symm ▸ c.property
  have hQ := mem_normalizer_iff.mp hcQ b
  rw [(MulAut.conj (c : G)).orderOf_eq]
  exact and_congr hH.symm (and_congr (not_congr hQ.symm) Iff.rfl)

private theorem coreSecond_conj_iff [Finite G] (h : Hypotheses z)
    (c : Centralizer z) (x : G) :
    (MulAut.conj (c : G) x ∈ coreInG z ∧
      orderOf (MulAut.conj (c : G) x) = 2 ∧
      MulAut.conj (c : G) x ∉ fusionCore z) ↔
      (x ∈ coreInG z ∧ orderOf x = 2 ∧ x ∉ fusionCore z) := by
  have hcQ : (c : G) ∈ normalizer (coreInG z : Set G) :=
    h.normalizer_core.symm ▸ c.property
  have hQ := mem_normalizer_iff.mp hcQ x
  have hF := mem_normalizer_iff.mp (h.centralizer_le_normalizer_fusionCore c.property) x
  rw [(MulAut.conj (c : G)).orderOf_eq]
  change (_ ∧ _ ∧ ¬ _ ∈ _) ↔ _
  exact and_congr hQ.symm (and_congr Iff.rfl (not_congr hF.symm))

private noncomputable def outsideProductsConjEquiv [Finite G] (h : Hypotheses z)
    (c : Centralizer z) (t : G) :
    OutsideProducts z t ≃ OutsideProducts z (MulAut.conj (c : G) t) := by
  apply Equiv.subtypeEquiv (MulAut.conj (c : G)).toEquiv
  intro b
  change (_ ∧ _ ∧ _ ∧ _) ↔
    (MulAut.conj (c : G) b ∈ Centralizer z ∧
      MulAut.conj (c : G) b ∉ coreInG z ∧
      orderOf (MulAut.conj (c : G) b) = 2 ∧
      z ∈ zpowers (MulAut.conj (c : G) b * MulAut.conj (c : G) t))
  rw [cyclic_conj_iff]
  have hb := outside_conj_iff h c b
  tauto

private noncomputable def coreSecondConjEquiv [Finite G] (h : Hypotheses z)
    (c : Centralizer z) : CoreSecond z ≃ CoreSecond z :=
  Equiv.subtypeEquiv (MulAut.conj (c : G)).toEquiv
    (fun x => (coreSecond_conj_iff h c x).symm)

private noncomputable def corePartnersConjEquiv [Finite G] (h : Hypotheses z)
    (c : Centralizer z) (b : G) :
    CorePartners z b ≃ CorePartners z (MulAut.conj (c : G) b) := by
  apply Equiv.subtypeEquiv (coreSecondConjEquiv h c)
  intro x
  exact (cyclic_conj_iff c b x).symm

private def incidenceEquiv (z : G) :
    (Σ b : OutsideInvolutions z, CorePartners z (b : G)) ≃
      (Σ t : CoreSecond z, OutsideProducts z (t : G)) where
  toFun p := ⟨p.2.val, ⟨p.1.val, p.1.property.1, p.1.property.2.1,
    p.1.property.2.2, p.2.property⟩⟩
  invFun p := ⟨⟨p.2.val, p.2.property.1, p.2.property.2.1, p.2.property.2.2.1⟩,
    ⟨p.1, p.2.property.2.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Count the same cyclic-product incidence relation in its two directions. -/
public theorem outside_products_double_count [Finite G] (h : Hypotheses z)
    (o : OrbitData z u) (ht : t ∈ coreInG z ∧ orderOf t = 2 ∧ t ∉ fusionCore z) :
    Nat.card (OutsideInvolutions z) * Nat.card (CorePartners z u) =
      12 * Nat.card (OutsideProducts z t) := by
  classical
  let : Fintype (OutsideInvolutions z) := Fintype.ofFinite _
  let : Fintype (CoreSecond z) := Fintype.ofFinite _
  have hrows (b : OutsideInvolutions z) :
      Nat.card (CorePartners z (b : G)) = Nat.card (CorePartners z u) := by
    obtain ⟨c, hc⟩ := o.outside_transitive b b.property.1 b.property.2.1 b.property.2.2
    rw [← hc]
    exact (Nat.card_congr (corePartnersConjEquiv h c u)).symm
  have hcols (x : CoreSecond z) :
      Nat.card (OutsideProducts z (x : G)) = Nat.card (OutsideProducts z t) := by
    obtain ⟨c, hc⟩ := o.core_transitive ⟨t, ht⟩ x
    rw [← hc]
    exact (Nat.card_congr (outsideProductsConjEquiv h c t)).symm
  have he := Nat.card_congr (incidenceEquiv (G := G) z)
  rw [Nat.card_sigma, Nat.card_sigma] at he
  simp only [hrows, hcols, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, o.core_card] at he
  exact he

/-- Orbit-stabilizer for the supplied outside-involution orbit. -/
public theorem outside_involutions_card_mul_centralizer [Finite G] (h : Hypotheses z)
    (o : OrbitData z u) (hu : u ∈ Centralizer z ∧ u ∉ coreInG z ∧ orderOf u = 2) :
    Nat.card (OutsideInvolutions z) *
      Nat.card (Centralizer z ⊓ Centralizer u : Subgroup G) = 192 := by
  let : MulAction (Centralizer z) G :=
    MulAction.compHom G (MulAut.conj.comp (Centralizer z).subtype)
  have horbit : MulAction.orbit (Centralizer z) u =
      {b : G | b ∈ Centralizer z ∧ b ∉ coreInG z ∧ orderOf b = 2} := by
    ext b
    constructor
    · rintro ⟨c, rfl⟩
      exact (outside_conj_iff h c u).mpr hu
    · intro hb
      exact o.outside_transitive b hb.1 hb.2.1 hb.2.2
  have hstab : MulAction.stabilizer (Centralizer z) u =
      (Centralizer u).subgroupOf (Centralizer z) := by
    ext c
    change MulAut.conj (c : G) u = u ↔ (c : G) ∈ Centralizer u
    rw [mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul
  have hcard : Nat.card (MulAction.stabilizer (Centralizer z) u) =
      Nat.card (Centralizer z ⊓ Centralizer u : Subgroup G) := by
    rw [hstab]
    exact Nat.card_congr {
      toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
      invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (Centralizer z) u)
  rw [Nat.card_prod, horbit, hcard, h.centralizer_card] at hc
  exact hc


private theorem product_pow_four_mem [Finite G] (h : Hypotheses z)
    (b : Centralizer z) (t : Core z) (hb : b ^ 2 = 1) :
    (((b : G) * ((t : Centralizer z) : G)) ^ 4) ∈ zpowers z := by
  let α : MulAut (Core z) := MulAut.conjNormal b
  have hbI : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hb)
  have he : ((b : G) * ((t : Centralizer z) : G)) ^ 2 =
      (((α t * t : Core z) : Centralizer z) : G) := by
    change _ = (b : G) * ((t : Centralizer z) : G) * ((b⁻¹ : Centralizer z) : G) *
      ((t : Centralizer z) : G)
    simp only [hbI, pow_two, mul_assoc]
  have hfour : ((b : G) * ((t : Centralizer z) : G)) ^ 4 =
      ((((α t * t)^2 : Core z) : Centralizer z) : G) := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, he]
    rfl
  rw [hfour]
  let : IsExtraspecial 2 (Core z) := h.extraspecial
  have hm := mem_map_of_mem (Core z).subtype (IsExtraspecial.square_mem_center (α t * t))
  rw [h.core_center_image] at hm
  exact (MonoidHom.map_zpowers (Centralizer z).subtype (distinguished z)) ▸
    mem_map_of_mem (Centralizer z).subtype hm

private theorem cyclic_iff_fourth_ne_one [Finite G] (h : Hypotheses z)
    (b : Centralizer z) (t : Core z) (hb : b ^ 2 = 1)
    (hout : b ∉ Core z)
    (hn : ((b : G) * ((t : Centralizer z) : G)) ^ 2 ≠ z) :
    z ∈ zpowers ((b : G) * ((t : Centralizer z) : G)) ↔
      ((b : G) * ((t : Centralizer z) : G)) ^ 4 ≠ 1 := by
  classical
  let v := (b : G) * ((t : Centralizer z) : G)
  have hvout : v ∉ coreInG z := by
    intro hm
    have htQ : ((t : Centralizer z) : G) ∈ coreInG z :=
      mem_map_of_mem (Centralizer z).subtype t.property
    have hbQ : (b : G) ∈ coreInG z := by
      have hm' := (coreInG z).mul_mem hm ((coreInG z).inv_mem htQ)
      simpa only [v, mul_inv_cancel_right] using hm'
    apply hout
    have hh : b ∈ (coreInG z).subgroupOf (Centralizer z) := hbQ
    rwa [coreInG_subgroupOf] at hh
  have hline := product_pow_four_mem h b t hb
  change v ^ 4 ∈ zpowers z at hline
  constructor
  · intro hz hv4
    have hvo : orderOf v ∣ 4 := orderOf_dvd_of_pow_eq_one hv4
    have hmod : z = v ^ (orderOf v / 2) := by
      have he := IsCyclic.eq_of_orderOf_eq_two
        (x := (⟨z, hz⟩ : zpowers v))
        (y := ⟨v ^ (orderOf v / 2), pow_mem (mem_zpowers v) _⟩)
        ((Subgroup.orderOf_coe _).symm.trans h.involution)
      have hdiv : 2 ∣ orderOf v := by
        rw [← Nat.card_zpowers]
        exact h.involution ▸ (Subgroup.orderOf_coe (⟨z, hz⟩ : zpowers v)) ▸
          orderOf_dvd_natCard (⟨z, hz⟩ : zpowers v)
      have hn0 : orderOf v ≠ 0 := orderOf_pos v |>.ne'
      have hp : orderOf (v ^ (orderOf v / 2)) = 2 := by
        rw [orderOf_pow, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hdiv),
          Nat.div_div_self hdiv hn0]
      exact congrArg Subtype.val (he ((Subgroup.orderOf_coe _).symm.trans hp))
    have ho : orderOf v = 1 ∨ orderOf v = 2 ∨ orderOf v = 4 := by
      obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
        (show orderOf v ∣ 2 ^ 2 from hvo)
      interval_cases k <;> simp_all only [pow_zero, pow_one, Nat.reducePow, true_or, or_true]
    rcases ho with ho | ho | ho
    · have he : v = 1 := orderOf_eq_one_iff.mp ho
      exact hvout (he ▸ (coreInG z).one_mem)
    · have he : z = v := by simpa only [ho, Nat.reduceDiv, pow_one] using hmod
      exact hvout (he ▸ h.involution_mem_coreInG)
    · exact hn (by simpa only [ho, Nat.reduceDiv] using hmod.symm)
  · intro hv4
    have hz : v ^ 4 = z := by
      rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hline
      obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hline
      have hn' := Finset.mem_range.mp hn
      interval_cases n
      · exact (hv4 (by simpa using he.symm)).elim
      · simpa only [pow_one] using he.symm
    exact (congrArg (fun w : G => w ∈ zpowers v) hz).mp (pow_mem (mem_zpowers v) 4)


private theorem perm_three_commuting_involution :
    ∀ w v : Equiv.Perm (Fin 3), w ^ 2 = 1 → w ≠ 1 →
      v * w = w * v → v = 1 ∨ v = w := by decide

/-- Four fixed core elements give an order-eight centralizer of an outside involution. -/
public theorem centralizer_card_of_fixed_four [Finite G] (h : Hypotheses z)
    (u : Centralizer z) (hu2 : u ^ 2 = 1) (huQ : u ∉ Core z)
    (hf : Nat.card ((MulAut.conjNormal u : MulAut (Core z)).toMonoidHom.eqLocus
      (MonoidHom.id (Core z))) = 4) :
    Nat.card (Centralizer z ⊓ Centralizer (u : G) : Subgroup G) = 8 := by
  classical
  let e := h.quotient_model.some
  let π : Centralizer z →* Equiv.Perm (Fin 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Core z))
  have hπ (v : Centralizer z) : π v = 1 ↔ v ∈ Core z := by
    change e (QuotientGroup.mk' (Core z) v) = 1 ↔ _
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff v
  have hw2 : (π u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have hw1 : π u ≠ 1 := fun he => huQ ((hπ u).mp he)
  have hw : orderOf (π u) = 2 := orderOf_eq_prime hw2 hw1
  let K := centralizer ({u} : Set (Centralizer z))
  let f : K →* Equiv.Perm (Fin 3) := π.comp K.subtype
  have hr : f.range = zpowers (π u) := by
    apply le_antisymm
    · rintro y ⟨v, rfl⟩
      have hc : (v : Centralizer z) * u = u * (v : Centralizer z) :=
        mem_centralizer_singleton_iff.mp v.property
      have hc' : π (v : Centralizer z) * π u = π u * π (v : Centralizer z) := by
        simpa only [map_mul] using congrArg π hc
      rcases perm_three_commuting_involution (π u) (π v) hw2 hw1 hc' with hv | hv
      · change π (v : Centralizer z) ∈ _
        rw [hv]
        exact one_mem _
      · change π (v : Centralizer z) ∈ _
        rw [hv]
        exact mem_zpowers _
    · apply zpowers_le.mpr
      exact ⟨⟨u, mem_centralizer_singleton_iff.mpr rfl⟩, rfl⟩
  let F := (MulAut.conjNormal u : MulAut (Core z)).toMonoidHom.eqLocus
    (MonoidHom.id (Core z))
  have hF (q : Core z) : q ∈ F ↔ (q : Centralizer z) * u = u * (q : Centralizer z) := by
    change MulAut.conjNormal u q = q ↔ _
    rw [Subtype.ext_iff]
    change u * (q : Centralizer z) * u⁻¹ = q ↔ _
    rw [mul_inv_eq_iff_eq_mul]
    exact eq_comm
  let E : f.ker ≃ F := {
    toFun := fun v => ⟨⟨v.val.val, (hπ v.val).mp v.property⟩,
      (hF _).mpr (mem_centralizer_singleton_iff.mp v.val.property)⟩
    invFun := fun q => ⟨⟨q.val.val,
      mem_centralizer_singleton_iff.mpr ((hF q.val).mp q.property)⟩,
      (hπ q.val).mpr q.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hk : Nat.card f.ker = 4 := (Nat.card_congr E).trans hf
  have hc := f.ker.card_mul_index
  rw [hk, index_ker, hr, Nat.card_zpowers, hw] at hc
  have hK : Nat.card K = Nat.card (Centralizer z ⊓ Centralizer (u : G) : Subgroup G) := by
    apply Nat.card_congr
    exact {
      toFun := fun v => ⟨v.val.val, v.val.property, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp v.property))⟩
      invFun := fun v => ⟨⟨v.val, v.property.1⟩,
        mem_centralizer_singleton_iff.mpr (Subtype.ext
          (mem_centralizer_singleton_iff.mp v.property.2))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  omega


/-- The intrinsic quaternion product count gives the literal partners of the selected
outside involution; products in the fusion eight have square one and are excluded. -/
public theorem corePartners_card_of_quaternion_products [Finite G] (h : Hypotheses z)
    (d : FusionEightData z) (a : SelectedFusionData h)
    (hcentral : ∀ x : Core z, x ^ 2 = 1 →
      (MulAut.conjNormal (⟨a.u, a.u_centralizes⟩ : Centralizer z) x * x) ∈ center (Core z) →
      MulAut.conjNormal (⟨a.u, a.u_centralizes⟩ : Centralizer z) x * x = 1)
    (hcount : Nat.card {x : Core z // x ^ 2 = 1 ∧
      (MulAut.conjNormal (⟨a.u, a.u_centralizes⟩ : Centralizer z) x * x) ^ 2 ≠ 1} = 8) :
    Nat.card (CorePartners z a.u) = 8 := by
  classical
  let b : Centralizer z := ⟨a.u, a.u_centralizes⟩
  let α : MulAut (Core z) := MulAut.conjNormal b
  have hb : b ^ 2 = 1 := Subtype.ext (a.u_order ▸ pow_orderOf_eq_one a.u)
  have hbI : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hb)
  have hbQ : b ∉ Core z := fun hb =>
    a.u_not_core (mem_map_of_mem (Centralizer z).subtype hb)
  let emb : Core z →* G := (Centralizer z).subtype.comp (Core z).subtype
  have emb_inj : Function.Injective emb :=
    (Centralizer z).subtype_injective.comp (Core z).subtype_injective
  have hpow (x : Core z) : (a.u * emb x) ^ 2 = emb (α x * x) := by
    change _ = (b : G) * emb x * ((b⁻¹ : Centralizer z) : G) * emb x
    simp only [hbI, pow_two, mul_assoc]
    rfl
  have hpow4 (x : Core z) : (a.u * emb x) ^ 4 = emb ((α x * x) ^ 2) := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hpow, map_pow]
  have hcyc (x : Core z) (hx : x ^ 2 = 1) :
      z ∈ zpowers (a.u * emb x) ↔ (α x * x) ^ 2 ≠ 1 := by
    have hn : (a.u * emb x) ^ 2 ≠ z := by
      intro he
      rw [hpow] at he
      let zz : Core z := ⟨distinguished z, h.distinguished_mem_core⟩
      have heq : α x * x = zz := emb_inj he
      have hzZ : zz ∈ center (Core z) := by
        apply mem_center_iff.mpr
        intro q
        apply Subtype.ext
        apply Subtype.ext
        exact mem_centralizer_singleton_iff.mp q.val.property
      have hn1 := hcentral x hx (heq ▸ hzZ)
      have hzz : z = 1 := by
        have hh := congrArg emb hn1
        change emb (α x * x) = emb 1 at hh
        exact he.symm.trans (hh.trans (map_one emb))
      have hzord := h.involution
      simp [hzz] at hzord
    have hh := cyclic_iff_fourth_ne_one h b x hb hbQ hn
    change z ∈ zpowers (a.u * emb x) ↔ (a.u * emb x) ^ 4 ≠ 1 at hh
    rw [hpow4] at hh
    exact hh.trans (not_congr (by
      rw [← emb.map_one]
      exact emb_inj.eq_iff))
  have houtside (x : Core z) (hx : (α x * x) ^ 2 ≠ 1) : emb x ∉ fusionCore z := by
    intro hxF
    let : IsElementaryAbelian 2 (fusionCore z) := d.elementary
    have hax : emb (α x) ∈ fusionCore z :=
      (mem_normalizer_iff.mp (h.centralizer_le_normalizer_fusionCore a.u_centralizes)
        (emb x)).mp hxF
    have hm : emb (α x * x) ∈ fusionCore z := by
      rw [map_mul]
      exact (fusionCore z).mul_mem hax hxF
    apply hx
    apply emb_inj
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (emb (α x * x)) hm
  let M := {x : Core z // x ^ 2 = 1 ∧ (α x * x) ^ 2 ≠ 1}
  let f : M → CorePartners z a.u := fun x =>
    have hxF := houtside x x.property.2
    have hx1 : emb x ≠ 1 := fun he => hxF (he ▸ (fusionCore z).one_mem)
    ⟨⟨emb x, mem_map_of_mem (Centralizer z).subtype x.val.property,
      orderOf_eq_prime (by rw [← map_pow, x.property.1, map_one]) hx1, hxF⟩,
      (hcyc x x.property.1).mpr x.property.2⟩
  have hfi : Function.Injective f := by
    intro x y he
    exact Subtype.ext (emb_inj (congrArg (fun p : CorePartners z a.u => (p.val : G)) he))
  have hfs : Function.Surjective f := by
    intro p
    obtain ⟨q, hq, he⟩ := p.val.property.1
    let x : Core z := ⟨q, hq⟩
    have hex : emb x = (p.val : G) := he
    have hx : x ^ 2 = 1 := by
      apply emb_inj
      rw [map_pow, map_one, hex]
      have hh := pow_orderOf_eq_one (p.val : G)
      rwa [p.val.property.2.1] at hh
    have hm : x ^ 2 = 1 ∧ (α x * x) ^ 2 ≠ 1 := ⟨hx, (hcyc x hx).mp (hex.symm ▸ p.property)⟩
    exact ⟨⟨x, hm⟩, Subtype.ext (Subtype.ext hex)⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hfi, hfs⟩)).symm.trans hcount

/-- Two local calculations at the selected involution give sixteen partners at every long-core involution. -/
public theorem outside_products_card_of_selected_counts [Finite G] (h : Hypotheses z)
    (d : FusionEightData z) (a : SelectedFusionData h) (o : OrbitData z a.u)
    (hc : Nat.card (Centralizer z ⊓ Centralizer a.u : Subgroup G) = 8)
    (hp : Nat.card (CorePartners z a.u) = 8)
    (htQ : t ∈ coreInG z) (ht : orderOf t = 2) (hnt : ¬ IsConj z t) :
    Nat.card (OutsideProducts z t) = 16 := by
  have htF : t ∉ fusionCore z := fun hf =>
    hnt (d.fusion t hf (fun he => by simp [he] at ht))
  have hb := outside_involutions_card_mul_centralizer h o
    ⟨a.u_centralizes, a.u_not_core, a.u_order⟩
  have he := outside_products_double_count h o ⟨htQ, ht, htF⟩
  rw [hc] at hb
  rw [hp] at he
  omega

/-- Assembly from the selected quaternion action and the intrinsic product calculation. -/
public theorem outside_products_card_of_quaternion_action [Finite G] (h : Hypotheses z)
    (d : FusionEightData z) (a : SelectedFusionData h) (o : OrbitData z a.u)
    (q : QuaternionCentralProductData (Core z))
    (ha : q.BothOuter (MulAut.conjNormal (⟨a.u, a.u_centralizes⟩ : Centralizer z)))
    (hcentral : ∀ x : Core z, x ^ 2 = 1 →
      (MulAut.conjNormal (⟨a.u, a.u_centralizes⟩ : Centralizer z) x * x) ∈ center (Core z) →
      MulAut.conjNormal (⟨a.u, a.u_centralizes⟩ : Centralizer z) x * x = 1)
    (hcount : Nat.card {x : Core z // x ^ 2 = 1 ∧
      (MulAut.conjNormal (⟨a.u, a.u_centralizes⟩ : Centralizer z) x * x) ^ 2 ≠ 1} = 8)
    (htQ : t ∈ coreInG z) (ht : orderOf t = 2) (hnt : ¬ IsConj z t) :
    Nat.card (OutsideProducts z t) = 16 := by
  let b : Centralizer z := ⟨a.u, a.u_centralizes⟩
  have hb : b ^ 2 = 1 := Subtype.ext (a.u_order ▸ pow_orderOf_eq_one a.u)
  have hbQ : b ∉ Core z := fun hb =>
    a.u_not_core (mem_map_of_mem (Centralizer z).subtype hb)
  have ha2 : (MulAut.conjNormal b : MulAut (Core z)) ^ 2 = 1 := by
    rw [← map_pow, hb, map_one]
  exact outside_products_card_of_selected_counts h d a o
    (centralizer_card_of_fixed_four h b hb hbQ (ha.fixed_card q ha2))
    (corePartners_card_of_quaternion_products h d a hcentral hcount) htQ ht hnt

/-- The sixteen outside-core involutions whose product with any second-class
core involution generates a cyclic subgroup containing z. The orbit profile
is the sole remaining census input; the action and norm facts are proved. -/
public theorem outside_products_card [Finite G] (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : FusionEightData z)
    (a : SelectedFusionData h) (o : OrbitData z a.u)
    (htQ : t ∈ coreInG z) (ht : orderOf t = 2) (hnt : ¬ IsConj z t) :
    Nat.card (OutsideProducts z t) = 16 := by
  obtain ⟨q⟩ := h.quaternionCentralProduct
  let b : Centralizer z := ⟨a.u, a.u_centralizes⟩
  have hb : b ^ 2 = 1 := Subtype.ext (a.u_order ▸ pow_orderOf_eq_one a.u)
  have ha2 : (MulAut.conjNormal b : MulAut (Core z)) ^ 2 = 1 := by
    rw [← map_pow, hb, map_one]
  have ha := selected_bothOuter h hn a q
  obtain ⟨hcentral, hcount⟩ := q.involution_products (MulAut.conjNormal b) ha2 ha
  exact outside_products_card_of_quaternion_action h d a o q ha hcentral hcount htQ ht hnt

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.Census
