module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicExclusionCoreGeometry
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
public import Theory.GroupAction.Extraspecial27ElementaryActor
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.CentralQuotientInversionFixedDerived
public import Theory.ElementaryAbelian.Join

/-!
# Frattini-fixed involutions in the terminal extraspecial branch

The literal map P → H/O₂(H) is injective and identifies P with O²(H/O₂(H)).
Self-centralization of that residual makes every two-subgroup of the quotient
act faithfully on it. The extraspecial order-27 automorphism bound therefore
bounds a center-fixing elementary two-subgroup by order two.

An involution in C_T(Φ(P)) fixes the unique nonidentity point of C_V(Φ(P)),
namely the original inverter. Their elementary join has image of order two,
so the involution is q or qv with q in C_{O₂(H)}(Φ(P)). Replacing a fixed
involutory orbit generator in O₂(L) by q preserves its T-span modulo V and
feeds the proved terminal contradiction.

The construction of that orbit generator from the L₃(2) core module remains
with qt-d-12213-cyclic-block. LocalConfigurationCyclicExclusionCoreInvolutionAssembly
applies the reduction to the original cyclic-block consumer.
Source: Aschbacher–Smith, 12.2.23, printed p.804.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U W : Subgroup G} {d p : ℕ} {g v : G}
namespace InvariantOddLocalAnalysis
variable (S : InvariantOddLocalAnalysis T L V d p H P U W g v)
include S

/-- The inclusion of the original P followed by H → H/O₂(H). -/
@[expose] def oddQuotientMap : P →* H ⧸ pCore 2 H :=
  (QuotientGroup.mk' (pCore 2 H)).comp (inclusion (S.overgroup ▸ le_sup_left))

omit [Finite G] in
/-- The odd subgroup meets the original two-core trivially. -/
theorem oddQuotientMap_injective : Function.Injective S.oddQuotientMap := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  apply Subtype.ext
  have hxQ : (x : G) ∈ H.pCoreIn 2 :=
    mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff _).mp hx)
  exact (S.pgroup.disjoint_of_coprime (isPGroup_pCoreIn 2 H)
    S.odd_prime.coprime_two_right).le_bot ⟨x.property, hxQ⟩

/-- The literal residual equality descends to the star quotient. -/
theorem oddQuotientMap_range :
    S.oddQuotientMap.range = pResidual 2 (H ⧸ pCore 2 H) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hPW : P ⊔ W ≤ H := sup_le (S.overgroup ▸ le_sup_left)
    (S.in_core.trans (pCoreIn_le 2 H))
  have hres : pResidual 2 H = P.subgroupOf H ⊔ W.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [S.residual, Subgroup.map_sup, map_subgroupOf_eq_of_le (le_sup_left.trans hPW),
      map_subgroupOf_eq_of_le (le_sup_right.trans hPW)]
  rw [← map_pResidual_quotient 2 (pCore 2 H), hres, Subgroup.map_sup]
  have hW : (W.subgroupOf H).map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mpr
    have hQ := S.in_core hx
    obtain ⟨y, hy, he⟩ := hQ
    have hxy : y = x := Subtype.ext he
    exact hxy ▸ hy
  rw [hW, sup_bot_eq]
  ext x
  exact ⟨fun ⟨a, ha⟩ => ⟨inclusion (S.overgroup ▸ le_sup_left) a, a.property, ha⟩,
    fun ⟨a, ha, he⟩ => ⟨⟨a, ha⟩, he⟩⟩

/-- The original P, identified with the two-residual of H/O₂(H). -/
@[expose] def oddQuotientResidualEquiv : P ≃* pResidual 2 (H ⧸ pCore 2 H) :=
  (MonoidHom.ofInjective S.oddQuotientMap_injective).trans
    (MulEquiv.subgroupCongr S.oddQuotientMap_range)

/-- The residual identification retains the original quotient map. -/
@[simp] theorem oddQuotientResidualEquiv_apply (x : P) :
    (S.oddQuotientResidualEquiv x : H ⧸ pCore 2 H) = S.oddQuotientMap x := rfl

/-- An elementary subgroup of T centralizing Φ(P) modulo O₂(H) has
image of order at most two in the original star quotient. -/
theorem extraspecial_elementary_quotient_card_le_two
    (he : IsExtraspecial p P) (hc : Nat.card P = p ^ 3) (hp : p = 3)
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hET : E ≤ (T : Subgroup G))
    (hcomm : ⁅E, (frattini P).map P.subtype⁆ ≤ H.pCoreIn 2) :
    Nat.card ((E.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) ≤ 2 := by
  subst p
  let := he
  let J := H ⧸ pCore 2 H
  let q := QuotientGroup.mk' (pCore 2 H)
  let R := pResidual 2 J
  let F := (E.subgroupOf H).map q
  let : IsElementaryAbelian 2 (E.subgroupOf H) := IsElementaryAbelian.subgroupOf (hET.trans S.hstar.1.1.2)
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map q
  let e := S.oddQuotientResidualEquiv
  let a : F →* MulAut R := R.normalizerMonoidHom.comp
    ((MonoidHom.id J).codRestrict _ (fun x => by rw [normalizer_eq_top]; trivial) |>.comp F.subtype)
  let b : F →* MulAut P := (MulAut.congr e.symm).toMonoidHom.comp a
  have hR : IsPGroup 3 R := S.pgroup.of_equiv e
  have hFR : Disjoint F R :=
    (IsElementaryAbelian.isPGroup 2 F).disjoint_of_coprime hR (by decide)
  have hfaith : Function.Injective b := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro t ht
    have ha : a t = 1 := (MulAut.congr e.symm).injective (ht.trans (map_one _).symm)
    have hcent : (t : J) ∈ centralizer (R : Set J) := by
      intro r hr
      have hh := congrArg (fun f : MulAut R => (f ⟨r, hr⟩ : J)) ha
      change (t : J) * r * (t : J)⁻¹ = r at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    apply Subtype.ext
    exact hFR.le_bot ⟨t.property,
      centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot (G := H) 2) hcent⟩
  have hfix : ∀ t : F, ∀ z ∈ center P, b t z = z := by
    intro t z hz
    obtain ⟨tH, htE, ht⟩ := t.property
    have hzPhi : (z : G) ∈ (frattini P).map P.subtype := by
      apply mem_map_of_mem
      rwa [IsExtraspecial.frattini_eq_center (p := 3)]
    have hd := hcomm (commutator_mem_commutator htE hzPhi)
    have hd' : ⁅tH, inclusion (S.overgroup ▸ le_sup_left) z⁆ ∈ pCore 2 H := by
      obtain ⟨y, hy, hy'⟩ := hd
      have hh : y = ⁅tH, inclusion (S.overgroup ▸ le_sup_left) z⁆ := Subtype.ext hy'
      exact hh ▸ hy
    have hq : Commute (t : J) (S.oddQuotientMap z) := by
      apply commutatorElement_eq_one_iff_commute.mp
      rw [← ht]
      change ⁅q tH, q (inclusion (S.overgroup ▸ le_sup_left) z)⁆ = 1
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr hd'
    apply e.injective
    change e (e.symm (a t (e z))) = e z
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change (t : J) * S.oddQuotientMap z * (t : J)⁻¹ = S.oddQuotientMap z
    exact mul_inv_eq_iff_eq_mul.mpr hq.eq
  exact MulAut.elementary_two_center_preserving_card_le_two (by simpa using hc) b hfaith hfix

/-- The original inverter fixes the extraspecial Frattini subgroup pointwise. -/
theorem extraspecial_inverter_centralizes_frattini
    (he : IsExtraspecial p P) :
    v ∈ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) := by
  let := he
  let : Fact p.Prime := ⟨S.prime⟩
  let a : MulAut P := P.normalizerMonoidHom ⟨v, S.inverter_normalizes⟩
  have hi (x : P) : a x * x ∈ center P := by
    rw [← IsExtraspecial.frattini_eq_center (p := p)]
    have hh := S.inverts_frattini_quotient x x.property
    obtain ⟨y, hy, heq⟩ := hh
    have heq' : y = a x * x := Subtype.ext heq
    exact heq' ▸ hy
  have hfix := a.fixes_derived_of_inverts_mod_center
    (IsExtraspecial.commutator_eq_center (p := p)).le hi
  rintro z ⟨z, hz, rfl⟩
  have hz' : z ∈ _root_.commutator P := by
    rwa [IsExtraspecial.commutator_eq_center (p := p),
      ← IsExtraspecial.frattini_eq_center (p := p)]
  have hh := congrArg Subtype.val ((MulAut.mem_fixedSubgroup a z).mp (hfix hz'))
  change v * (z : G) * v⁻¹ = z at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

omit [Finite G] in
/-- The inverter has nonidentity image in H/O₂(H). -/
theorem inverter_not_mem_hstar_core : v ∉ H.pCoreIn 2 := by
  intro hvQ
  have hPH : P ≤ H := S.overgroup ▸ le_sup_left
  have hgH : g ∈ H := hPH S.generator_mem
  have hvH : v ∈ H := pCoreIn_le 2 H hvQ
  let q := QuotientGroup.mk' (pCore 2 H)
  let vg : H := ⟨v, hvH⟩
  let gg : P := ⟨g, S.generator_mem⟩
  have hv : q vg = 1 := by
    apply (QuotientGroup.eq_one_iff vg).mpr
    obtain ⟨x, hx, he⟩ := hvQ
    have hh : x = vg := Subtype.ext he
    exact hh ▸ hx
  have hconj : vg * inclusion hPH gg * vg⁻¹ = inclusion hPH gg⁻¹ :=
    Subtype.ext S.inverts_generator
  have hinv := congrArg q hconj
  simp only [map_mul, map_inv, hv, one_mul, inv_one, mul_one] at hinv
  have hgg : S.oddQuotientMap gg = S.oddQuotientMap gg⁻¹ := hinv
  have heq : gg = gg⁻¹ := S.oddQuotientMap_injective hgg
  have hg2 : g ^ 2 = 1 := by
    have hh : g = g⁻¹ := congrArg Subtype.val heq
    calc
      g ^ 2 = g * g := pow_two _
      _ = g⁻¹ * g := congrArg (· * g) hh
      _ = 1 := inv_mul_cancel _
  have hp2 : p ∣ 2 := S.generator_order ▸ orderOf_dvd_of_pow_eq_one hg2
  exact S.odd_prime.not_two_dvd_nat (by
    rw [(Nat.prime_dvd_prime_iff_eq S.prime Nat.prime_two).mp hp2])

/-- Every square-one element of C_T(Φ(P)) is q or qv with
q in the literal Frattini centralizer inside O₂(H). -/
theorem extraspecial_fixed_involution_factorization
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (he : IsExtraspecial p P) (hc : Nat.card P = p ^ 3) (hp : p = 3)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥)
    (t : G) (ht : t ∈ (T : Subgroup G)) (ht2 : t ^ 2 = 1)
    (htPhi : t ∈ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G)) :
    ∃ q ∈ H.pCoreIn 2 ⊓ centralizer
        (((frattini P).map P.subtype : Subgroup G) : Set G),
      t = q ∨ t = q * v := by
  let Φ := (frattini P).map P.subtype
  let C := V ⊓ centralizer (Φ : Set G)
  have hvPhi := S.extraspecial_inverter_centralizes_frattini he
  have hvC : v ∈ C := ⟨S.inverter_mem, hvPhi⟩
  have htC : t ∈ normalizer (C : Set G) := inf_normalizer_le_normalizer_inf
    ⟨hTV ht, normalizer_le_normalizer_centralizer _
      (Subgroup.centralizer_le_normalizer _ htPhi)⟩
  have htv : Commute t v := (normalizer_le_centralizer_of_card_two C
    (S.chosen_split_frattini D A hf).2.2 htC v hvC).symm
  let E := zpowers t ⊔ zpowers v
  let := D.elementary
  let : IsElementaryAbelian 2 (zpowers t) := IsElementaryAbelian.zpowers_of_pow_eq_one ht2
  let : IsElementaryAbelian 2 (zpowers v) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (elemPow_eq_one_of_isElementaryAbelian v S.inverter_mem)
  have hcv : zpowers v ≤ centralizer (zpowers t : Set G) := by
    apply zpowers_le.mpr
    intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    exact (htv.zpow_left n).eq
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.sup_of_le_centralizer hcv
  have hET : E ≤ (T : Subgroup G) :=
    sup_le (zpowers_le.mpr ht) (zpowers_le.mpr (D.le_sylow S.inverter_mem))
  have hEPhi : E ≤ centralizer (Φ : Set G) :=
    sup_le (zpowers_le.mpr htPhi) (zpowers_le.mpr hvPhi)
  let q := QuotientGroup.mk' (pCore 2 H)
  let F := (E.subgroupOf H).map q
  have hFle : Nat.card F ≤ 2 := S.extraspecial_elementary_quotient_card_le_two he hc hp E hET
    (by rw [commutator_eq_bot_iff_le_centralizer.mpr hEPhi]; exact bot_le)
  let tH : H := ⟨t, S.hstar.1.1.2 ht⟩
  let vH : H := ⟨v, S.hstar.1.1.2 (D.le_sylow S.inverter_mem)⟩
  have hvF : q vH ∈ F := mem_map_of_mem q
    (show vH ∈ E.subgroupOf H from (le_sup_right : zpowers v ≤ E) (mem_zpowers v))
  have htF : q tH ∈ F := mem_map_of_mem q
    (show tH ∈ E.subgroupOf H from (le_sup_left : zpowers t ≤ E) (mem_zpowers t))
  have hvne : q vH ≠ 1 := fun hh => S.inverter_not_mem_hstar_core
    (mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff vH).mp hh))
  have hFcard : Nat.card F = 2 := by
    have : Nontrivial F := ⟨⟨⟨q vH, hvF⟩, 1, fun hh => hvne (congrArg Subtype.val hh)⟩⟩
    have hh : 1 < Nat.card F := Finite.one_lt_card
    omega
  obtain ⟨z, hz, hu⟩ := (Nat.card_eq_two_iff' (1 : F)).mp hFcard
  by_cases ht1 : q tH = 1
  · exact ⟨t, ⟨mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff tH).mp ht1), htPhi⟩, Or.inl rfl⟩
  · have hsame : q tH = q vH := congrArg Subtype.val
      ((hu ⟨q tH, htF⟩ (fun hh => ht1 (congrArg Subtype.val hh))).trans
        (hu ⟨q vH, hvF⟩ (fun hh => hvne (congrArg Subtype.val hh))).symm)
    have hprod : t * v⁻¹ ∈ H.pCoreIn 2 := by
      refine ⟨tH * vH⁻¹, ?_, rfl⟩
      change tH * vH⁻¹ ∈ pCore 2 H
      apply (QuotientGroup.eq_one_iff _).mp
      change q (tH * vH⁻¹) = 1
      rw [map_mul, map_inv, hsame, mul_inv_cancel]
    exact ⟨t * v⁻¹, ⟨hprod, (centralizer (Φ : Set G)).mul_mem htPhi
      ((centralizer (Φ : Set G)).inv_mem hvPhi)⟩, Or.inr (inv_mul_cancel_right t v).symm⟩

/-- Place a fixed involutory orbit generator in the original H-core by
removing the original inverter, which does not change its T-span modulo V. -/
theorem extraspecial_false_of_fixed_involution_orbit
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (he : IsExtraspecial p P) (hcard : Nat.card P = p ^ 3)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥)
    (hp : p = 3) (hd : d = 3) (hW : Nat.card W = 64)
    (horbit : ∃ t ∈ L.pCoreIn 2 ⊓ centralizer
        (((frattini P).map P.subtype : Subgroup G) : Set G),
      t ^ 2 = 1 ∧ L.pCoreIn 2 = componentOrbit (zpowers t) (T : Subgroup G) ⊔ V) :
    False := by
  obtain ⟨t, ht, ht2, hgen⟩ := horbit
  have hTQ : (T : Subgroup G) ≤ normalizer (L.pCoreIn 2 : Set G) :=
    D.sylow_normalizes_component.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hQT : L.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hQL := pCoreIn_mono_of_normalizes (p := 2)
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer D.sylow_normalizes_component)
    apply hQL.trans
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  obtain ⟨q, hq, heq⟩ := S.extraspecial_fixed_involution_factorization D A hTV
    he hcard hp hf t (hQT ht.1) ht2 ht.2
  have hqL : q ∈ L.pCoreIn 2 := by
    rcases heq with h | h
    · exact h ▸ ht.1
    · have hh := (L.pCoreIn 2).mul_mem ht.1
        ((L.pCoreIn 2).inv_mem (D.le_componentCore S.inverter_mem))
      simpa only [h, mul_inv_cancel_right] using hh
  let R := componentOrbit (zpowers q) (T : Subgroup G) ⊔ V
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (le_inf (le_normalizer_componentOrbit _ _) hTV).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have htR : t ∈ R := by
    have hqR : q ∈ R := (le_sup_left : componentOrbit (zpowers q) (T : Subgroup G) ≤ R)
      (le_componentOrbit _ _ (mem_zpowers q))
    rcases heq with h | h
    · exact h.symm ▸ hqR
    · rw [h]
      exact R.mul_mem hqR ((le_sup_right : V ≤ R) S.inverter_mem)
  have hgenq : L.pCoreIn 2 = R := by
    apply le_antisymm
    · rw [hgen]
      exact sup_le (iSup_conjugates_le_of_le_normalizer _ _ _ (zpowers_le.mpr htR) hTR)
        le_sup_right
    · exact sup_le (iSup_conjugates_le_of_le_normalizer _ _ _ (zpowers_le.mpr hqL) hTQ)
        D.le_componentCore
  exact S.extraspecial_false_of_core_orbit D A hTV he hcard hf hp hd hW ⟨q, hq, hgenq⟩

end InvariantOddLocalAnalysis
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
