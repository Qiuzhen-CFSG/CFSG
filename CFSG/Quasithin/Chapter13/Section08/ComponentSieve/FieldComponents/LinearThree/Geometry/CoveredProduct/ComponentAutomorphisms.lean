module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms
public import Theory.GroupAction.ModelConjugation.InnerImage

/-!
# The covered component action and the corrected source inverter

The same conjugation aligns K*, its Sylow intersection and the full L₀*
residual with one standard binary parabolic. An element of T therefore
preserves that residual, so its component action is inner. The source
factorization extends innerness to all of H*.

Fixing L₀/O₂(L₀) only puts a two-power actor's implementer in O₂(L₀*).
We lift that element through the actual source core map, prove that the
lift belongs to T, and correct the inverter inside T∩L. The corrected
inverter centralizes K* while still inverting X/O₂(X) and X*.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.21(1), printed p.957. No product or centralizer identification is
assumed here; their construction is a separate step.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
open ResidualPlacement
variable {G : Type*} [Group G]

/-- Align the component, its parabolic, residual and Sylow subgroup together. -/
noncomputable def markedComponentEquiv (H K L T : Subgroup G)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (p : ParabolicPlacement H K L T eK) :
    Source.starImage H K ≃* BinaryLinearThree.Group :=
  eK.trans (MulAut.conj p.conjugator)

theorem markedComponentEquiv_residual (H K L T : Subgroup G)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (p : ParabolicPlacement H K L T eK) :
    ((Source.starImage H (zero L)).subgroupOf (Source.starImage H K)).map
      (markedComponentEquiv H K L T eK p).toMonoidHom = residual p.standard := by
  change ((Source.starImage H (zero L)).subgroupOf (Source.starImage H K)).map
    ((MulAut.conj p.conjugator).toMonoidHom.comp eK.toMonoidHom) = _
  rw [← map_map]
  exact p.residual_mark

/-- The parabolic uses exactly the same component coordinates. -/
theorem markedComponentEquiv_parabolic (H K L T : Subgroup G)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (p : ParabolicPlacement H K L T eK) :
    p.parabolic.map (markedComponentEquiv H K L T eK p).toMonoidHom = p.standard := by
  change p.parabolic.map ((MulAut.conj p.conjugator).toMonoidHom.comp eK.toMonoidHom) = _
  rw [← map_map]
  exact p.parabolic_mark

/-- The actual source Sylow intersection is the standard Borel under those coordinates. -/
theorem markedComponentEquiv_sylow (H K L T : Subgroup G)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (p : ParabolicPlacement H K L T eK) :
    ((Source.starImage H T).subgroupOf (Source.starImage H K)).map
      (markedComponentEquiv H K L T eK p).toMonoidHom = Matrix.PSL3Two.borelSL := by
  rw [← p.sylow_eq]
  change (p.sylow : Subgroup (Source.starImage H K)).map
    ((MulAut.conj p.conjugator).toMonoidHom.comp eK.toMonoidHom) = _
  rw [← map_map]
  exact p.sylow_mark

/-- The literal conjugation action on the normal source component. -/
def componentAction (H K : Subgroup G) [(Source.starImage H K).Normal]
    (e : Source.starImage H K ≃* BinaryLinearThree.Group) :
    Source.Hstar H →* MulAut BinaryLinearThree.Group :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

private theorem componentAction_apply (H K : Subgroup G)
    [(Source.starImage H K).Normal]
    (e : Source.starImage H K ≃* BinaryLinearThree.Group)
    (g : Source.Hstar H) (x : Source.starImage H K) :
    componentAction H K e g (e x) = e (MulAut.conjNormal g x) := by
  change e (MulAut.conjNormal g (e.symm (e x))) = _
  rw [e.symm_apply_apply]

private theorem componentAction_stable (H K : Subgroup G)
    [(Source.starImage H K).Normal]
    (e : Source.starImage H K ≃* BinaryLinearThree.Group)
    (A : Subgroup (Source.Hstar H))
    (g : Source.Hstar H) (hg : g ∈ normalizer (A : Set (Source.Hstar H))) :
    ((A.subgroupOf (Source.starImage H K)).map e.toMonoidHom).map
      (componentAction H K e g).toMonoidHom =
      (A.subgroupOf (Source.starImage H K)).map e.toMonoidHom := by
  have hs : (A.subgroupOf (Source.starImage H K)).map
      (MulAut.conjNormal g).toMonoidHom = A.subgroupOf (Source.starImage H K) := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (mem_normalizer_iff.mp hg b.val).mp hb
    · intro ha
      refine ⟨MulAut.conjNormal g⁻¹ a, ?_, ?_⟩
      · exact (mem_normalizer_iff.mp ((normalizer (A : Set (Source.Hstar H))).inv_mem hg) a.val).mp ha
      · apply Subtype.ext
        change g * (g⁻¹ * a.val * (g⁻¹)⁻¹) * g⁻¹ = a.val
        group
  have he := Theory.GroupAction.ModelConjugation.stable_map_congr e _ _ hs
  exact he

private theorem star_normalizes_of_normalizes (H A B : Subgroup G)
    (hAB : A ≤ normalizer (B : Set G)) :
    Source.starImage H A ≤ normalizer (Source.starImage H B : Set (Source.Hstar H)) := by
  apply le_normalizer_iff.mpr
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  refine ⟨a * b * a⁻¹, le_normalizer_iff.mp hAB a.val ha b.val hb, ?_⟩
  simp only [map_mul, map_inv]

/-- Normalizing the actual residual rules out every outer component action. -/
theorem T_component_action_is_inner (H K L T : Subgroup G)
    [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (p : ParabolicPlacement H K L T eK)
    (hTL : T ≤ normalizer (L : Set G)) (t : Source.starImage H T) :
    ∃ g ∈ p.standard,
      componentAction H K (markedComponentEquiv H K L T eK p) t.val = MulAut.conj g := by
  apply Matrix.PSL3Two.MarkedAutomorphisms.preserving_residual_is_conj _ p.standard_eq
  change (residual p.standard).map _ = residual p.standard
  rw [← markedComponentEquiv_residual H K L T eK p]
  exact componentAction_stable H K _ _ t.val
    (star_normalizes_of_normalizes H T (zero L)
      (hTL.trans (normalizer_le_zero_normalizer L)) t.property)

/-- The full group acts by inner automorphisms, from the actual source generators. -/
theorem source_inner_action (H K L T V₁ : Subgroup G)
    [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (p : ParabolicPlacement H K L T eK)
    (hTL : T ≤ normalizer (L : Set G))
    (hgen : H = K ⊔ (one L T V₁ ⊔ T))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hzero : zero L ≤ K)
    (hcentral : Source.starImage H K ≤
      centralizer (Source.starImage H (plus L T V₁) : Set (Source.Hstar H))) :
    ∀ h : Source.Hstar H, ∃ k : Source.starImage H K,
      ∀ x : Source.starImage H K,
        h * x.val * h⁻¹ = k.val * x.val * k.val⁻¹ := by
  let e := markedComponentEquiv H K L T eK p
  let f := componentAction H K e
  let N := MulAut.conj.range.comap f
  have hK : Source.starImage H K ≤ N := by
    intro k hk
    refine ⟨e ⟨k,hk⟩, ?_⟩
    apply MulEquiv.ext
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    rw [componentAction_apply]
    change e ⟨k,hk⟩ * e x * (e ⟨k,hk⟩)⁻¹ = e (⟨k,hk⟩ * x * (⟨k,hk⟩)⁻¹)
    rw [map_mul, map_mul, map_inv]
  have hX : Source.starImage H (plus L T V₁) ≤ N := by
    intro x hx
    refine ⟨1, ?_⟩
    rw [map_one]
    apply MulEquiv.ext
    intro y
    obtain ⟨k,rfl⟩ := e.surjective y
    rw [componentAction_apply]
    change e k = e (MulAut.conjNormal x k)
    apply congrArg e
    apply Subtype.ext
    change k.val = x * k.val * x⁻¹
    rw [hcentral k.property x hx, mul_inv_cancel_right]
  have hT : Source.starImage H T ≤ N := by
    intro t ht
    obtain ⟨g,_,he⟩ := T_component_action_is_inner H K L T eK p hTL ⟨t,ht⟩
    exact ⟨g,he.symm⟩
  have hKH : K ≤ H := by rw [hgen]; exact le_sup_left
  have hDH : one L T V₁ ≤ H := by rw [hgen]; exact le_sup_left.trans le_sup_right
  have hTH : T ≤ H := by rw [hgen]; exact le_sup_right.trans le_sup_right
  have hD : Source.starImage H (one L T V₁) ≤ N := by
    have hXH : plus L T V₁ ≤ H := (show plus L T V₁ ≤ one L T V₁ by rw [hfactor]; exact le_sup_left).trans hDH
    rw [hfactor, star_sup H _ _ hXH (hzero.trans hKH)]
    exact sup_le hX ((star_le_of_le H hzero).trans hK)
  have hN : (⊤ : Subgroup (Source.Hstar H)) ≤ N := by
    have he : Source.starImage H H = ⊤ := by
      simp [Source.starImage, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rw [← he]
    conv_lhs => arg 2; rw [hgen]
    rw [star_sup H _ _ hKH (sup_le hDH hTH), star_sup H _ _ hDH hTH]
    exact sup_le hK (sup_le hD hT)
  intro h
  obtain ⟨g,hg⟩ := hN (mem_top h)
  refine ⟨e.symm g, ?_⟩
  intro x
  have he := congrArg (fun a : MulAut BinaryLinearThree.Group => a (e x)) hg
  rw [componentAction_apply] at he
  have hx := e.injective (show e (e.symm g * x * (e.symm g)⁻¹) = e (MulAut.conjNormal h x) by
    simpa only [map_mul, map_inv, e.apply_symm_apply, MulAut.conj_apply] using he)
  exact (congrArg Subtype.val hx).symm


variable [Finite G]

private theorem star_core_displacement (H A : Subgroup G) (hAH : A ≤ H)
    (t : normalizer (A : Set G)) (htH : t.val ∈ H) (ht : coreAction A t = 1) :
    ∀ a ∈ Source.starImage H A,
      QuotientGroup.mk' (pCore 2 H) ⟨t.val,htH⟩ * a *
        (QuotientGroup.mk' (pCore 2 H) ⟨t.val,htH⟩)⁻¹ * a⁻¹ ∈
          (Source.starImage H A).pCoreIn 2 := by
  rintro _ ⟨a,ha,rfl⟩
  have hc := (coreAction_eq_one_iff A t).mp ht ⟨a.val,ha⟩
  rw [← starImage_twoCore H A hAH]
  refine ⟨⟨t.val * a.val * t.val⁻¹ * a.val⁻¹,
    H.mul_mem (H.mul_mem (H.mul_mem htH a.property) (H.inv_mem htH)) (H.inv_mem a.property)⟩,
    ⟨A.normalizerMonoidHom t ⟨a.val,ha⟩ * (⟨a.val,ha⟩ : A)⁻¹,hc,rfl⟩, ?_⟩
  change QuotientGroup.mk' (pCore 2 H)
    ((⟨t.val,htH⟩ : H) * a * (⟨t.val,htH⟩ : H)⁻¹ * a⁻¹) = _
  simp only [map_mul, map_inv]

/-- An actor of two-power order fixing L₀/O₂(L₀) is implemented on K*
by the image of an actual element of O₂(L₀). -/
theorem source_core_implementer (H K L T : Subgroup G)
    [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (p : ParabolicPlacement H K L T eK)
    (hKH : K ≤ H) (hzero : zero L ≤ K)
    (t : normalizer (zero L : Set G)) (htH : t.val ∈ H)
    (ht : coreAction (zero L) t = 1) (htTwo : ∃ n : ℕ, t.val ^ (2 ^ n) = 1) :
    ∃ c : (zero L).pCoreIn 2, ∃ hcH : c.val ∈ H,
      ∀ x : Source.starImage H K,
        QuotientGroup.mk' (pCore 2 H) ⟨t.val,htH⟩ * x.val *
          (QuotientGroup.mk' (pCore 2 H) ⟨t.val,htH⟩)⁻¹ =
        QuotientGroup.mk' (pCore 2 H) ⟨c.val,hcH⟩ * x.val *
          (QuotientGroup.mk' (pCore 2 H) ⟨c.val,hcH⟩)⁻¹ := by
  let e := markedComponentEquiv H K L T eK p
  let ts : Source.Hstar H := QuotientGroup.mk' (pCore 2 H) ⟨t.val,htH⟩
  let A := (Source.starImage H (zero L)).subgroupOf (Source.starImage H K)
  have hZK : Source.starImage H (zero L) ≤ Source.starImage H K := star_le_of_le H hzero
  have hmark : A.map e.toMonoidHom = Matrix.PSL3Two.MarkedAutomorphisms.residual p.standard :=
    markedComponentEquiv_residual H K L T eK p
  have hstable : (A.map e.toMonoidHom).map (componentAction H K e ts).toMonoidHom = A.map e.toMonoidHom := by
    apply componentAction_stable
    apply star_normalizes_of_normalizes H
      (normalizer (zero L : Set G)) (zero L) le_rfl
    exact ⟨⟨t.val,htH⟩,t.property,rfl⟩
  have hdisp (a : BinaryLinearThree.Group) (ha : a ∈ A.map e.toMonoidHom) :
      componentAction H K e ts a * a⁻¹ ∈ (A.map e.toMonoidHom).pCoreIn 2 := by
    obtain ⟨x,hx,rfl⟩ := ha
    change componentAction H K e ts (e x) * (e x)⁻¹ ∈ _
    rw [componentAction_apply, ← map_inv, ← map_mul,
      ← map_pCoreIn_of_injective 2 A e.toMonoidHom e.injective]
    apply mem_map_of_mem
    have hh := star_core_displacement H (zero L) (hzero.trans hKH) t htH ht x.val hx
    have hm : (A.pCoreIn 2).map (Source.starImage H K).subtype =
        (Source.starImage H (zero L)).pCoreIn 2 := by
      rw [map_pCoreIn_of_injective 2 A _ (Source.starImage H K).subtype_injective,
        map_subgroupOf_eq_of_le hZK]
    rw [← hm] at hh
    exact (mem_map_iff_mem (Source.starImage H K).subtype_injective).mp hh
  have hpow : ∃ n : ℕ, componentAction H K e ts ^ (2 ^ n) = 1 := by
    obtain ⟨n,hn⟩ := htTwo
    have htn : ts ^ (2 ^ n) = 1 := by
      rw [← map_pow]
      have he : (⟨t.val,htH⟩ : H) ^ (2 ^ n) = 1 := Subtype.ext hn
      rw [he, map_one]
    exact ⟨n, by rw [← map_pow, htn, map_one]⟩
  rw [hmark] at hstable hdisp
  obtain ⟨g,hg,he⟩ := Matrix.PSL3Two.MarkedAutomorphisms.two_quotient_fixer_is_conj
    p.standard p.standard_eq (componentAction H K e ts) hstable hdisp hpow
  rw [← hmark, ← map_pCoreIn_of_injective 2 A e.toMonoidHom e.injective] at hg
  obtain ⟨k,hk,rfl⟩ := hg
  have hks : k.val ∈ Source.starImage H ((zero L).pCoreIn 2) := by
    rw [starImage_twoCore H (zero L) (hzero.trans hKH)]
    have hm := mem_map_of_mem (Source.starImage H K).subtype hk
    rw [map_pCoreIn_of_injective 2 A _ (Source.starImage H K).subtype_injective,
      map_subgroupOf_eq_of_le hZK] at hm
    exact hm
  obtain ⟨c,hc,hck⟩ := hks
  refine ⟨⟨c.val,hc⟩,c.property,?_⟩
  intro x
  have hh := congrArg (fun a : MulAut BinaryLinearThree.Group => a (e x)) he
  rw [componentAction_apply] at hh
  have hx := e.injective (show e (MulAut.conjNormal ts x) = e (k * x * k⁻¹) by
    change e (MulAut.conjNormal ts x) = e k * e x * (e k)⁻¹ at hh
    rw [map_mul, map_mul, map_inv]
    exact hh)
  have hv := congrArg Subtype.val hx
  change ts * x.val * ts⁻¹ = k.val * x.val * k.val⁻¹ at hv
  rw [← hck] at hv
  exact hv


omit [Finite G] in
/-- The correction lies in the original source Sylow subgroup, not merely
in a two-subgroup of the component. -/
theorem source_zero_core_le_T (L T V V₁ V₃ : Subgroup G)
    (d : LocalAction.NaturalSetup L T V V₁ V₃) : (zero L).pCoreIn 2 ≤ T := by
  have hz : (zero L).pCoreIn 2 ≤ (L ⊔ T).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes ((zero_le L).trans le_sup_left)
      (sup_le (L_normalizes_zero L)
        (d.normalizes_L.trans (normalizer_le_zero_normalizer L)))
  have hc := pCoreIn_le_sylow (L ⊔ T) d.sylow
  rw [d.sylow_eq, map_subgroupOf_eq_of_le le_sup_right] at hc
  exact hz.trans hc

/-- Correct the source inverter by an element of O₂(L₀). It remains in T∩L,
inverts the original intrinsic quotient, and now centralizes K* itself. -/
theorem source_centralizing_inverter (H K L T V V₁ V₃ : Subgroup G)
    (d : LocalAction.NaturalSetup L T V V₁ V₃)
    [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (p : ParabolicPlacement H K L T eK)
    (hKH : K ≤ H) (hDH : one L T V₁ ≤ H) (hTH : T ≤ H)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L) (hzero : zero L ≤ K)
    (hn : (Source.starImage H (plus L T V₁)).Normal)
    (hcentral : Source.starImage H K ≤
      centralizer (Source.starImage H (plus L T V₁) : Set (Source.Hstar H))) :
    ∃ s : (T ⊓ L : Subgroup G), ∃ hsH : s.val ∈ H,
      (∀ x : plus L T V₁ ⧸ pCore 2 (plus L T V₁), coreAction (plus L T V₁)
        ⟨s.val, T_normalizes_plus L T V₁ d.normalizes_L d.line_stable s.property.1⟩ x = x⁻¹) ∧
      coreAction (zero L) ⟨s.val, L_normalizes_zero L s.property.2⟩ = 1 ∧
      (∀ x : Source.starImage H K,
        QuotientGroup.mk' (pCore 2 H) ⟨s.val,hsH⟩ * x.val *
          (QuotientGroup.mk' (pCore 2 H) ⟨s.val,hsH⟩)⁻¹ = x.val) ∧
      (∀ x ∈ Source.starImage H (plus L T V₁),
        QuotientGroup.mk' (pCore 2 H) ⟨s.val,hsH⟩ * x *
          (QuotientGroup.mk' (pCore 2 H) ⟨s.val,hsH⟩)⁻¹ = x⁻¹) := by
  obtain ⟨t,ht,ht₀⟩ := d.exists_plus_inverter hfactor
  have hTtwo : IsPGroup 2 T := by
    have hh := d.sylow.isPGroup'.map (L ⊔ T : Subgroup G).subtype
    rwa [d.sylow_eq, map_subgroupOf_eq_of_le le_sup_right] at hh
  obtain ⟨n,hnpow⟩ := hTtwo.exists_pow_pow_eq_one ⟨t.val,t.property.1⟩
  have htH : t.val ∈ H := hTH t.property.1
  obtain ⟨c,hcH,hc⟩ := source_core_implementer H K L T eK p hKH hzero
    ⟨t.val,L_normalizes_zero L t.property.2⟩ htH ht₀
    ⟨n,congrArg Subtype.val hnpow⟩
  have hcT : c.val ∈ T := source_zero_core_le_T L T V V₁ V₃ d c.property
  have hcZ : c.val ∈ zero L := pCoreIn_le 2 (zero L) c.property
  have hcL : c.val ∈ L := zero_le L hcZ
  let s : (T ⊓ L : Subgroup G) := ⟨t.val * c.val⁻¹,
    T.mul_mem t.property.1 (T.inv_mem hcT), L.mul_mem t.property.2 (L.inv_mem hcL)⟩
  have hsH : s.val ∈ H := hTH s.property.1
  have hsInv : ∀ x : plus L T V₁ ⧸ pCore 2 (plus L T V₁), coreAction (plus L T V₁)
      ⟨s.val,T_normalizes_plus L T V₁ d.normalizes_L d.line_stable s.property.1⟩ x = x⁻¹ := by
    exact zero_core_inversion_preserved H K L T V₁ hKH hDH d.line_stable hzero hn hcentral
      ⟨t.val,T_normalizes_plus L T V₁ d.normalizes_L d.line_stable t.property.1⟩
      ⟨c.val⁻¹,zero_core_normalizes_plus L T V₁ hfactor ((zero L).pCoreIn 2 |>.inv_mem c.property)⟩
      ((zero L).pCoreIn 2 |>.inv_mem c.property) ht
  refine ⟨s,hsH,hsInv,L_centralizes_zero_quotient L ⟨s.val,s.property.2⟩,?_,?_⟩
  · intro x
    let cs : Source.starImage H K := ⟨QuotientGroup.mk' (pCore 2 H) ⟨c.val,hcH⟩,
      ⟨⟨c.val,hcH⟩,hzero hcZ,rfl⟩⟩
    have hh := hc (cs⁻¹ * x * cs)
    calc
      QuotientGroup.mk' (pCore 2 H) ⟨s.val,hsH⟩ * x.val *
          (QuotientGroup.mk' (pCore 2 H) ⟨s.val,hsH⟩)⁻¹ =
        QuotientGroup.mk' (pCore 2 H) ⟨t.val,htH⟩ * (cs⁻¹ * x * cs).val *
          (QuotientGroup.mk' (pCore 2 H) ⟨t.val,htH⟩)⁻¹ := by
            change QuotientGroup.mk' (pCore 2 H) ((⟨t.val,htH⟩ : H) * (⟨c.val,hcH⟩ : H)⁻¹) *
                x.val * (QuotientGroup.mk' (pCore 2 H) ((⟨t.val,htH⟩ : H) * (⟨c.val,hcH⟩ : H)⁻¹))⁻¹ = _
            simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
            dsimp only [cs]
            group
      _ = cs.val * (cs⁻¹ * x * cs).val * cs.val⁻¹ := hh
      _ = x.val := by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  · exact normal_star_inversion H _ ((plus_le_one L T V₁ d.line_stable).trans hDH) hn
      ⟨s.val,T_normalizes_plus L T V₁ d.normalizes_L d.line_stable s.property.1⟩ hsH hsInv

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
