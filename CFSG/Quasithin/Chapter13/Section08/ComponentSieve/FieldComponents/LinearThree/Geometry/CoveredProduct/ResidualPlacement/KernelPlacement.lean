module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.ComponentAction

/-!
# Locating L₀ by the marked cubic kernel

A surjection from L₁ to a cubic group kills O₂(L₁). Its kernel in the
actual elementary-nine quotient has order three. If the kernel is T-stable
and does not contain X, the local marked-line theorem identifies it with
the L₀ mark. Applying this to H* → H*/K* places L₀* in K*. Two-perfectness
then lifts that inclusion to L₀ ≤ K through the normal two-kernel.

The only comparison with a cubic quotient occurs inside L₁/O₂(L₁).
The subgroup L₀* itself, with its possible surviving two-core, is retained.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.21(1), printed p.957, with Notation 13.2.1 and 13.2.2(3).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
open LocalAction

theorem zero_in_cubic_kernel (L T V V₁ V₃ : Subgroup G)
    (d : NaturalSetup L T V V₁ V₃)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    {E : Type*} [Group E] (hE : Nat.card E = 3)
    (f : one L T V₁ →* E) (hf : Function.Surjective f)
    (hstable : ∀ s : T, ∀ a : one L T V₁, f a = 1 →
      f ((one L T V₁).normalizerMonoidHom
        ⟨s.val, T_normalizes_one L T V₁ d.line_stable s.property⟩ a) = 1)
    (hX : ¬ plus L T V₁ ≤ f.ker.map (one L T V₁).subtype) :
    zero L ≤ f.ker.map (one L T V₁).subtype := by
  have hthree : IsPGroup 3 E := IsPGroup.of_card (n := 1) hE
  have hcore : pCore 2 (one L T V₁) ≤ f.ker := by
    apply (Subgroup.map_eq_bot_iff _).mp
    exact disjoint_self.mp (IsPGroup.disjoint_of_ne 2 3 (by decide) _ _
      (pCore_isPGroup.map f) (hthree.to_subgroup _))
  let fbar := QuotientGroup.lift (pCore 2 (one L T V₁)) f hcore
  have hsur : Function.Surjective fbar := QuotientGroup.lift_surjective_of_surjective _ f hf hcore
  have hcard : Nat.card fbar.ker = 3 := by
    have he := card_eq_card_quotient_mul_card_subgroup fbar.ker
    rw [d.one_quotient_card hfactor,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective fbar hsur).toEquiv, hE] at he
    omega
  have hs : ∀ s : T, ∀ q ∈ fbar.ker,
      coreAction (one L T V₁)
        ⟨s.val, T_normalizes_one L T V₁ d.line_stable s.property⟩ q ∈ fbar.ker := by
    intro s q hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (one L T V₁)) q
    rw [coreAction_mk]
    exact hstable s a hq
  rcases d.invariant_marked_line hfactor fbar.ker hcard hs with hzero | hplus
  · intro z hz
    have he : zeroCoreMap L T V₁ d.normalizes_L hfactor
        (QuotientGroup.mk' (pCore 2 (zero L)) ⟨z, hz⟩) ∈ fbar.ker := by
      rw [hzero]
      exact ⟨_, rfl⟩
    change fbar (localCoreMap _ _ _ _ _) = 1 at he
    rw [localCoreMap_mk] at he
    exact ⟨inclusion (zero_le_one_of_factorization L T V₁ hfactor) ⟨z, hz⟩, he, rfl⟩
  · apply (hX ?_).elim
    intro x hx
    have he : plusCoreMap L T V₁ d.line_stable
        (QuotientGroup.mk' (pCore 2 (plus L T V₁)) ⟨x, hx⟩) ∈ fbar.ker := by
      rw [hplus]
      exact ⟨_, rfl⟩
    change fbar (localCoreMap _ _ _ _ _) = 1 at he
    rw [localCoreMap_mk] at he
    exact ⟨inclusion (plus_le_one L T V₁ d.line_stable) ⟨x, hx⟩, he, rfl⟩

omit [Finite G] in
private theorem disjoint_of_centerless_centralizing (K X : Subgroup G)
    (hz : center K = ⊥) (hc : K ≤ centralizer (X : Set G)) : Disjoint K X := by
  apply disjoint_iff_inf_le.mpr
  intro x hx
  have hxZ : (⟨x, hx.1⟩ : K) ∈ center K := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext ((hc k.property x hx.2).symm)
  rw [hz, mem_bot] at hxZ
  exact congrArg (fun k : K => (k : G)) hxZ

/-- The two T-invariant marked lines locate the other residual in the actual
component. No intrinsic cubic quotient is substituted for its star image. -/
theorem zero_le_component (H K L T V V₁ V₃ : Subgroup G)
    (d : NaturalSetup L T V V₁ V₃)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    [(K.subgroupOf H).Normal]
    (hKH : K ≤ H) (hDH : one L T V₁ ≤ H) (hTH : T ≤ H)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (hc : Nat.card (Source.starImage H (plus L T V₁)) = 3)
    (hDKX : Source.starImage H (one L T V₁) ≤
      Source.starImage H K ⊔ Source.starImage H (plus L T V₁))
    (hcentral : Source.starImage H K ≤
      centralizer (Source.starImage H (plus L T V₁) : Set (Source.Hstar H))) :
    zero L ≤ K := by
  let D := one L T V₁
  let X := plus L T V₁
  let Ks := Source.starImage H K
  let Xs := Source.starImage H X
  let : Ks.Normal := (inferInstance : (K.subgroupOf H).Normal).map _
    (QuotientGroup.mk'_surjective _)
  let q := QuotientGroup.mk' Ks
  let E := Xs.map q
  have hdis : Disjoint Ks Xs :=
    disjoint_of_centerless_centralizing Ks Xs (star_component_centerless H K eK) hcentral
  have hinj : Function.Injective (q.subgroupMap Xs) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_bot_iff.mp
    intro x hx
    have hxq : q x.val = 1 := congrArg Subtype.val hx
    have hxK : x.val ∈ Ks := (QuotientGroup.eq_one_iff _).mp hxq
    exact Subtype.ext (disjoint_def.mp hdis hxK x.property)
  have hE : Nat.card E = 3 :=
    (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap Xs)
      ⟨hinj, q.subgroupMap_surjective Xs⟩).toEquiv).symm.trans hc
  have hmap : (Source.starImage H D).map q ≤ E := by
    have he := map_mono (f := q) hDKX
    simpa only [q, Ks, Xs, E, D, X, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] using he
  let f₀ : D →* (Source.Hstar H ⧸ Ks) := q.comp
    ((Source.starImage H D).subtype.comp (starMap H D hDH))
  let f : D →* E := f₀.codRestrict E
    (fun a => hmap (mem_map_of_mem q (starMap H D hDH a).property))
  have hf : Function.Surjective f := by
    rintro ⟨_, x, hx, rfl⟩
    obtain ⟨xH, hxH, rfl⟩ := hx
    exact ⟨⟨xH.val, plus_le_one L T V₁ d.line_stable hxH⟩, Subtype.ext rfl⟩
  have hs : ∀ s : T, ∀ a : D, f a = 1 →
      f (D.normalizerMonoidHom
        ⟨s.val, T_normalizes_one L T V₁ d.line_stable s.property⟩ a) = 1 := by
    intro s a ha
    have haq : q (QuotientGroup.mk' (pCore 2 H) (inclusion hDH a)) = 1 :=
      congrArg Subtype.val ha
    have haK : QuotientGroup.mk' (pCore 2 H) (inclusion hDH a) ∈ Ks :=
      (QuotientGroup.eq_one_iff _).mp haq
    apply Subtype.ext
    apply (QuotientGroup.eq_one_iff _).mpr
    change QuotientGroup.mk' (pCore 2 H)
      ((⟨s.val, hTH s.property⟩ : H) * inclusion hDH a * (⟨s.val, hTH s.property⟩ : H)⁻¹) ∈ Ks
    rw [map_mul, map_mul, map_inv]
    exact (inferInstance : Ks.Normal).conj_mem _ haK _
  have hX : ¬ X ≤ f.ker.map D.subtype := by
    intro hX
    have hXK : Xs ≤ Ks := by
      rintro _ ⟨xH, hx, rfl⟩
      obtain ⟨a, ha, he⟩ := hX hx
      have haq : q (QuotientGroup.mk' (pCore 2 H) (inclusion hDH a)) = 1 :=
        congrArg Subtype.val (show f a = 1 from ha)
      have he' : inclusion hDH a = xH := Subtype.ext he
      rw [he'] at haq
      exact (QuotientGroup.eq_one_iff _).mp haq
    have hbot : Xs = ⊥ := le_bot_iff.mp ((le_inf hXK le_rfl).trans hdis.le_bot)
    have hh : Nat.card Xs = 1 := by rw [hbot, card_bot]
    change Nat.card Xs = 3 at hc
    omega
  have hz := zero_in_cubic_kernel L T V V₁ V₃ d hfactor hE f hf hs hX
  apply le_of_star_le H K (zero L) hKH
    ((zero_le_one_of_factorization L T V₁ hfactor).trans hDH) (residual_isPPerfect _)
  rintro _ ⟨zH, hzH, rfl⟩
  obtain ⟨a, ha, he⟩ := hz hzH
  have haq : q (QuotientGroup.mk' (pCore 2 H) (inclusion hDH a)) = 1 :=
    congrArg Subtype.val (show f a = 1 from ha)
  have he' : inclusion hDH a = zH := Subtype.ext he
  rw [he'] at haq
  exact (QuotientGroup.eq_one_iff _).mp haq

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
