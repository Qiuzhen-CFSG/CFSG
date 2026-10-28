module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.Quotient
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SourceBorel
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.KernelPlacement

/-!
# Locating the covered central residual in the Borel

Theta puts every cubic element of BX into L₁. Its rank forces the image of
L₁ ∩ BX to fill the order-nine quotient of L₁. Normality and two-perfectness
remove the two-core supplement, giving L₁ ≤ BX. In the literal star quotient,
the direct product B* X* has a cubic projection. The earlier classification
of T-invariant marked lines identifies its kernel on L₁ with the L₀ mark.
Thus L₀* ≤ B*. The lift retains O₂(H), which lies in T and normalizes B;
two-perfectness of both residuals then gives L₀ ≤ B.

The generic marked-line result imported from the binary-L₃ development has
no binary-L₃ hypothesis. None of that development's component-placement or
component-automorphism conclusions is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.20(a), printed p.954/PDF p.971; local marks from 13.2.1–2, p.877.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.MarkedBorel
open Components.Swapped.LinearTwo
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]

private theorem rank_le_one_of_card_le_three {E : Type*} [Group E] [Finite E]
    (hc : Nat.card E ≤ 3) : primeRank 3 E ≤ 1 := by
  apply (primeRank_le_iff_elementary_card_le E).mpr
  intro A _
  exact (Subgroup.card_le_card_group A).trans (by simpa using hc)

private theorem eq_top_of_rank_gt_one_card_nine {E : Type*} [Group E] [Finite E]
    (hc : Nat.card E = 9) (A : Subgroup E) (hr : 1 < primeRank 3 A) : A = ⊤ := by
  have hd : Nat.card A ∣ 3 ^ 2 := by simpa [hc] using A.card_subgroup_dvd_card
  obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
  interval_cases k
  · have hh := rank_le_one_of_card_le_three (E := A) (by omega)
    omega
  · have hh := rank_le_one_of_card_le_three (E := A) (by omega)
    omega
  · apply eq_of_le_of_card_ge le_top
    simp [he, hc]

theorem marked_le_of_theta_rank (H M D J : Subgroup G)
    (htheta : D = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (hJH : J ≤ H) (hJM : J ≤ M) (hn : D ≤ normalizer (J : Set G))
    (hp : IsPPerfect 2 D) (hc : Nat.card (D ⧸ pCore 2 D) = 9)
    (hr : 1 < primeRank 3 J) : D ≤ J := by
  let A := J.subgroupOf D
  have hnorm : A.Normal := normal_subgroupOf_of_le_normalizer hn
  let q := QuotientGroup.mk' (pCore 2 D)
  let f := q.subgroupMap A
  have hrA : 1 < primeRank 3 A := by
    have hl : primeRank 3 J ≤ primeRank 3 (J ⊓ D : Subgroup G) :=
      threeRank_le_of_contains_threes _ _ (by
        intro x hx ho
        refine ⟨hx, ?_⟩
        rw [htheta]
        exact subset_closure ⟨⟨hJH hx,hJM hx⟩,ho⟩)
    let e : A ≃* (J ⊓ D : Subgroup G) :=
      { toFun x := ⟨x.val.val, x.property, x.val.property⟩
        invFun x := ⟨⟨x.val,x.property.2⟩,x.property.1⟩
        left_inv _ := rfl
        right_inv _ := rfl
        map_mul' _ _ := rfl }
    have he := primeRank_congr 3 e
    omega
  have hk : IsPGroup 2 f.ker := by
    let i : f.ker →* pCore 2 D :=
      { toFun x := ⟨x.val.val, (QuotientGroup.eq_one_iff _).mp
          (congrArg Subtype.val (show f x.val = 1 from x.property))⟩
        map_one' := rfl
        map_mul' _ _ := rfl }
    have hi : Function.Injective i := by
      intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun a : pCore 2 D => a.val) h))
    exact pCore_isPGroup.of_injective i hi
  have hk0 : primeRank 3 f.ker = 0 := by
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    obtain ⟨k,hk⟩ := hk.exists_card_eq
    rw [hk]
    exact fun h => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  have hu := primeRank_le_ker_add (p := 3) f
  rw [hk0, zero_add] at hu
  have him : A.map q = ⊤ := eq_top_of_rank_gt_one_card_nine hc _ (hrA.trans_le hu)
  have hsup : A ⊔ pCore 2 D = ⊤ := by
    have he := congrArg (fun U => U.comap q) him
    simpa only [comap_map_eq, comap_top, q, QuotientGroup.ker_mk'] using he
  let g := (QuotientGroup.mk' A).comp (pCore 2 D).subtype
  have hg : Function.Surjective g := by
    apply MonoidHom.range_eq_top.mp
    have he := congrArg (fun U => U.map (QuotientGroup.mk' A)) hsup
    simpa only [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _), g,
      MonoidHom.range_comp, range_subtype] using he
  have hAtop : A = ⊤ := hp A hnorm (pCore_isPGroup.of_surjective g hg)
  intro d hd
  exact show (⟨d,hd⟩ : D) ∈ A from hAtop.symm ▸ mem_top _

theorem zero_le_borel_of_marked_join (H K B L T V V₁ V₃ : Subgroup G)
    (d : LocalAction.NaturalSetup L T V V₁ V₃)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hKH : K ≤ H) (hBK : B ≤ K) (hDH : one L T V₁ ≤ H) (hTH : T ≤ H)
    (hT : Chapter1.IsSylowIn 2 T H)
    (hnB : T ≤ normalizer (B : Set G)) (hpB : IsPPerfect 2 B)
    (hjoin : one L T V₁ ≤ B ⊔ plus L T V₁)
    (hc : Nat.card (Source.starImage H (plus L T V₁)) = 3)
    (hne : ¬ Source.starImage H (plus L T V₁) ≤ Source.starImage H K)
    (hcent : Source.starImage H (plus L T V₁) ≤
      centralizer (Source.starImage H K : Set (Source.Hstar H))) :
    zero L ≤ B := by
  let D := one L T V₁
  let X := plus L T V₁
  let Bs := Source.starImage H B
  let Xs := Source.starImage H X
  let J := Bs ⊔ Xs
  change Nat.card Xs = 3 at hc
  have hXH : X ≤ H := (plus_le_one L T V₁ d.line_stable).trans hDH
  have hBsK : Bs ≤ Source.starImage H K := map_mono (subgroupOf_mono H hBK)
  have hdis : Disjoint Xs Bs := by
    have hdvd : Nat.card (Xs ⊓ Bs : Subgroup (Source.Hstar H)) ∣ 3 := by
      rw [← hc]
      exact card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact disjoint_iff.mpr (card_eq_one.mp h1)
    · have he : Xs ⊓ Bs = Xs := eq_of_le_of_card_ge inf_le_left (by omega)
      exact (hne (he.symm.le.trans (inf_le_right.trans hBsK))).elim
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting Bs Xs hdis.symm
    (le_centralizer_iff.mp (hcent.trans (centralizer_le hBsK)))
  have hDJ : Source.starImage H D ≤ J := by
    have hm := map_mono (f := QuotientGroup.mk' (pCore 2 H)) (subgroupOf_mono H hjoin)
    rwa [subgroupOf_sup (hBK.trans hKH) hXH, Subgroup.map_sup] at hm
  let s : D →* J := (starHom H D hDH).codRestrict J (fun a => hDJ ⟨inclusion hDH a,a.property,rfl⟩)
  let f : D →* Xs := (MonoidHom.snd Bs Xs).comp (e.symm.toMonoidHom.comp s)
  have hfker (a : D) : f a = 1 ↔ starHom H D hDH a ∈ Bs := by
    change (e.symm (s a)).2 = 1 ↔ (s a).val ∈ Bs
    constructor
    · intro hx
      have he' := he (e.symm (s a)).1 (e.symm (s a)).2
      rw [e.apply_symm_apply, hx, OneMemClass.coe_one, mul_one] at he'
      exact he'.symm ▸ (e.symm (s a)).1.property
    · intro ha
      have he' : e (⟨(s a).val,ha⟩,1) = s a := by
        apply Subtype.ext
        simpa using he ⟨(s a).val,ha⟩ 1
      rw [← he', e.symm_apply_apply]
  have hf : Function.Surjective f := by
    rintro ⟨x, xH, hx, rfl⟩
    let a : D := ⟨xH.val, plus_le_one L T V₁ d.line_stable hx⟩
    have he' : s a = e (1,⟨QuotientGroup.mk' (pCore 2 H) xH,⟨xH,hx,rfl⟩⟩) := by
      apply Subtype.ext
      have haH : inclusion hDH a = xH := Subtype.ext rfl
      change QuotientGroup.mk' (pCore 2 H) (inclusion hDH a) = _
      rw [haH]
      simpa using (he 1
        ⟨QuotientGroup.mk' (pCore 2 H) xH,⟨xH,hx,rfl⟩⟩).symm
    refine ⟨a, ?_⟩
    change (e.symm (s a)).2 = _
    rw [he', e.symm_apply_apply]
  have hstable : ∀ t : T, ∀ a : D, f a = 1 →
      f (D.normalizerMonoidHom
        ⟨t.val,T_normalizes_one L T V₁ d.line_stable t.property⟩ a) = 1 := by
    intro t a ha
    apply (hfker _).mpr
    obtain ⟨b,hb,hba⟩ := (hfker a).mp ha
    refine ⟨(⟨t.val,hTH t.property⟩ : H) * b * (⟨t.val,hTH t.property⟩ : H)⁻¹,
      le_normalizer_iff.mp hnB t.val t.property b.val hb, ?_⟩
    change _ = QuotientGroup.mk' (pCore 2 H)
      ((⟨t.val,hTH t.property⟩ : H) * inclusion hDH a * (⟨t.val,hTH t.property⟩ : H)⁻¹)
    simp only [map_mul,map_inv]
    rw [hba]
    rfl
  have hX : ¬ X ≤ f.ker.map D.subtype := by
    intro hx
    apply hne
    rintro _ ⟨xH,hxH,rfl⟩
    obtain ⟨a,ha,hea⟩ := hx hxH
    have hb := (hfker a).mp ha
    have he' : inclusion hDH a = xH := Subtype.ext hea
    change QuotientGroup.mk' (pCore 2 H) (inclusion hDH a) ∈ Bs at hb
    rw [he'] at hb
    exact hBsK hb
  have hz := zero_in_cubic_kernel L T V V₁ V₃ d hfactor hc f hf hstable hX
  have hzB : Source.starImage H (zero L) ≤ Bs := by
    rintro _ ⟨zH,hzH,rfl⟩
    obtain ⟨a,ha,hea⟩ := hz hzH
    have hb := (hfker a).mp ha
    have he' : inclusion hDH a = zH := Subtype.ext hea
    change QuotientGroup.mk' (pCore 2 H) (inclusion hDH a) ∈ Bs at hb
    rwa [he'] at hb
  have hQT : Source.QH H ≤ T := by
    obtain ⟨P,hP⟩ := hT
    rw [← hP]
    exact map_mono (pCore_isPGroup.le_sylow_of_normal P)
  exact Structure.le_of_star_le_of_kernel_normalizes H B (zero L) (hBK.trans hKH)
    ((LocalAction.zero_le_one_of_factorization L T V₁ hfactor).trans hDH)
    hpB (residual_isPPerfect _) (hQT.trans hnB) hzB
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.MarkedBorel

end
