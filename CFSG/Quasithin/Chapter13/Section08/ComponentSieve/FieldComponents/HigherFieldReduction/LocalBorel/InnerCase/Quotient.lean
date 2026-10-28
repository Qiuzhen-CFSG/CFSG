module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.Actors
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Fitting
public import Theory.GroupTheory.PResidual.InnerInverter
public import Theory.GroupTheory.PResidual.NormalityLift
public import Theory.GroupAction.InnerSylow

/-!
# Correcting an inner prescribed actor and lifting normality

The actual Sylow image in Inn(K*) contains every inner actor induced by T*.
Thus the original t* can be corrected by s in T*∩K*, retaining the complete
centralizer kernel. If X* normalizes that Sylow, mutual normalization in
its two-group preimage makes s act trivially on X/O₂(X). Inversion by t
then forces X* into C_H*(K*), using two-perfectness of X.

Generation H=KL₁T gives normality of X*. The kernel O₂(H) lies in T and
normalizes X, so the two-perfect normality-lifting theorem gives X normal
in H. Only then is O₂(X) killed in H*, and the corrected element inverts
all of X*. A cubic core quotient excludes X≤K.

The Sylow-normalization premise is an explicit interface for the Borel
calculation. No externality, centralization or normality conclusion is
assumed here. Source: Aschbacher–Smith 13.8.20, printed p.954/PDF p.971.
-/

public section

open Subgroup Theory.GroupAction.ModelConjugation
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.InnerCase
open Components.Fitting
variable {G : Type*} [Group G] [Finite G]

/-- Correct the prescribed actor by an actual element of the component Sylow. -/
theorem inner_correction (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hT : Chapter1.IsSylowIn 2 T H) (t : H) (ht : t.val ∈ T)
    (hi : markedActor H K T t ht ∈ MulAut.innerSubgroup (Source.starImage H K)) :
    ∃ s ∈ Source.starImage H T ⊓ Source.starImage H K,
      s⁻¹ * QuotientGroup.mk' (pCore 2 H) t ∈ Source.starImage H T ⊓
        centralizer (Source.starImage H K : Set (Source.Hstar H)) := by
  have hm := MulAut.mem_innerSylow_of_mem_inner (sourceSylow H K T hT)
    (starActor H K T).range (starActor_twoGroup H K T hT)
    (starActor_innerSylow H K T hT)
    (show markedActor H K T t ht ∈ (starActor H K T).range from ⟨_, rfl⟩) hi
  have hST : (sourceSylow H K T hT : Subgroup (Source.starImage H K)).map
      ((Source.starImage H K).subtype.comp (MulEquiv.refl _).symm.toMonoidHom) ≤
        Source.starImage H T := by
    change (sourceSylow H K T hT : Subgroup (Source.starImage H K)).map
      (Source.starImage H K).subtype ≤ _
    rw [sourceSylow_image]
    exact inf_le_left
  have hh := (action_mem_inner_iff (Source.starImage H T) (Source.starImage H K)
    le_normalizer_of_normal (MulEquiv.refl _) (sourceSylow H K T hT) hST
    ⟨QuotientGroup.mk' (pCore 2 H) t, ⟨t, ht, rfl⟩⟩).mp hm
  change QuotientGroup.mk' (pCore 2 H) t ∈
    (sourceSylow H K T hT : Subgroup (Source.starImage H K)).map
      (Source.starImage H K).subtype ⊔ _ at hh
  rw [sourceSylow_image] at hh
  have hh' : QuotientGroup.mk' (pCore 2 H) t ∈
      (Source.starImage H T ⊓ Source.starImage H K) ⊔
        centralizer (Source.starImage H K : Set (Source.Hstar H)) :=
    (show _ ≤ (Source.starImage H T ⊓ Source.starImage H K) ⊔
      centralizer (Source.starImage H K : Set (Source.Hstar H)) from
        sup_le_sup le_rfl inf_le_right) hh
  obtain ⟨s, hs, c, hc, he⟩ := mem_sup_of_normal_right.mp hh'
  refine ⟨s, hs, (Source.starImage H T).mul_mem
    ((Source.starImage H T).inv_mem hs.1) ⟨t, ht, rfl⟩, ?_⟩
  rwa [← he, inv_mul_cancel_left]

omit [Finite G] in
private theorem restrict_normalizes (H X A : Subgroup G) (hXH : X ≤ H)
    (hn : A ≤ normalizer (X : Set G)) :
    A.subgroupOf H ≤ normalizer (X.subgroupOf H : Set H) := by
  rw [← subgroupOf_normalizer_eq hXH]
  exact subgroupOf_mono H hn

omit [Finite G] in
private theorem image_normalizes (H X A : Subgroup G) (hXH : X ≤ H)
    (hn : A ≤ normalizer (X : Set G)) :
    Source.starImage H A ≤ normalizer (Source.starImage H X : Set (Source.Hstar H)) :=
  (map_mono (restrict_normalizes H X A hXH hn)).trans (le_normalizer_map _)

/-- The complete external-X conclusion from Sylow normalization, with the
normality lift and the centralizing inverter both constructed. -/
theorem external_of_normalizes_sylow (H K L₁ T X : Subgroup G)
    (hKH : K ≤ H) (hLH : L₁ ≤ H) (hX : X ≤ L₁)
    (hgen : H = K ⊔ (L₁ ⊔ T)) (hT : Chapter1.IsSylowIn 2 T H)
    (hKn : (K.subgroupOf H).Normal)
    (hXperfect : IsPPerfect 2 X)
    (hXnorm : L₁ ⊔ T ≤ normalizer (X : Set G))
    (hcard : Nat.card (X ⧸ pCore 2 X) = 3)
    (hXS : Source.starImage H X ≤ normalizer
      ((Source.starImage H T ⊓ Source.starImage H K : Subgroup (Source.Hstar H)) : Set _))
    (t : H) (ht : t.val ∈ T)
    (hinv : ∀ x ∈ X, t.val * x * t.val⁻¹ * x ∈ X.pCoreIn 2)
    (hi : let := hKn; let : (Source.starImage H K).Normal :=
      Subgroup.Normal.map hKn _ (QuotientGroup.mk'_surjective _)
      markedActor H K T t ht ∈ MulAut.innerSubgroup (Source.starImage H K)) :
    ExternalXAlternative H K X := by
  let := hKn
  let : (Source.starImage H K).Normal :=
    Subgroup.Normal.map hKn _ (QuotientGroup.mk'_surjective _)
  let q := QuotientGroup.mk' (pCore 2 H)
  let A := X.subgroupOf H
  let R := (Source.starImage H T ⊓ Source.starImage H K).comap q
  let C := centralizer (Source.starImage H K : Set (Source.Hstar H))
  have hXH : X ≤ H := hX.trans hLH
  have hTH : T ≤ H := by rw [hgen]; exact le_sup_right.trans le_sup_right
  have hTN := restrict_normalizes H X T hXH (le_sup_right.trans hXnorm)
  obtain ⟨P, hP⟩ := hT
  have hPH : T.subgroupOf H = (P : Subgroup H) := by
    rw [← hP]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  have hkerT : q.ker ≤ T.subgroupOf H := by
    rw [QuotientGroup.ker_mk', hPH]
    exact pCore_isPGroup.le_sylow_of_normal P
  have hRT : R ≤ T.subgroupOf H := by
    have hh := comap_mono (f := q) (inf_le_left :
      Source.starImage H T ⊓ Source.starImage H K ≤ Source.starImage H T)
    change R ≤ ((T.subgroupOf H).map q).comap q at hh
    simpa only [comap_map_eq, sup_of_le_left hkerT] using hh
  have hR : IsPGroup 2 R := (hPH ▸ P.isPGroup').to_le hRT
  have hAR : A ≤ normalizer (R : Set H) := by
    apply le_normalizer_iff.mpr
    intro a ha r hr
    change q (a * r * a⁻¹) ∈ Source.starImage H T ⊓ Source.starImage H K
    simpa only [map_mul, map_inv] using
      le_normalizer_iff.mp hXS (q a) (mem_map_of_mem q ha) (q r) hr
  obtain ⟨s, hs, hc⟩ := inner_correction H K T ⟨P, hP⟩ t ht hi
  have hc := hc.2
  obtain ⟨sH, hsH⟩ := QuotientGroup.mk'_surjective (pCore 2 H) s
  change q sH = s at hsH
  change s⁻¹ * q t ∈ C at hc
  have hAperfect : IsPPerfect 2 A := hXperfect.of_surjective
    (subgroupOfEquivOfLe hXH).symm.toMonoidHom (subgroupOfEquivOfLe hXH).symm.surjective
  have hAC : A ≤ C.comap q := by
    apply le_normal_of_inversion_mod_twoCore A R (C.comap q) hAperfect hR hAR
      (hRT.trans hTN) t sH
    · change q sH ∈ Source.starImage H T ⊓ Source.starImage H K
      rwa [hsH]
    · change q (sH⁻¹ * t) ∈ C
      simpa only [map_mul, map_inv, hsH] using hc
    · intro x hx
      have he : (A.pCoreIn 2).map H.subtype = X.pCoreIn 2 := by
        rw [map_pCoreIn_of_injective 2 A H.subtype H.subtype_injective,
          map_subgroupOf_eq_of_le hXH]
      apply (mem_map_iff_mem H.subtype_injective).mp
      rw [he]
      exact hinv x.val hx
  have hXC : Source.starImage H X ≤ C := map_le_iff_le_comap.mpr hAC
  have hnstar : (Source.starImage H X).Normal := by
    have hnorm : (⊤ : Subgroup (Source.Hstar H)) ≤
        normalizer (Source.starImage H X : Set (Source.Hstar H)) := by
      have htop : Source.starImage H K ⊔ Source.starImage H (L₁ ⊔ T) = ⊤ := by
        rw [Source.starImage, Source.starImage, ← Subgroup.map_sup,
          ← subgroupOf_sup hKH (sup_le hLH hTH), ← hgen, subgroupOf_self,
          map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
      rw [← htop]
      exact sup_le ((le_centralizer_iff.mp hXC).trans (Subgroup.centralizer_le_normalizer _))
        (image_normalizes H X (L₁ ⊔ T) hXH hXnorm)
    exact normalizer_eq_top_iff.mp (top_unique hnorm)
  let : (A.map q).Normal := hnstar
  have hnA : A.Normal := normal_of_map_normal_of_pPerfect q A hAperfect
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) (hkerT.trans hTN)
  have hkill : ∀ z ∈ X.pCoreIn 2, ∀ hzH : z ∈ H, q ⟨z, hzH⟩ = 1 := by
    intro z hz hzH
    have he : (A.pCoreIn 2).map H.subtype = X.pCoreIn 2 := by
      rw [map_pCoreIn_of_injective 2 A H.subtype H.subtype_injective,
        map_subgroupOf_eq_of_le hXH]
    have hzA : (⟨z, hzH⟩ : H) ∈ A.pCoreIn 2 :=
      (mem_map_iff_mem H.subtype_injective).mp (he ▸ hz)
    exact (QuotientGroup.eq_one_iff _).mpr
      ((pCoreIn_le_of_subnormal 2 hnA.isSubnormal) hzA)
  have htinv : ∀ x ∈ Source.starImage H X, q t * x * (q t)⁻¹ = x⁻¹ := by
    rintro _ ⟨x, hx, rfl⟩
    have hh := hkill _ (hinv x.val hx) (H.mul_mem (H.mul_mem
      (H.mul_mem t.property x.property) (H.inv_mem t.property)) x.property)
    change q (t * x * t⁻¹ * x) = 1 at hh
    rw [map_mul, map_mul, map_mul, map_inv] at hh
    exact mul_eq_one_iff_eq_inv.mp hh
  have hcinv : ∀ x ∈ Source.starImage H X, (s⁻¹ * q t) * x * (s⁻¹ * q t)⁻¹ = x⁻¹ := by
    intro x hx
    have hcomm : s * x = x * s := (hXC hx) s hs.2
    calc
      _ = s⁻¹ * (q t * x * (q t)⁻¹) * s := by group
      _ = s⁻¹ * x⁻¹ * s := by rw [htinv x hx]
      _ = x⁻¹ := by
        have hh : s⁻¹ * x⁻¹ = x⁻¹ * s⁻¹ := (Commute.inv_left hcomm).inv_right
        rw [hh, mul_assoc, inv_mul_cancel, mul_one]
  refine ⟨hXH, ?_, hXC, hnA, s⁻¹ * q t, hc, hcinv⟩
  intro hXK
  have hcardstar : Nat.card (Source.starImage H X) = 3 :=
    (Nat.card_congr (subnormalStarEquiv H X hXH hnA.isSubnormal).toEquiv).symm.trans hcard
  have hp : IsPGroup 2 (Source.starImage H X) := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    have hxc := hc x.val ((map_mono (subgroupOf_mono H hXK)) x.property)
    have hin := hcinv x.val x.property
    have he : x.val = x.val⁻¹ := by
      rw [← hxc, mul_inv_cancel_right] at hin
      exact hin
    change x.val ^ (2 ^ 1) = 1
    rw [pow_one, pow_two]
    calc
      x.val * x.val = x.val * x.val⁻¹ := congrArg (x.val * ·) he
      _ = 1 := mul_inv_cancel _
  obtain ⟨n, hn⟩ := hp.exists_card_dvd_pow
  rw [hcardstar] at hn
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hn)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.InnerCase
