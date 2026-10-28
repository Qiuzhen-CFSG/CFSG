module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.SourceAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OvergroupLift
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.ResidualDirections
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Basic
public import Theory.GroupTheory.PResidual.NormalizerImage

/-!
# Local algebra for the covered source parabolics

We retain the literal central-preimage residual L₀, the relative
normalizer residual L₁, and the commutator residual L₁,+ from 13.2.1.
The cubic center of the genuine triple cover gives the first residual's
cubic quotient. The earlier factorization and second cubic order then
give the order-nine quotient of L₁. Its factor of nine survives passage
to H*, ruling out a component PSL₃(2).

The actual Sylow subgroup puts O₂(H) inside T. Thus it normalizes L₀,
and the normalizer lifting theorem applies to L₀*. After the overlap
calculation, the one-sided source bound N_G(L₀) ≤ M suffices to give the
required starred normalizer inequality. No equality N_G(L₀) = M is used.

Source: Aschbacher–Smith, Notation 13.2.1, 13.2.2(3),(9), and 13.8.25,
printed pp.877–878 and 959–960, combined manuscript of 1 March 2004.
The common flag coordinates and exact overlap still require geometric
identification; the last two lemmas are explicit tools for that assembly.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
variable {G : Type*} [Group G] [Finite G]

/-- The central quotient order in Notation 13.2.1 follows from the genuine
triple-cover hypothesis, without choosing a different covering model. -/
theorem zero_quotient_card (L : Subgroup G)
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L)) :
    Nat.card (zero L ⧸ pCore 2 (zero L)) = 3 := by
  have hc := hcover.2.1
  have hpre : Source.starImage L (centralPreimage L) = center (L ⧸ pCore 2 L) := by
    unfold Source.starImage centralPreimage
    rw [← comap_subtype, comap_map_eq_self_of_injective L.subtype_injective,
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hr : residual (center (L ⧸ pCore 2 L)) = center (L ⧸ pCore 2 L) := by
    apply le_antisymm (residual_le _)
    intro x hx
    refine ⟨⟨x, hx⟩, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
    exact (by decide : Nat.Coprime 2 3).of_dvd_right
      (hc ▸ orderOf_dvd_natCard (⟨x, hx⟩ : center (L ⧸ pCore 2 L)))
  have hs : Source.starImage L (zero L) = center (L ⧸ pCore 2 L) := by
    rw [zero, star_residual L (centralPreimage L) (map_subtype_le _), hpre, hr]
  have hn : (Source.starImage L (zero L)).Normal := by rw [hs]; infer_instance
  exact (Nat.card_congr (normalStarEquiv L (zero L) (zero_le L) hn).toEquiv).trans
    (by rwa [hs])

/-- The marked order-nine quotient cannot lose its factor of nine in H*.
The comparison identifies both intrinsic two-core quotients. -/
theorem nine_dvd_star_one (H L T V₁ : Subgroup G) (hLH : one L T V₁ ≤ H)
    (hTL : T ≤ normalizer (L : Set G)) (hTV : T ≤ normalizer (V₁ : Set G))
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hplus : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3) :
    9 ∣ Nat.card (Source.starImage H (one L T V₁)) := by
  have hc := one_quotient_card L T V₁ hTL hTV hfactor (zero_quotient_card L hcover) hplus
  have he := Nat.card_congr (starCoreQuotientEquiv H (one L T V₁) hLH).toEquiv
  have hc' : Nat.card (Source.starImage H (one L T V₁) ⧸
      pCore 2 (Source.starImage H (one L T V₁))) = 9 := he.symm.trans hc
  rw [← hc']
  exact card_dvd_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)

/-- In the cover case PSL₃(2) is excluded by the actual order-nine
source quotient, independently of any proposed flag placement. -/
theorem exclude_three (H K L T V₁ : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hLK : one L T V₁ ≤ K)
    (hTL : T ≤ normalizer (L : Set G)) (hTV : T ≤ normalizer (V₁ : Set G))
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hplus : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3)
    (e : (K ⧸ pCore 2 K) ≃* PSL 3) : False := by
  have h9 := (nine_dvd_star_one H L T V₁ (hLK.trans hKH) hTL hTV hcover hfactor hplus).trans
    (card_dvd_of_le (map_mono (subgroupOf_mono H hLK)))
  have hc : Nat.card (Source.starImage H K) = 168 :=
    (Nat.card_congr (starLinearEquiv H K hKH hK e).toEquiv).trans Matrix.PSL3Two.card_PSL
  change 9 ∣ Nat.card (Source.starImage H K) at h9
  rw [hc] at h9
  exact (by decide : ¬ 9 ∣ 168) h9

omit [Finite G] in
/-- The kernel containment uses the actual Sylow subgroup of H. -/
theorem twoCore_le_T (H T : Subgroup G) (hTH : T ≤ H)
    (S : Sylow 2 H) (hS : (S : Subgroup H) = T.subgroupOf H) : Source.QH H ≤ T := by
  have h := pCoreIn_le_sylow H S
  rwa [hS, map_subgroupOf_eq_of_le hTH] at h

omit [Finite G] in
/-- Relative normalization passes to the literal quotient images. -/
theorem star_normalizes (H A B : Subgroup G) (hn : A ≤ normalizer (B : Set G)) :
    Source.starImage H A ≤ normalizer (Source.starImage H B : Set (Source.Hstar H)) :=
  (map_mono ((comap_mono hn).trans (B.le_normalizer_comap H.subtype))).trans
    ((B.subgroupOf H).le_normalizer_map (QuotientGroup.mk' (pCore 2 H)))

omit [Finite G] in
/-- The target normalizer is the image of the actual relative normalizer.
The two-perfectness and kernel-normalization hypotheses are essential. -/
theorem star_normalizer (H A : Subgroup G) (hAH : A ≤ H) (hp : IsPPerfect 2 A)
    (hQ : Source.QH H ≤ normalizer (A : Set G)) :
    normalizer (Source.starImage H A : Set (Source.Hstar H)) =
      Source.starImage H (normalizer (A : Set G)) := by
  have hp' : IsPPerfect 2 (A.subgroupOf H) :=
    hp.of_surjective (subgroupOfEquivOfLe hAH).symm.toMonoidHom
      (subgroupOfEquivOfLe hAH).symm.surjective
  have hk : IsPGroup 2 (QuotientGroup.mk' (pCore 2 H)).ker := by
    rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hn : (QuotientGroup.mk' (pCore 2 H)).ker ≤ normalizer (A.subgroupOf H : Set H) := by
    rw [QuotientGroup.ker_mk', ← subgroupOf_normalizer_eq hAH]
    intro q hq
    exact hQ (mem_map_of_mem H.subtype hq)
  rw [Source.starImage, ← map_normalizer_of_pPerfect _ (QuotientGroup.mk'_surjective _)
    (A.subgroupOf H) hp' hk hn, ← subgroupOf_normalizer_eq hAH]
  rfl

omit [Finite G] in
/-- Once the geometric normalizer bound is proved, relative normality of
L₁ in H∩M yields equality of the original subgroups, including O₂(H). -/
theorem overlap_eq_of_star_normalizer (H M L₁ T : Subgroup G)
    (hLH : L₁ ≤ H) (hLM : L₁ ≤ M) (hTH : T ≤ H) (hTM : T ≤ M)
    (S : Sylow 2 H) (hS : (S : Subgroup H) = T.subgroupOf H)
    (hn : (L₁.subgroupOf (H ⊓ M)).Normal)
    (hbound : normalizer (Source.starImage H L₁ : Set (Source.Hstar H)) ≤
      Source.starImage H (L₁ ⊔ T)) : H ⊓ M = L₁ ⊔ T := by
  have hnorm : H ⊓ M ≤ normalizer (L₁ : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (le_inf hLH hLM)).mp hn
  have hs := (star_normalizes H (H ⊓ M) L₁ hnorm).trans hbound
  have hle := (le_liftStar_iff H (H ⊓ M) inf_le_left _).mpr hs
  rw [liftStar_starImage_of_core_le H (L₁ ⊔ T) (sup_le hLH hTH)
    ((twoCore_le_T H T hTH S hS).trans le_sup_right)] at hle
  exact le_antisymm hle (sup_le (le_inf hLH hLM) (le_inf hTH hTM))

/-- The source's one-sided 13.2.2(9) bound gives the starred normalizer
chain after the exact overlap is known. Kernel lifting is proved here. -/
theorem zero_star_normalizer_le_plus (H M L T V₁ : Subgroup G)
    (hLH : one L T V₁ ≤ H) (hTH : T ≤ H)
    (hTL : T ≤ normalizer (L : Set G)) (hTV : T ≤ normalizer (V₁ : Set G))
    (S : Sylow 2 H) (hS : (S : Subgroup H) = T.subgroupOf H)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hNM : normalizer (zero L : Set G) ≤ M)
    (hinter : H ⊓ M = one L T V₁ ⊔ T) :
    normalizer (Source.starImage H (zero L) : Set (Source.Hstar H)) ≤
      normalizer (Source.starImage H (plus L T V₁) : Set (Source.Hstar H)) := by
  have hzeroH := (zero_le_one_of_factorization L T V₁ hfactor).trans hLH
  have hTzero := hTL.trans (normalizer_le_zero_normalizer L)
  rw [star_normalizer H (zero L) hzeroH (residual_isPPerfect _)
    ((twoCore_le_T H T hTH S hS).trans hTzero)]
  have hnorm : H ⊓ M ≤ normalizer (plus L T V₁ : Set G) := by
    rw [hinter]
    exact sup_le (one_normalizes_plus L T V₁) (T_normalizes_plus L T V₁ hTL hTV)
  have hlocal : (normalizer (zero L : Set G)).subgroupOf H ≤
      (H ⊓ M).subgroupOf H := fun x hx => ⟨x.property, hNM hx⟩
  exact (map_mono hlocal).trans (star_normalizes H (H ⊓ M) _ hnorm)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource
end
