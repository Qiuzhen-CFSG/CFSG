module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCritical
public import Theory.Representation.SmallBinaryPrimeNormalizer.CubicInvolutions
public import Theory.GroupTheory.PGroup.OmegaAmbient

/-!
# Involution control in the single quintic factor branch

A singleton canonical five-factor is normal. The actual point cubic acts
without fixed vectors on the original U_I/V₁, so the support calculation
forces every square-one star actor to centralize it. The full star image
of R₁ is the centralizer of that cubic in the Sylow image. Its inverse
image is exactly R₁: O₂(I) already lies in O₂(L₁T). Thus Ω₁(T) lies in R₁,
with the original ambient Sylow and quotient maps unchanged.

Source: Aschbacher–Smith, 14.7.5(3), 14.7.6, printed pp.1044–1045,
refs/quasithin.pdf. The ambient source application is in
LargePrimeSingleFactorSource.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter12.Section08 CriticalFusion.Source ChapterD
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

/-- The single canonical five-factor is normal, so every square-one star
actor centralizes the original point cubic. -/
theorem local_single_five_square_one_centralizes
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hLI : F.Li L 1 ≤ I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1)) :
    let := BinaryGroupAction.action a.representation
    ∀ (_i : smallSupportFactors (HStar I)
        (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2),
      Nat.card (smallSupportFactors (HStar I)
        (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 1 →
      ∀ t : HStar I, t ^ 2 = 1 →
        t ∈ centralizer (actorImage I (F.Li L 1) : Set (HStar I)) := by
  intro _ i hone t ht
  let W := Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I))
  let := BinaryGroupAction.action a.representation
  let : IsElementaryAbelian 2 (Multiplicative W) := BinaryGroupAction.elementary
  let : FaithfulSMul (HStar I) (Multiplicative W) :=
    BinaryGroupAction.faithful a.representation a.faithful
  let : Subsingleton (smallSupportFactors (HStar I) (Multiplicative W) 2) :=
    (Nat.card_eq_one_iff_unique.mp hone).1
  let : i.val.Normal := normalizer_eq_top_iff.mp (top_unique (by
    intro g _
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact congrArg Subtype.val (Subsingleton.elim (smallSupportFactors_conjEquiv 2 g i) i)))
  let B := actorImage I (F.Li L 1)
  let : B.Normal := Normal.map hn _ (QuotientGroup.mk'_surjective _)
  have hB : Nat.card B = 3 := local_point_star_card_of_normal h structural I hLI hn
  have hfixed : FixedPoints.subgroup B (Multiplicative W) = ⊥ := by
    rw [BinaryGroupAction.fixedPoints_eq]
    change BinaryGroupAction.submoduleEquivSubgroup
      (fixedSpace a.representation (((F.Li L 1).subgroupOf I).map
        (QuotientGroup.mk' (pCore 2 I)))) = ⊥
    rw [local_point_fixedSpace_eq_bot h structural I hLI hn a]
    exact BinaryGroupAction.submoduleEquivSubgroup.map_bot
  exact _root_.SmallBinaryPrimeNormalizer.square_one_centralizes_cubic_on_five_support
    (V := Multiplicative W) i.val B i.property.2.1 hB i.property.2.2 hfixed t ht

/-- Centralization of the actual point image by a subgroup of T places it
in R₁. Both two-cores and the full original quotient map are retained. -/
theorem local_sylow_le_point_core_of_star_centralizes
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hBI : F.Li L 1 ⊔ (T : Subgroup G) ≤ I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (E : Subgroup G) (hET : E ≤ T)
    (hc : actorImage I E ≤ centralizer (actorImage I (F.Li L 1) : Set (HStar I))) :
    E ≤ F.Ri L 1 := by
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 I)
  let P := actorImage I (F.Li L 1)
  let : P.Normal := Normal.map hn _ (QuotientGroup.mk'_surjective _)
  have hP : IsPGroup 3 P := IsPGroup.of_card (n := 1)
    (by change Nat.card P = 3
        exact local_point_star_card_of_normal h structural I (le_sup_left.trans hBI) hn)
  let S : Sylow 2 I := T.subtype (le_sup_right.trans hBI)
  let S' : Sylow 2 (HStar I) := S.mapSurjective (QuotientGroup.mk'_surjective _)
  have hgen : actorImage I B = P ⊔ (S' : Subgroup (HStar I)) := by
    change (B.subgroupOf I).map q = _
    rw [subgroupOf_sup (le_sup_left.trans hBI) (le_sup_right.trans hBI),Subgroup.map_sup]
    rfl
  have hcore : actorImage I (F.Ri L 1) = (actorImage I B).pCoreIn 2 := by
    have he : (B.subgroupOf I).pCoreIn 2 = (B.pCoreIn 2).subgroupOf I := by
      apply map_injective I.subtype_injective
      rw [map_pCoreIn_of_injective 2 _ _ I.subtype_injective,map_subgroupOf_eq_of_le hBI,
        map_subgroupOf_eq_of_le ((pCoreIn_le 2 B).trans hBI)]
    change ((B.pCoreIn 2).subgroupOf I).map q = _
    rw [←he,map_pCoreIn_of_ker_isPGroup q (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)]
    rfl
  have hm : actorImage I E ≤ actorImage I (F.Ri L 1) := by
    rw [hcore,hgen,core_join_odd_eq_sylow_centralizer P hP S']
    exact le_inf (map_mono (comap_mono hET)) hc
  have hQI : I.pCoreIn 2 ≤ T := by
    have hh := pCoreIn_le_sylow I S
    simpa only [S,Sylow.coe_subtype,map_subgroupOf_eq_of_le (le_sup_right.trans hBI)] using hh
  have hQB : I.pCoreIn 2 ≤ B.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 I) (hQI.trans le_sup_right)
    (hBI.trans (I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))))
  intro e he
  have heI : e ∈ I := (hET.trans (le_sup_right.trans hBI)) he
  have heimage := hm (mem_map_of_mem q (show (⟨e,heI⟩ : I) ∈ E.subgroupOf I from he))
  obtain ⟨r,hr,heq⟩ := heimage
  have hdiff : (r : G)⁻¹ * e ∈ B.pCoreIn 2 := hQB (mem_map.mpr
    ⟨r⁻¹ * ⟨e,heI⟩,(QuotientGroup.eq_one_iff _).mp (by
      change q (r⁻¹ * ⟨e,heI⟩) = 1
      rw [map_mul,map_inv,heq,inv_mul_cancel]),rfl⟩)
  change e ∈ B.pCoreIn 2
  have hh := (B.pCoreIn 2).mul_mem hr hdiff
  change (r : G) * ((r : G)⁻¹ * e) ∈ B.pCoreIn 2 at hh
  simpa only [mul_inv_cancel_left] using hh

/-- The original involution-generated Sylow subgroup lies in R₁ in the
singleton canonical-factor branch. -/
theorem local_single_five_omega_le_point_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hBI : F.Li L 1 ⊔ (T : Subgroup G) ≤ I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1)) :
    let := BinaryGroupAction.action a.representation
    ∀ (_i : smallSupportFactors (HStar I)
        (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2),
      Nat.card (smallSupportFactors (HStar I)
        (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) = 1 →
      omegaOneAmbient (T : Subgroup G) ≤ F.Ri L 1 := by
  intro _ i hone
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro t ht ht2
  have hzt : zpowers t ≤ T := zpowers_le.mpr ht
  have htI : t ∈ I := (le_sup_right.trans hBI) ht
  apply local_sylow_le_point_core_of_star_centralizes h structural I hBI hn (zpowers t) hzt
    (by
      have hm : actorImage I (zpowers t) = zpowers (QuotientGroup.mk' (pCore 2 I) ⟨t,htI⟩) := by
        rw [actorImage,show (zpowers t).subgroupOf I = zpowers (⟨t,htI⟩ : I) from
          (map_injective I.subtype_injective (by rw [map_subgroupOf_eq_of_le (hzt.trans (le_sup_right.trans hBI)),MonoidHom.map_zpowers]; rfl)),
          MonoidHom.map_zpowers]
      rw [hm]
      exact zpowers_le.mpr (local_single_five_square_one_centralizes h structural I
        (le_sup_left.trans hBI) hn a i hone _ (by
          rw [←map_pow]
          have he : (⟨t,htI⟩ : I) ^ 2 = 1 := Subtype.ext ht2
          rw [he,map_one])))
  exact mem_zpowers t

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
