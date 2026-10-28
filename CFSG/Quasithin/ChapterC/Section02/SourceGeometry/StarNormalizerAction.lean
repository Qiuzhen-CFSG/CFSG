module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.LocalClauses
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
/-!
# Normalizer actions on the literal C.2.7 star module

An element normalizing K and R acts on KR and its characteristic elementary
omega-center V. It descends to KR/C_KR(V), preserves the actual image K*,
and intertwines the binary action on V. The component automorphism retains
the original surjection from K and its conjugation formula.

Source: Aschbacher–Smith C.2.7 and15.3.20, pp.145–147,1127–1128.
-/
public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
variable {G : Type*} [Group G] (K R : Subgroup G)

noncomputable def starNormalizerAut (a : G)
    (hK : a ∈ normalizer (K : Set G)) (hR : a ∈ normalizer (R : Set G)) :
    MulAut (StarQuotient K R) :=
  quotientAut (starKernel K R) ((K ⊔ R).normalizerMonoidHom
    ⟨a,normalizer_inf_normalizer_le_normalizer_sup K R ⟨hK,hR⟩⟩)

noncomputable def starVectorAut (a : G)
    (hK : a ∈ normalizer (K : Set G)) (hR : a ∈ normalizer (R : Set G)) :
    Additive (starV K R) ≃ₗ[ZMod 2] Additive (starV K R) :=
  let b := MulAut.characteristic (starV K R) ((K ⊔ R).normalizerMonoidHom
    ⟨a,normalizer_inf_normalizer_le_normalizer_sup K R ⟨hK,hR⟩⟩)
  b.toAdditive.toLinearEquiv (ZMod.map_smul _)

theorem starVectorAut_apply (a : G) (hK) (hR) (v : Additive (starV K R)) :
    (((starVectorAut K R a hK hR v).toMul : (K ⊔ R : Subgroup G)) : G) =
      a * ((v.toMul : (K ⊔ R : Subgroup G)) : G) * a⁻¹ := by rfl

theorem starNormalizerAut_mk (a : G) (hK) (hR) (g : (K ⊔ R : Subgroup G)) :
    starNormalizerAut K R a hK hR (QuotientGroup.mk' (starKernel K R) g) =
      QuotientGroup.mk' (starKernel K R) ((K ⊔ R).normalizerMonoidHom
        ⟨a,normalizer_inf_normalizer_le_normalizer_sup K R ⟨hK,hR⟩⟩ g) :=
  quotientAut_apply_mk _ _ _

theorem starNormalizerAut_intertwines (a : G) (hK) (hR)
    (g : StarQuotient K R) (v : Additive (starV K R)) :
    starVectorAut K R a hK hR (starRepresentation K R g v) =
      starRepresentation K R (starNormalizerAut K R a hK hR g)
        (starVectorAut K R a hK hR v) := by
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (starKernel K R) g
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  rw [starNormalizerAut_mk,starVectorAut_apply]
  have he := congrArg Subtype.val (starRepresentation_apply K R g v)
  change (((starRepresentation K R (QuotientGroup.mk' (starKernel K R) g) v).toMul :
    (K ⊔ R : Subgroup G)) : G) = (g : G) * (v.toMul : (K ⊔ R : Subgroup G)) * (g : G)⁻¹ at he
  rw [he]
  rw [starRepresentation_apply]
  change a * ((g : G) * (v.toMul : (K ⊔ R : Subgroup G)) * (g : G)⁻¹) * a⁻¹ =
    (a * (g : G) * a⁻¹) *
      (((starVectorAut K R a hK hR v).toMul : (K ⊔ R : Subgroup G)) : G) *
      (a * (g : G) * a⁻¹)⁻¹
  rw [starVectorAut_apply]
  group

theorem starNormalizerAut_toStarImage (a : G) (hK) (hR) (k : K) :
    starNormalizerAut K R a hK hR (toStarImage K R k : StarQuotient K R) =
      (toStarImage K R (K.normalizerMonoidHom ⟨a,hK⟩ k) : StarQuotient K R) := by
  change starNormalizerAut K R a hK hR (QuotientGroup.mk' (starKernel K R)
    (⟨k,mem_sup_left k.property⟩ : (K ⊔ R : Subgroup G))) = _
  rw [starNormalizerAut_mk]
  rfl

theorem starNormalizerAut_component (a : G) (hK) (hR) :
    (starImage K R K).map (starNormalizerAut K R a hK hR).toMonoidHom =
      starImage K R K := by
  ext x
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨k,hk⟩ := toStarImage_surjective K R ⟨x,hx⟩
    have he := congrArg Subtype.val hk
    change (toStarImage K R k : StarQuotient K R) = x at he
    change starNormalizerAut K R a hK hR x ∈ _
    rw [←he,starNormalizerAut_toStarImage]
    exact (toStarImage K R _).property
  · intro hx
    obtain ⟨k,hk⟩ := toStarImage_surjective K R ⟨x,hx⟩
    have he : (toStarImage K R k : StarQuotient K R) = x := congrArg Subtype.val hk
    rw [←he]
    let j := (K.normalizerMonoidHom ⟨a,hK⟩).symm k
    refine ⟨toStarImage K R j,(toStarImage K R j).property,?_⟩
    change starNormalizerAut K R a hK hR (toStarImage K R j : StarQuotient K R) = _
    rw [starNormalizerAut_toStarImage]
    change (toStarImage K R ((K.normalizerMonoidHom ⟨a,hK⟩)
      ((K.normalizerMonoidHom ⟨a,hK⟩).symm k)) : StarQuotient K R) = _
    rw [MulEquiv.apply_symm_apply]

noncomputable def starComponentAut (a : G)
    (hK : a ∈ normalizer (K : Set G)) (hR : a ∈ normalizer (R : Set G)) : MulAut (starImage K R K) :=
  ((starNormalizerAut K R a hK hR).subgroupMap (starImage K R K)).trans
    (MulEquiv.subgroupCongr (starNormalizerAut_component K R a hK hR))

theorem starComponentAut_coe (a : G) (hK) (hR) (x : starImage K R K) :
    (starComponentAut K R a hK hR x : StarQuotient K R) =
      starNormalizerAut K R a hK hR x := by rfl

theorem starComponentAut_toStarImage (a : G) (hK) (hR) (k : K) :
    starComponentAut K R a hK hR (toStarImage K R k) =
      toStarImage K R (K.normalizerMonoidHom ⟨a,hK⟩ k) := by
  apply Subtype.ext
  rw [starComponentAut_coe,starNormalizerAut_toStarImage]

end CFSG.Quasithin.ChapterC.C27Source
