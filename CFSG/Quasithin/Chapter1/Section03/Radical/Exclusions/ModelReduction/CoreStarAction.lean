module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.Quotients
public import Theory.GroupTheory.GeneralizedFitting.InnerAutomorphisms

/-!
# Conjugation through the actual core-to-star map

The comparison from K/O₂(K) to K* respects the normalizer action literally
on quotient representatives. If F* of the star actor is K*, an actor whose
core automorphism is inner belongs to K* after passage to the star quotient.
The latter follows by reflecting the inner action through the surjective
comparison and using self-centralization of the generalized Fitting subgroup.

These are the action transfers used in the exceptional central-cover rows
of Aschbacher–Smith C.2.7 and original15.3.17–21, pp.145–147,1126–1127.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
variable {G : Type*} [Group G] {K R : Subgroup G}

/-- Literal normalizer equivariance of the comparison, as an ambient equality. -/
theorem coreToStar_normalizer_action
    (hR : R ≤ normalizer (K : Set G))
    (r : normalizer (K : Set G)) (hr : (r : G) ∈ K ⊔ R)
    (x : K ⧸ pCore 2 K) :
    (coreToStar hR (quotientAut (pCore 2 K) (K.normalizerMonoidHom r) x) :
        StarQuotient K R) =
      QuotientGroup.mk' (starKernel K R) ⟨(r : G),hr⟩ *
        (coreToStar hR x : StarQuotient K R) *
        (QuotientGroup.mk' (starKernel K R) ⟨(r : G),hr⟩)⁻¹ := by
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) x
  rw [quotientAut_apply_mk,coreToStar_mk,coreToStar_mk]
  change QuotientGroup.mk' (starKernel K R) ⟨_,_⟩ =
    QuotientGroup.mk' (starKernel K R) ⟨_,_⟩ *
      QuotientGroup.mk' (starKernel K R) ⟨_,_⟩ *
        (QuotientGroup.mk' (starKernel K R) ⟨_,_⟩)⁻¹
  rw [←map_inv,←map_mul,←map_mul]
  congr 1

/-- Innerness on the actual core quotient forces star membership when K*=F*. -/
theorem star_mem_of_core_action_inner [Finite G]
    (hR : R ≤ normalizer (K : Set G))
    (hfit : generalizedFitting (StarQuotient K R) = starImage K R K)
    (r : normalizer (K : Set G)) (hr : (r : G) ∈ K ⊔ R)
    (hi : ∃ k : K ⧸ pCore 2 K,
      quotientAut (pCore 2 K) (K.normalizerMonoidHom r) = MulAut.conj k) :
    QuotientGroup.mk' (starKernel K R) ⟨(r : G),hr⟩ ∈ starImage K R K := by
  let q := QuotientGroup.mk' (starKernel K R)
  let rs : StarQuotient K R := q ⟨(r : G),hr⟩
  let C := starImage K R K
  change generalizedFitting (StarQuotient K R) = C at hfit
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hR)
  let : C.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hequiv (x : K ⧸ pCore 2 K) :
      coreToStar hR (quotientAut (pCore 2 K) (K.normalizerMonoidHom r) x) =
        (MulAut.conjNormal rs : MulAut C) (coreToStar hR x) := by
    apply Subtype.ext
    exact coreToStar_normalizer_action hR r hr x
  obtain ⟨k,hk⟩ := hi
  have hinner : (MulAut.conjNormal rs : MulAut C) = MulAut.conj (coreToStar hR k) := by
    ext x
    obtain ⟨y,rfl⟩ := coreToStar_surjective hR x
    rw [←hequiv,hk,MulAut.conj_apply,map_mul,map_mul,map_inv,MulAut.conj_apply]
  have hm : rs ∈ (MulAut.innerSubgroup C).comap MulAut.conjNormal :=
    ⟨coreToStar hR k,hinner.symm⟩
  rw [MulAut.conjNormal_comap_innerSubgroup] at hm
  have hC : centralizer (C : Set (StarQuotient K R)) ≤ C :=
    hfit ▸ centralizer_generalizedFitting_le (StarQuotient K R)
  exact (sup_le le_rfl hC) hm
end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
