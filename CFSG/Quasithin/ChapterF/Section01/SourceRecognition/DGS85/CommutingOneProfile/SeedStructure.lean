module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.LocalSubgroups
public import Theory.GroupTheory.ElementaryPairCommutator
public import Theory.ElementaryAbelian.Quotient
public import Theory.ElementaryAbelian.Injective

/-!
# The Chapter 11 two-seed group and elementary alpha quotient

The two elementary seeds E = Zα ∩ Qβ and F = Zα₂ ∩ Qβ are normalized
by Qβ when it normalizes their original centers. Their join V has derived
and Frattini subgroups equal to [E,F], central in V and contained in E ∩ F.
The (11.3)(h) core-generation identity and (11.4) core product imply the
literal elementary quotient S/Qα used in (11.5).

The source graph and rank-one arguments establishing those two generation
identities remain explicit. In particular this is not the elementary branch
hypothesis of (11.7), which instead concerns S/Qβ.
Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.1)(c), (11.3) and (11.5), printed pp.167--172.
-/

public section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
variable {G : Type*} [Group G]

private theorem seed_normalizes (Q Z : Subgroup G)
    (hn : Q ≤ normalizer (Z : Set G)) :
    Q ≤ normalizer ((Z ⊓ Q : Subgroup G) : Set G) :=
  (le_inf hn Q.le_normalizer).trans inf_normalizer_le_normalizer_inf

/-- The quadratic commutator of (11.1)(c) from normality of the original
central layer and elementary abelianness. -/
theorem core_center_quadratic (Q Z : Subgroup G) [IsElementaryAbelian 2 Z]
    (hn : Q ≤ normalizer (Z : Set G)) : ⁅⁅Q,Z⁆,Z⁆ = ⊥ := by
  apply bot_unique
  exact (commutator_mono (le_normalizer_iff_commutator_le_right.mp hn) le_rfl).trans
    (commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative Z)).le

/-- Both commutator and Frattini layers of V are literal subgroups of Qβ.
No ambient normality of either original center is asserted. -/
theorem pairSpan_commutator_frattini
    (Zα Zα₂ Qβ : Subgroup G) [Finite Qβ]
    [IsElementaryAbelian 2 Zα] [IsElementaryAbelian 2 Zα₂]
    (hQ : IsPGroup 2 Qβ)
    (hα : Qβ ≤ normalizer (Zα : Set G))
    (hα₂ : Qβ ≤ normalizer (Zα₂ : Set G)) :
    ⁅pairSpan Zα Zα₂ Qβ, pairSpan Zα Zα₂ Qβ⁆ =
        ⁅Zα ⊓ Qβ, Zα₂ ⊓ Qβ⁆ ∧
      (frattini (pairSpan Zα Zα₂ Qβ)).map (pairSpan Zα Zα₂ Qβ).subtype =
        ⁅Zα ⊓ Qβ, Zα₂ ⊓ Qβ⁆ ∧
      ⁅pairSpan Zα Zα₂ Qβ, pairSpan Zα Zα₂ Qβ⁆ ≤ Zα ⊓ Zα₂ ∧
      ⁅⁅pairSpan Zα Zα₂ Qβ, pairSpan Zα Zα₂ Qβ⁆, pairSpan Zα Zα₂ Qβ⁆ = ⊥ := by
  let E := Zα ⊓ Qβ
  let F := Zα₂ ⊓ Qβ
  let : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.of_injective (inclusion inf_le_left) (inclusion_injective _)
  let : IsElementaryAbelian 2 F :=
    IsElementaryAbelian.of_injective (inclusion inf_le_left) (inclusion_injective _)
  let : Finite E := Finite.of_injective (inclusion (show E ≤ Qβ from inf_le_right))
    (inclusion_injective _)
  let : Finite (E ⊔ F : Subgroup G) :=
    Finite.of_injective (inclusion (pairSpan_le_core Zα Zα₂ Qβ)) (inclusion_injective _)
  have hEF : E ≤ normalizer (F : Set G) := inf_le_right.trans (seed_normalizes _ _ hα₂)
  have hFE : F ≤ normalizer (E : Set G) := inf_le_right.trans (seed_normalizes _ _ hα)
  have hp : IsPGroup 2 (E ⊔ F : Subgroup G) := hQ.to_le (pairSpan_le_core Zα Zα₂ Qβ)
  exact ⟨commutator_join_of_abelian E F,
    frattini_sup_eq_cross_of_elementary_normalizes E F hp hFE,
    (commutator_sup_le_inf_of_abelian_normalizes E F hEF hFE).trans
      (inf_le_inf inf_le_left inf_le_left),
    commutator_sup_central_of_abelian_normalizes E F hEF hFE⟩

/-- The elementary supplement in (11.5), before any rank-one model identification. -/
theorem alpha_supplement_of_pair_generation (Qα Qβ Zα Zα₂ S : Subgroup G)
    (hS : S = Qα ⊔ Qβ)
    (hQβ : Qβ = pairSpan Zα Zα₂ Qβ ⊔ (Qα ⊓ Qβ))
    (hZα : Zα ≤ Qα) : S = Qα ⊔ (Zα₂ ⊓ Qβ) := by
  rw [hS]
  apply le_antisymm
  · apply sup_le le_sup_left
    apply hQβ.le.trans
    change ((Zα ⊓ Qβ) ⊔ (Zα₂ ⊓ Qβ)) ⊔ (Qα ⊓ Qβ) ≤ Qα ⊔ (Zα₂ ⊓ Qβ)
    exact sup_le (sup_le ((inf_le_left.trans hZα).trans le_sup_left) le_sup_right)
      (inf_le_left.trans le_sup_left)
  · exact sup_le le_sup_left (inf_le_right.trans le_sup_right)

/-- The literal quotient in the sentence preceding (11.5) is elementary.
The two-core product and (11.3)(h) remain earlier source inputs. -/
theorem alpha_quotient_elementary_of_pair_generation
    (Qα Qβ Zα Zα₂ S : Subgroup G) [IsElementaryAbelian 2 Zα₂]
    [(Qα.subgroupOf S).Normal]
    (hS : S = Qα ⊔ Qβ)
    (hQβ : Qβ = pairSpan Zα Zα₂ Qβ ⊔ (Qα ⊓ Qβ))
    (hZα : Zα ≤ Qα) : IsElementaryAbelian 2 (S ⧸ Qα.subgroupOf S) := by
  have hgen := alpha_supplement_of_pair_generation Qα Qβ Zα Zα₂ S hS hQβ hZα
  let E := Zα₂ ⊓ Qβ
  let : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hQS : Qα ≤ S := hS ▸ le_sup_left
  have hES : E ≤ S := hgen ▸ le_sup_right
  let f : E →* (S ⧸ Qα.subgroupOf S) :=
    (QuotientGroup.mk' (Qα.subgroupOf S)).comp (inclusion hES)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨s,rfl⟩ := QuotientGroup.mk'_surjective (Qα.subgroupOf S) x
    have hn : E ≤ normalizer (Qα : Set G) :=
      hES.trans ((normal_subgroupOf_iff_le_normalizer hQS).mp inferInstance)
    have hs : s.val ∈ (Qα : Set G) * (E : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left Qα E hn, ← hgen]
      exact s.property
    obtain ⟨q,hq,e,he,hqe⟩ := hs
    refine ⟨⟨e,he⟩,?_⟩
    have hse : s = (⟨q,hQS hq⟩ : S) * ⟨e,hES he⟩ := Subtype.ext hqe.symm
    rw [hse,map_mul]
    have hq1 : QuotientGroup.mk' (Qα.subgroupOf S) (⟨q,hQS hq⟩ : S) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hq
    rw [hq1,one_mul]
    rfl
  exact IsElementaryAbelian.of_surjective f hf

/-- Once (11.7) has identified the alpha core with its central layer,
(11.3)(h) identifies the whole beta core with the two actual seeds. -/
theorem beta_core_eq_pairSpan_of_alpha_core_eq
    (Qα Qβ Zα Zα₂ : Subgroup G)
    (hQβ : Qβ = pairSpan Zα Zα₂ Qβ ⊔ (Qα ⊓ Qβ))
    (hQα : Qα = Zα) : Qβ = pairSpan Zα Zα₂ Qβ := by
  exact hQβ.trans (sup_eq_left.mpr (hQα ▸ le_sup_left))


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
