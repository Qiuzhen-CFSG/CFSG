module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.CoverModels.Preparation

/-!
# Canonical actor comparisons and the inducing diagram element

After the center calculation, the actual projection from the actor component
is an isomorphism. The same map carries M∩K to the source Borel and
intertwines conjugation by every normalizing representative. Consequently
an E.2.2 diagram witness lifts to an actual element of T, acting on the
actor component, with the same marked parabolics.

All uses of centerlessness are explicit in this transport module. Its
construction does not establish the missing concrete central-cover facts.
Source: Aschbacher--Smith, E.2.2(2), pp.215--216, and 15.3.65, p.1152.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single
open BorelReduction
namespace CoverModels
universe u
variable {G : Type u} [Group G] [Finite G]
variable {𝒦 : GroupClass.{u}} {H M K T Z ZS : Subgroup G} {f : ℕ}
variable [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
variable {a : LocalQuotientAction H (conjugateSpanBy ZS H) Z}
variable {I : Submodule (ZMod 2)
  (Additive ((conjugateSpanBy ZS H) ⧸ Z.subgroupOf (conjugateSpanBy ZS H)))}
variable (h : LocalInput 𝒦 H M K T Z ZS f a I)
variable (hz : center (actorImage H K) = ⊥)
include h

/-- The actual comparison map becomes an isomorphism once its center is killed. -/
def componentEquiv : actorImage H K ≃* sourceImage H M K :=
  MulEquiv.ofBijective (componentToSource h.source.core_le)
    ⟨((componentToSource h.source.core_le).ker_eq_bot_iff).mp ((componentCover_ker h).trans hz),
      componentToSource_surjective h.source.core_le⟩

theorem componentEquiv_apply (k : actorImage H K) :
    componentEquiv h hz k = componentToSource h.source.core_le k := rfl

theorem componentEquiv_overlap :
    ((actorImage H (M ⊓ K)).subgroupOf (actorImage H K)).map
      (componentEquiv h hz).toMonoidHom = SourceCases.componentOverlap H M K :=
  componentToSource_overlap h.source.core_le

def modelEquiv {X : Type*} [Group X] (e : sourceImage H M K ≃* X) :
    actorImage H K ≃* X := (componentEquiv h hz).trans e

theorem modelEquiv_apply {X : Type*} [Group X] (e : sourceImage H M K ≃* X)
    (k : actorImage H K) :
    modelEquiv h hz e k = e (componentToSource h.source.core_le k) := rfl

theorem modelEquiv_overlap {X : Type*} [Group X] (B : Subgroup X)
    (e : sourceImage H M K ≃* X)
    (he : (SourceCases.componentOverlap H M K).map e.toMonoidHom = B) :
    ((actorImage H (M ⊓ K)).subgroupOf (actorImage H K)).map
      (modelEquiv h hz e).toMonoidHom = B := by
  change Subgroup.map (e.toMonoidHom.comp (componentEquiv h hz).toMonoidHom) _ = _
  rw [← map_map, componentEquiv_overlap, he]

/-- Conjugation by the actual image of a specified element of H. -/
def actorConjugation (t : H) : MulAut (actorImage H K) :=
  (actorImage H K).normalizerMonoidHom ⟨QuotientGroup.mk' (pCore 2 H) t, by
    let := actor_normal h
    rw [normalizer_eq_top]
    exact mem_top _⟩

theorem actorConjugation_apply (t : H) (k : actorImage H K) :
    (actorConjugation h t k : H ⧸ pCore 2 H) =
      QuotientGroup.mk' (pCore 2 H) t * k * (QuotientGroup.mk' (pCore 2 H) t)⁻¹ := rfl

/-- The source automorphism induced by t is transported by the canonical
comparison, not an independently chosen automorphism of the model. -/
theorem componentEquiv_conjugation (t : H)
    (s : normalizer (sourceImage H M K : Set (H ⧸ sourceKernel H M)))
    (hs : QuotientGroup.mk' (sourceKernel H M) t = s.val) :
    MulAut.congr (componentEquiv h hz) (actorConjugation h t) =
      (sourceImage H M K).normalizerMonoidHom s := by
  ext x
  change actorToSource h.source.core_le
      (QuotientGroup.mk' (pCore 2 H) t *
        ((componentEquiv h hz).symm x : H ⧸ pCore 2 H) *
        (QuotientGroup.mk' (pCore 2 H) t)⁻¹) = s.val * x.val * s.val⁻¹
  rw [map_mul, map_mul, map_inv]
  have ht : actorToSource h.source.core_le (QuotientGroup.mk' (pCore 2 H) t) = s.val := hs
  have hx : actorToSource h.source.core_le ((componentEquiv h hz).symm x : H ⧸ pCore 2 H) =
      x.val := congrArg Subtype.val ((componentEquiv h hz).apply_symm_apply x)
  rw [ht, hx]

/-- Retain the same source diagram witness as an actual element of T and its
conjugation on the representation component. -/
theorem diagram_witness {X : Type*} [Group X]
    (e : sourceImage H M K ≃* X) (P Q : Subgroup X)
    (hd : SourceCases.MovesDiagram H M K T e P Q) :
    ∃ t : H, t.val ∈ T ∧
      ¬ (SourceCases.PreservesParabolicClass
          (MulAut.congr (modelEquiv h hz e) (actorConjugation h t)) P ∧
        SourceCases.PreservesParabolicClass
          (MulAut.congr (modelEquiv h hz e) (actorConjugation h t)) Q) := by
  obtain ⟨α, hα, hd⟩ := hd
  obtain ⟨s, hs, rfl⟩ := hα
  obtain ⟨t, ht, he⟩ := hs
  refine ⟨t, ht, ?_⟩
  have hc := componentEquiv_conjugation h hz t s he
  have heq : MulAut.congr (modelEquiv h hz e) (actorConjugation h t) =
      MulAut.congr e ((sourceImage H M K).normalizerMonoidHom s) := by
    rw [← hc]
    ext x
    rfl
  rwa [heq]

end CoverModels
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single
