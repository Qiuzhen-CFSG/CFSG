module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.ModelComparisons
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection

/-!
# Exact local quotient comparisons in the exchanged branch

E.2.2(1) says J=O₂(H). Thus the action and source quotients are identified
by the identity on H, and the same map identifies both component overlaps.
For relatively subnormal K, its image in H/O₂(H) is K/O₂(K). These maps
retain the quotient representatives; no unrelated model isomorphism or
central-kernel collapse is assumed.

Source: Aschbacher--Smith, E.2.2(1), pp.215--216, and p.1152(i),(iii).
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged
open BorelReduction BorelReduction.SourceCases

variable {D : Type*} [Group D]

/-- Equality of quotient kernels induces the identity-on-representatives
equivalence between the literal images of a subgroup. -/
def quotientImageCongr {N J : Subgroup D} [N.Normal] [J.Normal]
    (h : N = J) (A : Subgroup D) :
    A.map (QuotientGroup.mk' N) ≃* A.map (QuotientGroup.mk' J) := by
  subst J
  exact MulEquiv.refl _

/-- The same quotient comparison identifies every indicated overlap. -/
theorem quotientImageCongr_overlap {N J : Subgroup D} [N.Normal] [J.Normal]
    (h : N = J) (A C : Subgroup D) :
    ((C.map (QuotientGroup.mk' N)).subgroupOf (A.map (QuotientGroup.mk' N))).map
      (quotientImageCongr h A).toMonoidHom =
    (C.map (QuotientGroup.mk' J)).subgroupOf (A.map (QuotientGroup.mk' J)) := by
  subst J
  exact Subgroup.map_id _

variable {G : Type*} [Group G] {H M K : Subgroup G}

/-- The actual component comparison for E.2.2(1), using precisely J=O₂(H). -/
def localComponentToSource (hker : sourceKernel H M = pCore 2 H) :
    actorImage H K ≃* sourceImage H M K := quotientImageCongr hker.symm (K.subgroupOf H)

/-- The component overlap is transported by that same comparison. -/
theorem localComponentToSource_overlap (hker : sourceKernel H M = pCore 2 H) :
    ((actorImage H (M ⊓ K)).subgroupOf (actorImage H K)).map
      (localComponentToSource (K := K) hker).toMonoidHom = componentOverlap H M K :=
  quotientImageCongr_overlap hker.symm (K.subgroupOf H) ((M ⊓ K).subgroupOf H)

variable [Finite G]

/-- Relative subnormality identifies the intrinsic two-core quotient with
its actual representation image. This also applies to the component orbit K₀. -/
def intrinsicCoreActorEquiv (hKH : K ≤ H) (hsub : (K.subgroupOf H).IsSubnormal) :
    (K ⧸ pCore 2 K) ≃* actorImage H K :=
  (QuotientGroup.congr (pCore 2 (K.subgroupOf H)) (pCore 2 K)
    (subgroupOfEquivOfLe hKH) (pCore_map_iso 2 (subgroupOfEquivOfLe hKH))).symm.trans
      (hsub.quotientCoreImageEquiv 2)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged
