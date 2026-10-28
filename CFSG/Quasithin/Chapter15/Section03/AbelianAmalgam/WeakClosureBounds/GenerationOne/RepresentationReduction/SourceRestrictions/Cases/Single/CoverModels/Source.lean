module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.LocalSetup
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.CentralComparison
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.CoverModels.CentralCollapse

/-!
# Source models on the actual single-component actor

The complete central-cover calculation gives canonical equivalences on the
actor in H/O₂(H) and on K/O₂(K). Their quotient equations, Borel-overlap
image and conjugation comparison use the original maps into H/J. The diagram
witness remains an element of the original T acting on the named parabolics.

The final source_models application discharges every centerlessness premise
of Models: the Bender alternative retains PSU₃ and its Hermitian form, while
the rank-two alternative uses the established odd-exponent PSL₃-to-SL₃ and
Sp₄′-to-Sp₄ comparisons. These are the group inputs for the independent
single-component representation deduction. No module marking is chosen here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.2.2,
printed pp.215--216, and 15.3.65, printed p.1152.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single
open BorelReduction SourceCases
namespace CoverModels
universe u
variable {G : Type u} [Group G] [Finite G]
variable {𝒦 : GroupClass.{u}} {H M K T Z ZS : Subgroup G} {f : ℕ}
variable [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
variable {a : LocalQuotientAction H (conjugateSpanBy ZS H) Z}
variable {I : Submodule (ZMod 2)
  (Additive ((conjugateSpanBy ZS H) ⧸ Z.subgroupOf (conjugateSpanBy ZS H)))}
variable (h : LocalInput 𝒦 H M K T Z ZS f a I)

/-- The original component comparison, with its centerlessness premise discharged. -/
def sourceComponentEquiv : actorImage H K ≃* sourceImage H M K :=
  componentEquiv h (actor_center_eq_bot h)

theorem sourceComponentEquiv_apply (k : actorImage H K) :
    sourceComponentEquiv h k = componentToSource h.source.core_le k := rfl

theorem sourceComponentEquiv_overlap :
    ((actorImage H (M ⊓ K)).subgroupOf (actorImage H K)).map
      (sourceComponentEquiv h).toMonoidHom = componentOverlap H M K :=
  componentEquiv_overlap h (actor_center_eq_bot h)

/-- The intrinsic K/O₂(K) model uses the same canonical quotient triangle. -/
def intrinsicSourceEquiv : (K ⧸ pCore 2 K) ≃* sourceImage H M K :=
  (intrinsicActorEquiv h).trans (sourceComponentEquiv h)

theorem intrinsicSourceEquiv_mk (k : K) :
    (intrinsicSourceEquiv h (QuotientGroup.mk' (pCore 2 K) k) : H ⧸ sourceKernel H M) =
      QuotientGroup.mk' (sourceKernel H M) ⟨k.val, h.source.component_le k.property⟩ := rfl

/-- Every E.2.2 model now lifts to the actor by its specified projection. -/
def sourceModelEquiv {X : Type*} [Group X] (e : sourceImage H M K ≃* X) :
    actorImage H K ≃* X := modelEquiv h (actor_center_eq_bot h) e

theorem sourceModelEquiv_apply {X : Type*} [Group X] (e : sourceImage H M K ≃* X)
    (k : actorImage H K) :
    sourceModelEquiv h e k = e (componentToSource h.source.core_le k) := rfl

/-- The source Borel marking is preserved on the literal M∩K image. -/
theorem sourceModelEquiv_overlap {X : Type*} [Group X] (B : Subgroup X)
    (e : sourceImage H M K ≃* X)
    (he : (componentOverlap H M K).map e.toMonoidHom = B) :
    ((actorImage H (M ⊓ K)).subgroupOf (actorImage H K)).map
      (sourceModelEquiv h e).toMonoidHom = B :=
  modelEquiv_overlap h (actor_center_eq_bot h) B e he

/-- The comparison intertwines conjugation by the original H representative. -/
theorem sourceComponentEquiv_conjugation (t : H)
    (s : normalizer (sourceImage H M K : Set (H ⧸ sourceKernel H M)))
    (hs : QuotientGroup.mk' (sourceKernel H M) t = s.val) :
    MulAut.congr (sourceComponentEquiv h) (actorConjugation h t) =
      (sourceImage H M K).normalizerMonoidHom s :=
  componentEquiv_conjugation h (actor_center_eq_bot h) t s hs

/-- The same inducing element of T moves the same marked model parabolics. -/
theorem source_diagram_witness {X : Type*} [Group X]
    (e : sourceImage H M K ≃* X) (P Q : Subgroup X)
    (hd : MovesDiagram H M K T e P Q) :
    ActorMovesDiagram h (sourceModelEquiv h e) P Q :=
  diagram_witness h (actor_center_eq_bot h) e P Q hd

/-- Complete group-model preparation for the single-component representation
deduction: J=O₂(H), and the marked Bender or diagram model on the actual actor.
All central-cover premises have been discharged from LocalInput. -/
theorem source_models :
    sourceKernel H M = pCore 2 H ∧ (ActorBenderModel H M K f ∨ ActorDiagramModel h) :=
  ⟨sourceKernel_eq_twoCore h, actor_models h (actor_center_eq_bot h)⟩

end CoverModels
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single
