module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.EqualLinearRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.SymplecticNative

/-!
# The C₂ source comparison from the original reduced natural actors

A second DGS reduction preserves the actual completion, endpoints, starred
subgroups and whole reduced Borel. Consequently the original b=1 action data
transport to the reduced F.1.1 pair without new action or actor assumptions.
Equal-linear recognition on its marked order-four split quotient constructs
both orientations of the full symplectic comparison, including field two.

The original natural actions and the marked split quotient with rotation
order four remain earlier source inputs. The following consumer restores
the full original diagram. No equality of the original and reduced Sylows
or exhaustive selection of this row is assumed or asserted here.

Source: DGS, Groups and Graphs (1985), (10.5), Theorem D and (15.1)--(15.2),
pp.156--157,224,226--228; Fong--Seitz I (6A)(a) and II (8A).
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneReduction
open SuzukiContainment Reduction NoncommutingProfile Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- A second reduction retains the same common two-subgroup. -/
theorem sylow_idempotent (h : HypothesisF11 L S) :
    reducedSylow L (reducedSylow L S) = reducedSylow L S := reduced_borel_core h

/-- The whole reduced overlap, including its odd factors, is unchanged. -/
theorem borel_idempotent (h : HypothesisF11 L S) :
    B₀ L (reducedSylow L S) = B₀ L S := by
  rw [B₀_eq_source (reduced_hypothesis h), sylow_idempotent h, B₀_eq_source h]

/-- Both full reduced endpoints are unchanged as ambient subgroups. -/
theorem endpoint_idempotent (h : HypothesisF11 L S) (i : Fin 2) :
    P₀ L (reducedSylow L S) i = P₀ L S i := by
  rw [P₀_eq_source (reduced_hypothesis h), sylow_idempotent h, P₀_eq_source h]

/-- The reduced completion itself is unchanged as an ambient subgroup. -/
theorem generated_idempotent (h : HypothesisF11 L S) :
    G₀ L (reducedSylow L S) = G₀ L S := by
  rw [G₀_eq_source (reduced_hypothesis h), sylow_idempotent h, G₀_eq_source h]

variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]

/-- Transport the actual pair of natural actors through the subgroup equalities. -/
theorem actions (h : HypothesisF11 L S)
    (c₀ : BOneActionData (reducedFamily L S) (base (reducedFamily L S) false)
      (base (reducedFamily L S) true) k₀ W₀)
    (c₁ : BOneActionData (reducedFamily L S) (base (reducedFamily L S) true)
      (base (reducedFamily L S) false) k₁ W₁)
    (hactor₀ : c₀.actor = ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 0).subgroupOf (G₀ L S))
    (hactor₁ : c₁.actor = ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 1).subgroupOf (G₀ L S)) :
    ∃ (a₀ : BOneActionData (reducedFamily L (reducedSylow L S))
        (base (reducedFamily L (reducedSylow L S)) false)
        (base (reducedFamily L (reducedSylow L S)) true) k₀ W₀)
      (a₁ : BOneActionData (reducedFamily L (reducedSylow L S))
        (base (reducedFamily L (reducedSylow L S)) true)
        (base (reducedFamily L (reducedSylow L S)) false) k₁ W₁),
      a₀.actor = ((B₀ L (reducedSylow L S)).pCoreIn 2 ⊔
        starredParabolic L (reducedSylow L S) 0).subgroupOf (G₀ L (reducedSylow L S)) ∧
      a₁.actor = ((B₀ L (reducedSylow L S)).pCoreIn 2 ⊔
        starredParabolic L (reducedSylow L S) 1).subgroupOf (G₀ L (reducedSylow L S)) := by
  unfold reducedFamily
  rw [generated_idempotent h]
  rw [show P₀ L (reducedSylow L S) = P₀ L S from funext (endpoint_idempotent h)]
  simp only [borel_idempotent h, reduced_starredParabolic h]
  exact ⟨c₀,c₁,hactor₀,hactor₁⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneReduction

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.C2Source
open SuzukiContainment Reduction NoncommutingProfile Subgroup.CosetGeometry.RankTwo
open OriginalExtension FongSeitzBinary

/-- The two actual reduced natural actors, with the original actor identities.
Only the first natural-space equivalence is required for C₂ recognition. -/
structure Profile {G : Type*} [Group G] (L : Fin 2 → Subgroup G) (S : Subgroup G)
    (k₀ k₁ W₀ W₁ : Type*) [Field k₀] [Finite k₀] [CharP k₀ 2]
    [Field k₁] [Finite k₁] [CharP k₁ 2]
    [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁] where
  left : BOneActionData (reducedFamily L S) (base (reducedFamily L S) false)
    (base (reducedFamily L S) true) k₀ W₀
  right : BOneActionData (reducedFamily L S) (base (reducedFamily L S) true)
    (base (reducedFamily L S) false) k₁ W₁
  left_actor : left.actor = ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 0).subgroupOf (G₀ L S)
  right_actor : right.actor = ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 1).subgroupOf (G₀ L S)
  natural : letI : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
    W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)

variable {G X k₀ k₁ W₀ W₁ : Type*} [Group G] [Group X]
  [Field k₀] [Finite k₀] [CharP k₀ 2] [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}

/-- The source actors survive a second reduction because its completion,
endpoints, starred subgroups and full reduced Borel are unchanged. -/
theorem Profile.reduced (h : HypothesisF11 L S) (p : Profile L S k₀ k₁ W₀ W₁) :
    Nonempty (Profile L (reducedSylow L S) k₀ k₁ W₀ W₁) := by
  obtain ⟨a₀,a₁,ha₀,ha₁⟩ := BOneReduction.actions h p.left p.right p.left_actor p.right_actor
  exact ⟨⟨a₀,a₁,ha₀,ha₁,p.natural⟩⟩

private def intersectionToReduced (h : HypothesisF11 L S) :
    Iso (ofSubgroups (parabolic L (reducedSylow L S) 0)
      (parabolic L (reducedSylow L S) 0 ⊓ parabolic L (reducedSylow L S) 1)
      (parabolic L (reducedSylow L S) 1) inf_le_left inf_le_right)
      (reducedAmalgam L S) :=
  NativeRestoration.subgroupCongrIso _ _ _ _ rfl (lemma_F_1_3_6 (reduced_hypothesis h)) rfl

/-- Full C₂ comparison on the literal reduced pair. Both inclusions and the
whole Borel are retained, and field two is included. -/
theorem reduced_comparison (h : HypothesisF11 L S) (p : Profile L S k₀ k₁ W₀ W₁)
    (Q : MarkedQuotient P) (e : Iso (reducedAmalgam L S) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 4) :
    ∃ point : Bool, Nonempty (Iso (reducedAmalgam L S) (SymplecticNative.amalgam k₀ point)) := by
  obtain ⟨a⟩ := p.reduced h
  rcases QuadrangleStructure.marked_bOne_symplectic_comparison Q
      ((intersectionToReduced h).trans e) (reduced_hypothesis h) split
      a.left a.right a.left_actor a.right_actor a.natural hm with hf | hf
  · obtain ⟨f⟩ := hf
    exact ⟨true, ⟨(intersectionToReduced h).symm.trans f⟩⟩
  · obtain ⟨f⟩ := hf
    exact ⟨false, ⟨(intersectionToReduced h).symm.trans f⟩⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.C2Source
