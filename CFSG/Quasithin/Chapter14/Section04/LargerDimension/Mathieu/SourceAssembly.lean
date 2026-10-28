module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.SourceGeometry
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.GeneratedSource
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.SecondActorPosition
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.DesignFlag

/-!
# Source Lemma 14.4.12

The genuine Mathieu quotient action and the earlier 12.8/14.4 geometry give
exactly two source actors. The first is the literal O²(O₂,₃(H)); the second
comes from the proved native residual catalogue. Their moved spaces have
order eight by the actual extraspecial central-kernel lift. Native radical
calculations and [W,Wg] ≤ E place both in E, while fixation excludes the
third Borel actor. The original overlap quotient is S₃ × S₃.

The earlier-source hypotheses and equivariant module marking are retained;
none of the actor, displacement or quotient conclusions is an input.
The final application gives the actual partner of L₁ needed by 14.4.13.

Source: Aschbacher--Smith 14.4.12--13, printed pp.1011--1012.
-/

@[expose] public section
noncomputable section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu
open ModuleGeometry.Native

variable {G Q : Type*} [Group G] [Finite G] [Group Q] [IsMulCommutative Q]
  [Module (ZMod 2) (Additive Q)]
  {H U V₂ W R E : Subgroup G} {S : Sylow 2 H}
  {e : coreQuotient H ≃* ActorCatalogue.Native.Model}
  {d : CentralAction (Q := Q) H U e} {Rbar : Subgroup Group}

/-- The full two-member Y-family and actual overlap quotient of 14.4.12,
from the original marked action and earlier local geometry. -/
theorem lemma_14_4_12 [IsExtraspecial 2 U]
    (h : EarlierGeometry H U V₂ W R E S e d Rbar) :
    ∃ X : Subgroup G,
      YFamily H ((S : Subgroup H).map H.subtype) V₂ E = {firstActor H, X} ∧
      TwoM22Output H ((S : Subgroup H).map H.subtype) V₂ E (firstActor H) X := by
  obtain ⟨full⟩ := ActorCatalogue.exists_generated_source_actors H S e
    markedVector markedVector_ne_zero h.fixed_point
  let a := full.actors
  let T := (S : Subgroup H).map H.subtype
  let X := ActorCatalogue.liftedActor H e a.parabolic
  have h₁ : firstActor H ∈ XFamily H T := by rw [a.catalogue]; simp
  have h₂ : X ∈ XFamily H T := by rw [a.catalogue]; simp [X]
  have hSP : (markedSylow : Subgroup Group) ≤ a.parabolic :=
    h.sylow_marking ▸ a.sylow_le_parabolic
  have hPi : (markedSylow : Subgroup Group).relIndex a.parabolic = 3 :=
    h.sylow_marking ▸ a.parabolic_index
  have hline : ∀ s : markedSylow, ActorCatalogue.Native.action s.val markedVector = markedVector := by
    have hv : markedVector ∈ fixedSpace representation markedSylow := by
      rw [markedSylow_fixedSpace]
      exact Submodule.mem_span_singleton_self _
    exact hv
  have h₂card : Nat.card (movedSpace V₂ X) = 8 := by
    apply d.movedSpace_card_eight T V₂ X h₂ h.core_le_sylow h.point_le_core h.center_le_point
    rw [h.point_marking]
    change Nat.card (subspaceCommutator ActorCatalogue.Native.action (binaryLine markedVector)
      (((ActorCatalogue.liftedActor H e a.parabolic).subgroupOf H).map
        (ActorCatalogue.starProjection H e))) = 4
    rw [ActorCatalogue.liftedActor_image]
    exact ModuleGeometry.secondActor_commutator_card_four markedSylow a.parabolic hSP hPi
      markedVector hline a.parabolic_moves
  have h₂E : movedSpace V₂ X ≤ E := by
    apply d.movedSpace_le_of_native_bound V₂ X W R E h.point_le_core h₂.le_H
      h.hyperplane_le_core h.conjugate_le_local h.center_le_intersection h.commutator_le_intersection
    rw [h.point_marking, h.hyperplane_marking, h.radical_image]
    change subspaceCommutator ActorCatalogue.Native.action (binaryLine markedVector)
      (((ActorCatalogue.liftedActor H e a.parabolic).subgroupOf H).map
        (ActorCatalogue.starProjection H e)) ≤ _
    rw [ActorCatalogue.liftedActor_image]
    exact SecondActorPosition.second_displacement_le_radical a.parabolic hSP hPi
      a.parabolic_disjoint a.parabolic_moves
  exact ⟨X, twoM22Output_of_three_actor_calculation H T V₂ E (firstActor H) X
    (borelActor (ActorCatalogue.sourceBorel H e a.borel)) a.catalogue
    (h.first_movedSpace_card h₁) h₂card (h.first_movedSpace_le h₁) h₂E
    (h.borel_not_mem_YFamily a.borel a.borel_fixes) a.first_ne_second a.overlap⟩

/-- Actual 14.4.13 consumer: the earlier L₁ membership selects its other
actor, retaining the literal overlap group and core quotient. -/
theorem exists_partner [IsExtraspecial 2 U]
    (h : EarlierGeometry H U V₂ W R E S e d Rbar) (L₁ : Subgroup G)
    (hL : L₁ ∈ YFamily H ((S : Subgroup H).map H.subtype) V₂ E) :
    ∃ X : Subgroup G, X ≠ L₁ ∧
      YFamily H ((S : Subgroup H).map H.subtype) V₂ E = {L₁, X} ∧
      Nonempty (coreQuotient (L₁ ⊔ X ⊔ ((S : Subgroup H).map H.subtype)) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  obtain ⟨X, hY, ho⟩ := lemma_14_4_12 h
  rw [hY] at hL
  rcases hL with rfl | hL
  · exact ⟨X, ho.distinct.symm, hY, ho.overlap_quotient⟩
  · have he : L₁ = X := hL
    subst L₁
    refine ⟨firstActor H, ho.distinct, ?_, ?_⟩
    · simpa only [Set.pair_comm] using hY
    · rw [sup_comm X (firstActor H)]
      exact ho.overlap_quotient

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu
