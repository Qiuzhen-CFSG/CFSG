module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.CriticalSylowProducts
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.BOneProfileSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneOrderSource

/-!
# The b=1 natural action on the original full Borel core

Source (7.1)(c) identifies the common edge Sylow with the product of the
two original parabolic cores. Its literal inclusion image is O₂(B), even
when the original F1.11 subgroup S is larger. The intrinsic graph actors
are identified with the original Chapter 6 enlargements, including their
full centers.

The Chapter 7 construction supplies both natural actions and their equal
field orders. Applying the existing Chapter 10 order theorem then gives
the two core orders q² or q³ and the corresponding full Borel core order
q³ or q⁴. The natural coordinates and actual matrix markings remain in
the conclusion; no Chapter 10 order or center premise is assumed.

The actor-model premise is the earlier setup input. Its unresolved
order-144 enlargement and the unconditional Chapter 7 bound remain with
their existing assembly owners. Source: DGS, *Groups and Graphs* (1985),
(7.1)(c), pp.126--127, (10.5)(a--c), pp.155--156, and pp.95--96.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
open DGS85.Reduction NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => reducedFamily L₀ S₀

/-- The original full Borel core is the product of the two original parabolic cores. -/
theorem original_bOne_borel_core_eq_product (h : HypothesisF11 L₀ S₀)
    (hm : ∀ x : Vertex F, IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)))
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 1) :
    (commonBorel L₀ S₀).pCoreIn 2 =
      (parabolic L₀ S₀ 0).pCoreIn 2 ⊔ (parabolic L₀ S₀ 1).pCoreIn 2 := by
  obtain ⟨hc₀,hne₀⟩ := reduced_bOne_base_critical_noncommuting h hc hne hb
  change IsCriticalPair F (base F false) (base F true) at hc₀
  change ⁅Z F (base F false),Z F (base F true)⁆ ≠ ⊥ at hne₀
  have he : (graph F).Adj (base F false) (base F true) :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hp := reduced_critical_product_eq_edge_core h hm hc₀ hne₀ he
    (by rw [SimpleGraph.dist_self,hb])
  have hcores : Q F (base F false) ⊔ Q F (base F true) =
      (stabilizer F (base F false) ⊓ stabilizer F (base F true)).pCoreIn 2 := by
    apply le_antisymm
    · exact sup_le (graph_Q_le_edgeCore (reduced_triple h) he)
        (by
          have hh : Q F (base F true) ≤
              (stabilizer F (base F true) ⊓ stabilizer F (base F false)).pCoreIn 2 :=
            graph_Q_le_edgeCore (reduced_triple h) he.symm
          rwa [inf_comm] at hh)
    · rw [←hp]
      exact sup_le (((source_Z_Q_U (reduced_triple h) (base F true)).1.trans
        (map_subtype_le _)).trans le_sup_right) le_sup_left
  have ht := congrArg (map (G₀ L₀ S₀).subtype) hcores
  rw [Subgroup.map_sup,reduced_base_Q_map h false,reduced_base_Q_map h true,
    ←Bool.not_false,reduced_base_edge_core_map h false] at ht
  exact ht.symm

/-- The constructed actor is the literal source enlargement used by the Chapter 10 order theorem. -/
theorem reduced_base_actor_eq_source (h : HypothesisF11 L₀ S₀) (i : Bool) :
    graphLocalGroup F (base F i) =
      ((B₀ L₀ S₀).pCoreIn 2 ⊔ starredParabolic L₀ S₀ (if i then 1 else 0)).subgroupOf (G₀ L₀ S₀) := by
  apply map_injective (G₀ L₀ S₀).subtype_injective
  rw [reduced_graphLocalGroup_image h i,B₀_core h]
  have he : family (enlargedEndpoint L₀ S₀) i =
      (commonBorel L₀ S₀).pCoreIn 2 ⊔ starredParabolic L₀ S₀ (if i then 1 else 0) := by
    cases i <;> exact sup_comm _ _
  have hle (j : Fin 2) : P₀ L₀ S₀ j ≤ G₀ L₀ S₀ := by
    fin_cases j
    · exact le_sup_left
    · exact le_sup_right
  have hcore : (commonBorel L₀ S₀).pCoreIn 2 ≤ P₀ L₀ S₀ (if i then 1 else 0) := by
    rw [←B₀_core h]
    exact (pCoreIn_le 2 _).trans le_sup_right
  rw [he,map_subgroupOf_eq_of_le (sup_le (hcore.trans (hle _)) (le_sup_left.trans (hle _)))]

/-- The existing Chapter 10 order calculation now uses the actual full Borel core,
with both actions constructed from Chapter 7 and the source actors identified. -/
theorem original_bOne_natural_borel_orders (h : HypothesisF11 L₀ S₀)
    (hm : ∀ x : Vertex F, IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)))
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 1) :
    ∃ (k₀ : Type u) (_ : Field k₀) (_ : Finite k₀) (_ : CharP k₀ 2) (_ : Algebra (ZMod 2) k₀)
      (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : CharP k₁ 2) (_ : Algebra (ZMod 2) k₁),
      ∃ (c₀ : BOneActionData F (base F false) (base F true) k₀ (Fin 2 → k₀))
        (c₁ : BOneActionData F (base F true) (base F false) k₁ (Fin 2 → k₁)),
        c₀.actor = graphLocalGroup F (base F false) ∧
        c₁.actor = graphLocalGroup F (base F true) ∧ Nat.card k₀ = Nat.card k₁ ∧
        OriginalNaturalCoreCoordinates false c₀ ∧ OriginalNaturalCoreCoordinates true c₁ ∧
        ((centerIn (enlargedEndpoint L₀ S₀ 0) = ⊥ ∧
          centerIn (enlargedEndpoint L₀ S₀ 1) = ⊥ ∧
          Nat.card ((parabolic L₀ S₀ 0).pCoreIn 2) = Nat.card k₀ ^ 2 ∧
          Nat.card ((parabolic L₀ S₀ 1).pCoreIn 2) = Nat.card k₁ ^ 2 ∧
          Nat.card ((commonBorel L₀ S₀).pCoreIn 2) = Nat.card k₀ ^ 3) ∨
        (Nat.card (centerIn (enlargedEndpoint L₀ S₀ 0)) = Nat.card k₀ ∧
          Nat.card (centerIn (enlargedEndpoint L₀ S₀ 1)) = Nat.card k₁ ∧
          Nat.card ((parabolic L₀ S₀ 0).pCoreIn 2) = Nat.card k₀ ^ 3 ∧
          Nat.card ((parabolic L₀ S₀ 1).pCoreIn 2) = Nat.card k₁ ^ 3 ∧
          Nat.card ((commonBorel L₀ S₀).pCoreIn 2) = Nat.card k₀ ^ 4)) := by
  obtain ⟨_,_,k₀,f₀,n₀,ch₀,a₀,k₁,f₁,n₁,ch₁,a₁,c₀,c₁,ha₀,ha₁,hfields,hn₀,hn₁⟩ :=
    original_bOne_natural_cores_of_actor_models h hm hc hne hb
  have haeq₀ : a₀ = ZMod.algebra k₀ 2 := Subsingleton.elim _ _
  have haeq₁ : a₁ = ZMod.algebra k₁ 2 := Subsingleton.elim _ _
  subst a₀ a₁
  let : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
  let : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
  change c₀.actor = graphLocalGroup F (base F false) at ha₀
  change c₁.actor = graphLocalGroup F (base F true) at ha₁
  have ho := (original_center_and_core_product_orders h c₀ c₁
    (LinearEquiv.refl (ZMod 2) _) (LinearEquiv.refl (ZMod 2) _)
    (ha₀.trans (reduced_base_actor_eq_source h false))
    (ha₁.trans (reduced_base_actor_eq_source h true))).2
  rw [ha₀,ha₁,reduced_graphLocalGroup_image h false,reduced_graphLocalGroup_image h true,
    ←original_bOne_borel_core_eq_product h hm hc hne hb] at ho
  exact ⟨k₀,f₀,n₀,ch₀,inferInstance,k₁,f₁,n₁,ch₁,inferInstance,c₀,c₁,
    ha₀,ha₁,hfields,hn₀,hn₁,ho⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting.Reduction
