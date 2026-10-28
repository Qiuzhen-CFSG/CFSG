module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.CanonicalParameters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.ProfileSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallProjectiveGraphApplication

/-!
# Chapter 7 conclusions and paired Chapter 10 actions

The intrinsic index calculation retains equal defining fields in the actual
natural-center markings. Together with the two distance branches this gives
all clauses of (7.1) and the Chapter 7 bound from genuine actor models and
the adjacent-core obstruction. Reversing a critical pair preserves its field
order. The constructed b=2 actions at both ends feed the existing opposite-lift
and literal Q/Z action consumers for every distinct neighbor.

The full-catalogue source application uses the latest enlarged-quotient and
mixed-edge theorems. Its one remaining premise excludes the actual order-144
PSU₃(2) enlargement. That premise is not proved here: the existing setup owner
retains its proof, and unconditional Chapter 7 assembly remains outstanding.
Source: DGS, *Groups and Graphs* (1985), (7.1)--(7.5), pp.126--131,
and the inputs to (10.1)--(10.6), pp.154--158.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
universe u
variable {G : Type u} [Group G]

/-- Two literal natural sections, retaining their original kernels and equal actual defining fields. -/
@[expose] def EqualFieldNaturalCenters (L₀ Z₀ Q₀ L₁ Z₁ Q₁ : Subgroup G) : Prop :=
  ∃ (k₀ : Type u) (_ : Field k₀) (_ : Finite k₀) (_ : Algebra (ZMod 2) k₀)
    (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : Algebra (ZMod 2) k₁),
    ∃ (π₀ : L₀ →* SL(2,k₀)) (π₁ : L₁ →* SL(2,k₁)),
      Function.Surjective π₀ ∧ π₀.ker = Q₀.subgroupOf L₀ ∧
      Nonempty (BinaryConjugationSection L₀ Z₀ (Stellmacher.omegaOneCenterAmbient L₀)
        (SL2NaturalOffenders.NoStrong.natural.comp π₀)) ∧
      Function.Surjective π₁ ∧ π₁.ker = Q₁.subgroupOf L₁ ∧
      Nonempty (BinaryConjugationSection L₁ Z₁ (Stellmacher.omegaOneCenterAmbient L₁)
        (SL2NaturalOffenders.NoStrong.natural.comp π₁)) ∧
      Nat.card k₀ = Nat.card k₁

/-- Reorient the actual natural markings without changing either section. -/
theorem EqualFieldNaturalCenters.symm {L₀ Z₀ Q₀ L₁ Z₁ Q₁ : Subgroup G}
    (h : EqualFieldNaturalCenters L₀ Z₀ Q₀ L₁ Z₁ Q₁) :
    EqualFieldNaturalCenters L₁ Z₁ Q₁ L₀ Z₀ Q₀ := by
  obtain ⟨k₀,f₀,n₀,a₀,k₁,f₁,n₁,a₁,π₀,π₁,hπ₀,hk₀,s₀,hπ₁,hk₁,s₁,hcard⟩ := h
  exact ⟨k₁,f₁,n₁,a₁,k₀,f₀,n₀,a₀,π₁,π₀,hπ₁,hk₁,s₁,hπ₀,hk₀,s₀,hcard.symm⟩

namespace Reduction
open DGS85.Reduction NoncommutingProfile
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L₀ S₀ i) (G₀ L₀ S₀))

/-- Construct the two natural-center markings and both original Sylow products with equal field orders. -/
theorem reduced_critical_equal_field_natural_centers (h : HypothesisF11 L₀ S₀)
    (hm : ∀ x : Vertex F, IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)))
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) :
    EqualFieldNaturalCenters (graphLocalGroup F v) (Z F v) (Q F v)
      (graphLocalGroup F w) (Z F w) (Q F w) ∧
    Stellmacher.IsSylowSubgroupIn (Z F w ⊔ Q F v) (stabilizer F v) ∧
    Stellmacher.IsSylowSubgroupIn (Z F v ⊔ Q F w) (stabilizer F w) := by
  let ht := reduced_triple h
  let d := graphActorLocalData ht (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hm
  have hd := graphActorLocalData_star ht (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hm
  obtain ⟨hn₀,hn₁,hs₀,hs₁⟩ := reduced_critical_natural_centers_of_localData h
    (graphLocalGroup F) d hd (graph_actor_odd_index ht) hc hne
  obtain ⟨k₀,f₀,n₀,a₀,π₀,hπ₀,hk₀,s₀⟩ := hn₀
  obtain ⟨k₁,f₁,n₁,a₁,π₁,hπ₁,hk₁,s₁⟩ := hn₁
  let : CharP k₀ 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) k₀).injective 2
  let : CharP k₁ 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) k₁).injective 2
  exact ⟨⟨k₀,f₀,n₀,a₀,k₁,f₁,n₁,a₁,π₀,π₁,hπ₀,hk₀,s₀,hπ₁,hk₁,s₁,
    reduced_critical_marked_field_orders h hm hc hne π₀ hπ₀ hk₀ π₁ hπ₁ hk₁⟩,hs₀,hs₁⟩

/-- Both distance branches and all of (7.1), with genuine Chapter 6 actor and obstruction inputs. -/
theorem reduced_noncommuting_source_conclusion (h : HypothesisF11 L₀ S₀)
    (hm : ∀ x : Vertex F, IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)))
    (hob : ∀ x y, (graph F).Adj x y → ¬ stabilizer F y ≤
      normalizer ((Q F x ⊓ Q F y : Subgroup (G₀ L₀ S₀)) : Set (G₀ L₀ S₀)))
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) :
    (b F = 1 ∨ b F = 2) ∧
    EqualFieldNaturalCenters (graphLocalGroup F v) (Z F v) (Q F v)
      (graphLocalGroup F w) (Z F w) (Q F w) ∧
    Stellmacher.IsSylowSubgroupIn (Z F w ⊔ Q F v) (stabilizer F v) ∧
    Stellmacher.IsSylowSubgroupIn (Z F v ⊔ Q F w) (stabilizer F w) :=
  ⟨(reduced_distance_bound_of_actor_models h hm hob hc hne).1,
    reduced_critical_equal_field_natural_centers h hm hc hne⟩

/-- Full-catalogue Chapter 7 application; only the unresolved order-144 enlargement is excluded. -/
theorem reduced_noncommuting_source_conclusion_of_no_order144 (h : HypothesisF11 L₀ S₀)
    (hsmall : ∀ i : Fin 2,
      Nat.card (enlargedEndpoint L₀ S₀ i ⧸ pCore 2 (enlargedEndpoint L₀ S₀ i)) ≠ 144)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) :
    (b F = 1 ∨ b F = 2) ∧
    EqualFieldNaturalCenters (graphLocalGroup F v) (Z F v) (Q F v)
      (graphLocalGroup F w) (Z F w) (Q F w) ∧
    Stellmacher.IsSylowSubgroupIn (Z F w ⊔ Q F v) (stabilizer F v) ∧
    Stellmacher.IsSylowSubgroupIn (Z F v ⊔ Q F w) (stabilizer F w) :=
  reduced_noncommuting_source_conclusion h (reduced_actor_models_of_no_order144 h hsmall)
    (fun x y he => reduced_graph_core_obstruction_of_no_order144 h hsmall y x he.symm) hc hne

theorem bTwo_center_action_field_order
    {v m w : Vertex F} {k W : Type*} [Field k] [Finite k] [CharP k 2]
    [AddCommGroup W] [Module (ZMod 2) W]
    (c : BTwoCenterActionData F v m w k W) :
    Nat.card k = (Q F v).relIndex (Z F w) := by
  have hc : Nat.card (((Z F w).subgroupOf c.actor).map c.quotient) = Nat.card k := by
    rw [c.critical_image]
    exact Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 c.imageSylow).symm.toEquiv
  exact hc.symm.trans (actor_image_card_eq_relIndex c.actor (Q F v) (Z F w)
    c.quotient c.kernel c.critical_le)

/-- Reoriented Chapter 10 action data have equal actual fields, independently of their chosen markings. -/
theorem reduced_bTwo_profile_field_orders (h : HypothesisF11 L₀ S₀)
    (hm : ∀ x : Vertex F, IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)))
    {v m w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    {k₀ W₀ k₁ W₁ : Type*}
    [Field k₀] [Finite k₀] [CharP k₀ 2] [AddCommGroup W₀] [Module (ZMod 2) W₀]
    [Field k₁] [Finite k₁] [CharP k₁ 2] [AddCommGroup W₁] [Module (ZMod 2) W₁]
    (c₀ : BTwoCenterActionData F v m w k₀ W₀)
    (c₁ : BTwoCenterActionData F w m v k₁ W₁) : Nat.card k₀ = Nat.card k₁ :=
  (bTwo_center_action_field_order c₀).trans
    ((reduced_critical_core_indices_eq h hm hc hne).trans (bTwo_center_action_field_order c₁).symm)

/-- Construct both Chapter 10 actions with equal fields and apply their opposite-lift and core-action consumers. -/
theorem reduced_bTwo_equal_field_profile_actions (h : HypothesisF11 L₀ S₀)
    (hm : ∀ x : Vertex F, IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)))
    {v m w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 2) (hvm : (graph F).Adj v m) (hmw : (graph F).Adj m w) :
    ∃ (k₀ : Type u) (_ : Field k₀) (_ : Finite k₀) (_ : CharP k₀ 2) (_ : Algebra (ZMod 2) k₀)
      (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : CharP k₁ 2) (_ : Algebra (ZMod 2) k₁),
      ∃ (c₀ : BTwoCenterActionData F v m w k₀ (Fin 2 → k₀))
        (c₁ : BTwoCenterActionData F w m v k₁ (Fin 2 → k₁)),
        c₀.actor = graphLocalGroup F v ∧ c₁.actor = graphLocalGroup F w ∧
        Nat.card k₀ = Nat.card k₁ ∧
        (∀ t, (graph F).Adj v t → t ≠ m →
          ∃ g : c₀.actor, (g : G₀ L₀ S₀) • m = t ∧
            c₀.quotient g ∉ normalizer (c₀.imageSylow : Set SL(2,k₀)) ∧
            Nonempty (BTwoActionData F w m v t k₀)) ∧
        (∀ t, (graph F).Adj w t → t ≠ m →
          ∃ g : c₁.actor, (g : G₀ L₀ S₀) • m = t ∧
            c₁.quotient g ∉ normalizer (c₁.imageSylow : Set SL(2,k₁)) ∧
            Nonempty (BTwoActionData F v m w t k₁)) := by
  obtain ⟨k₀,f₀,n₀,ch₀,a₀,c₀,ha₀⟩ := reduced_bTwo_center_action_exists h hm hc hne hb hvm hmw
  have hc' := (reduced_noncommuting_critical_intersections h hc hne).1
  obtain ⟨k₁,f₁,n₁,ch₁,a₁,c₁,ha₁⟩ := reduced_bTwo_center_action_exists h hm hc'
    (by rwa [commutator_comm]) hb hmw.symm hvm.symm
  refine ⟨k₀,f₀,n₀,ch₀,a₀,k₁,f₁,n₁,ch₁,a₁,c₀,c₁,ha₀,ha₁,
    reduced_bTwo_profile_field_orders h hm hc hne c₀ c₁,?_,?_⟩
  · intro t ht htm
    obtain ⟨g,hg,hout⟩ := c₀.exists_opposite_lift (reduced_triple h) ht htm
    exact ⟨g,hg,hout,⟨c₀.coreActionData g hg⟩⟩
  · intro t ht htm
    obtain ⟨g,hg,hout⟩ := c₁.exists_opposite_lift (reduced_triple h) ht htm
    exact ⟨g,hg,hout,⟨c₁.coreActionData g hg⟩⟩

/-- The full-catalogue b=2 profile application with the same single outstanding enlargement premise. -/
theorem reduced_bTwo_equal_field_profile_actions_of_no_order144 (h : HypothesisF11 L₀ S₀)
    (hsmall : ∀ i : Fin 2,
      Nat.card (enlargedEndpoint L₀ S₀ i ⧸ pCore 2 (enlargedEndpoint L₀ S₀ i)) ≠ 144)
    {v m w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 2) (hvm : (graph F).Adj v m) (hmw : (graph F).Adj m w) :
    ∃ (k₀ : Type u) (_ : Field k₀) (_ : Finite k₀) (_ : CharP k₀ 2) (_ : Algebra (ZMod 2) k₀)
      (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : CharP k₁ 2) (_ : Algebra (ZMod 2) k₁),
      ∃ (c₀ : BTwoCenterActionData F v m w k₀ (Fin 2 → k₀))
        (c₁ : BTwoCenterActionData F w m v k₁ (Fin 2 → k₁)),
        c₀.actor = graphLocalGroup F v ∧ c₁.actor = graphLocalGroup F w ∧
        Nat.card k₀ = Nat.card k₁ ∧
        (∀ t, (graph F).Adj v t → t ≠ m →
          ∃ g : c₀.actor, (g : G₀ L₀ S₀) • m = t ∧
            c₀.quotient g ∉ normalizer (c₀.imageSylow : Set SL(2,k₀)) ∧
            Nonempty (BTwoActionData F w m v t k₀)) ∧
        (∀ t, (graph F).Adj w t → t ≠ m →
          ∃ g : c₁.actor, (g : G₀ L₀ S₀) • m = t ∧
            c₁.quotient g ∉ normalizer (c₁.imageSylow : Set SL(2,k₁)) ∧
            Nonempty (BTwoActionData F v m w t k₁)) :=
  reduced_bTwo_equal_field_profile_actions h (reduced_actor_models_of_no_order144 h hsmall)
    hc hne hb hvm hmw

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
