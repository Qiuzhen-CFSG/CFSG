module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.Reduced
public import Theory.GroupAction.RankTwoCosetGeometry.Reorientation

/-!
# Reorienting the source rank-two pair

Interchanging the two original parabolics preserves the genuine source
hypothesis F.1.1. The coset graph is equivariantly isomorphic after this
interchange, so stabilizers, the groups Z and U, and critical distances are
unchanged. The reduced ambient subgroup is literally the same subgroup:
the common Borel and B₀ are fixed, while the two P₀ subgroups are exchanged.
Consequently the minimum critical distance b is unchanged as well.

This extension supplies the orientation change used for the Chapter 15
D₁₀/Sz(2)--A₅ source pair. It does not assert that an arbitrarily oriented
base edge is a critical pair.
Source: DGS, *Groups and Graphs* (1985), the reduction and graph definitions;
Aschbacher--Smith, Hypothesis F.1.1 and Section 15.2.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] {A B S : Subgroup G}

/-- Interchanging the two parabolics preserves the source hypothesis F.1.1. -/
theorem HypothesisF11.swap (h : HypothesisF11 ![A,B] S) : HypothesisF11 ![B,A] S := by
  refine ⟨h.finite_S,h.S_isP,?_,?_,?_,?_,?_,?_⟩
  · intro i; fin_cases i
    · exact h.S_normalizes 1
    · exact h.S_normalizes 0
  · intro i; fin_cases i
    · exact h.sylow 1
    · exact h.sylow 0
  · intro i; fin_cases i
    · exact h.quotient 1
    · exact h.quotient 0
  · intro i; fin_cases i
    · exact h.cross 1
    · exact h.cross 0
  · change pCore 2 (B ⊔ A ⊔ S : Subgroup G) = ⊥
    rw [sup_comm B A]
    exact h.twoCore_free
  · intro i; fin_cases i
    · exact h.characteristic_two 1
    · exact h.characteristic_two 0

namespace DGS85
open Subgroup.CosetGeometry.RankTwo
variable (F : Bool → Subgroup G)

private theorem swap_stabilizer (v : Vertex F) :
    stabilizer (swapFamily F) (swapVertex F v) = stabilizer F v := by
  ext g
  change g • swapVertex F v = swapVertex F v ↔ g • v = v
  rw [←swapVertex_smul]
  exact (swapVertexEquiv F).injective.eq_iff

private theorem swap_Z (v : Vertex F) :
    Z (swapFamily F) (swapVertex F v) = Z F v := by
  simp only [Z,swap_stabilizer]

private theorem swap_U (v : Vertex F) :
    U (swapFamily F) (swapVertex F v) = U F v := by
  ext g
  change (∀ w ∈ ball (swapFamily F) (swapVertex F v) 1, g • w = w) ↔
    ∀ w ∈ ball F v 1, g • w = w
  constructor
  · intro hg w hw
    apply (swapVertexEquiv F).injective
    change swapVertex F (g • w) = swapVertex F w
    rw [swapVertex_smul]
    apply hg
    rcases (mem_ball_one F v w).mp hw with hw | hw
    · exact (mem_ball_one _ _ _).mpr (.inl ((swapGraphIso F).map_adj_iff.mpr hw))
    · exact (mem_ball_one _ _ _).mpr (.inr (congrArg (swapVertex F) hw))
  · intro hg w hw
    obtain ⟨w,rfl⟩ := (swapVertexEquiv F).surjective w
    change g • swapVertex F w = swapVertex F w
    rw [←swapVertex_smul]
    congr 1
    apply hg
    rcases (mem_ball_one _ _ _).mp hw with hw | hw
    · exact (mem_ball_one F v w).mpr (.inl ((swapGraphIso F).map_adj_iff.mp hw))
    · exact (mem_ball_one F v w).mpr (.inr ((swapVertexEquiv F).injective hw))

private theorem graphIso_edist_le {V W : Type*} {Γ : SimpleGraph V} {Δ : SimpleGraph W}
    (e : Γ ≃g Δ) (v w : V) : Δ.edist (e v) (e w) ≤ Γ.edist v w := by
  by_cases h : Γ.Reachable v w
  · obtain ⟨p,hp⟩ := h.exists_walk_length_eq_edist
    rw [←hp]
    simpa only [SimpleGraph.Walk.length_map, RelEmbedding.coe_toRelHom,
      RelIso.coe_toRelEmbedding] using (p.map e.toHom).edist_le
  · rw [SimpleGraph.edist_eq_top_of_not_reachable h]
    exact le_top

private theorem swap_dist (v w : Vertex F) :
    (graph (swapFamily F)).dist (swapVertex F v) (swapVertex F w) = (graph F).dist v w := by
  unfold SimpleGraph.dist
  congr 1
  apply le_antisymm (graphIso_edist_le (swapGraphIso F) v w)
  simpa only [RelIso.symm_apply_apply] using
    graphIso_edist_le (swapGraphIso F).symm ((swapGraphIso F) v) ((swapGraphIso F) w)

/-- Relabeling the two vertex types preserves the minimum critical distance. -/
theorem b_swapFamily : b (swapFamily F) = b F := by
  unfold b
  congr 1
  ext n
  change (∃ v w, (graph (swapFamily F)).dist v w = n ∧
      ¬ Z (swapFamily F) v ≤ U (swapFamily F) w) ↔
    ∃ v w, (graph F).dist v w = n ∧ ¬ Z F v ≤ U F w
  constructor
  · rintro ⟨v,w,hd,he⟩
    obtain ⟨v,rfl⟩ := (swapVertexEquiv F).surjective v
    obtain ⟨w,rfl⟩ := (swapVertexEquiv F).surjective w
    change ¬ Z (swapFamily F) (swapVertex F v) ≤
      U (swapFamily F) (swapVertex F w) at he
    exact ⟨v,w,(swap_dist F v w).symm.trans hd,by simpa only [swap_Z,swap_U] using he⟩
  · rintro ⟨v,w,hd,he⟩
    exact ⟨swapVertex F v,swapVertex F w,(swap_dist F v w).trans hd,
      by simpa only [swap_Z,swap_U] using he⟩

namespace Reduction
variable (A B S : Subgroup G)
private theorem pair_commonBorel_swap : commonBorel ![B,A] S = commonBorel ![A,B] S := by
  change borel B S ⊔ borel A S ⊔ S = borel A S ⊔ borel B S ⊔ S
  rw [sup_comm (borel B S) (borel A S)]
private theorem pair_parabolic_swap (i : Fin 2) :
    parabolic ![B,A] S i = parabolic ![A,B] S (other i) := by fin_cases i <;> rfl
private theorem pair_starredParabolic_swap (i : Fin 2) :
    starredParabolic ![B,A] S i = starredParabolic ![A,B] S (other i) := by
  unfold starredParabolic
  rw [pair_parabolic_swap A B S i]
  fin_cases i <;> rfl
private theorem pair_B₀_swap : B₀ ![B,A] S = B₀ ![A,B] S := by
  unfold B₀
  rw [pair_commonBorel_swap A B S,pair_starredParabolic_swap A B S 0,
    pair_starredParabolic_swap A B S 1]
  change (commonBorel ![A,B] S ⊓ starredParabolic ![A,B] S 1) ⊔
      (commonBorel ![A,B] S ⊓ starredParabolic ![A,B] S 0) ⊔ _ = _
  rw [sup_comm (commonBorel ![A,B] S ⊓ starredParabolic ![A,B] S 1)
    (commonBorel ![A,B] S ⊓ starredParabolic ![A,B] S 0)]
private theorem pair_P₀_swap (i : Fin 2) : P₀ ![B,A] S i = P₀ ![A,B] S (other i) := by
  unfold P₀
  rw [pair_starredParabolic_swap A B S i,pair_B₀_swap A B S]
private theorem pair_G₀_swap : G₀ ![B,A] S = G₀ ![A,B] S := by
  unfold G₀
  rw [pair_P₀_swap A B S 0,pair_P₀_swap A B S 1]
  change P₀ ![A,B] S 1 ⊔ P₀ ![A,B] S 0 = _
  exact sup_comm _ _

/-- Swapping the original pair preserves the critical distance of its reduction. -/
theorem pair_b_swap : b (reducedFamily ![B,A] S) = b (reducedFamily ![A,B] S) := by
  unfold reducedFamily
  rw [pair_G₀_swap A B S]
  simp only [pair_P₀_swap A B S]
  have hs : family (fun i => (P₀ ![A,B] S (other i)).subgroupOf (G₀ ![A,B] S)) =
      swapFamily (family (fun i => (P₀ ![A,B] S i).subgroupOf (G₀ ![A,B] S))) := by
    funext i
    cases i <;> rfl
  rw [hs]
  exact b_swapFamily _
end Reduction
end DGS85
end CFSG.Quasithin.ChapterF.Source
