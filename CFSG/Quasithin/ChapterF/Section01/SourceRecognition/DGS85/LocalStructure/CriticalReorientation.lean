module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PairReorientation

/-!
# Original critical-path reorientation

Swapping the original F.1.1 factors keeps the reduced ambient subgroup and
full Borel unchanged. Relabel the literal cosets to transport a critical path
whose starting vertex has type true to the type-false orientation of the
swapped original pair. The critical escape uses the entire local kernel U;
the noncommuting centers and middle-edge incidence are transported together.
-/

public noncomputable section
open Subgroup Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction.CriticalReorientation
variable {G : Type*} [Group G] (A B S : Subgroup G)
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


private theorem pair_family_swap :
    family (fun i => (P₀ ![B,A] S i).subgroupOf (G₀ ![A,B] S)) =
      swapFamily (reducedFamily ![A,B] S) := by
  funext i
  cases i
  · exact congrArg (fun H : Subgroup G => H.subgroupOf (G₀ ![A,B] S)) (pair_P₀_swap A B S 0)
  · exact congrArg (fun H : Subgroup G => H.subgroupOf (G₀ ![A,B] S)) (pair_P₀_swap A B S 1)

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


/-- Reorient an actual noncommuting critical path by exchanging the original
factors. No new escape, source comparison, or endpoint marking is assumed. -/
theorem original_noncommuting_critical_swap
    {w : Vertex (reducedFamily ![A,B] S)}
    (hc : IsCriticalPair (reducedFamily ![A,B] S)
      (base (reducedFamily ![A,B] S) true) w)
    (hne : ⁅Z (reducedFamily ![A,B] S) (base (reducedFamily ![A,B] S) true),
      Z (reducedFamily ![A,B] S) w⁆ ≠ ⊥)
    (hmw : (graph (reducedFamily ![A,B] S)).Adj
      (base (reducedFamily ![A,B] S) false) w) :
    ∃ w' : Vertex (reducedFamily ![B,A] S),
      IsCriticalPair (reducedFamily ![B,A] S)
        (base (reducedFamily ![B,A] S) false) w' ∧
      ⁅Z (reducedFamily ![B,A] S) (base (reducedFamily ![B,A] S) false),
        Z (reducedFamily ![B,A] S) w'⁆ ≠ ⊥ ∧
      (graph (reducedFamily ![B,A] S)).Adj
        (base (reducedFamily ![B,A] S) true) w' := by
  unfold reducedFamily
  rw [pair_G₀_swap A B S, pair_family_swap]
  let F₀ := reducedFamily ![A,B] S
  refine ⟨swapVertex F₀ w, ⟨?_, ?_⟩, ?_, ?_⟩
  · change (graph (swapFamily F₀)).dist
      (swapVertex F₀ (base F₀ true)) (swapVertex F₀ w) = b (swapFamily F₀)
    rw [swap_dist, b_swapFamily]
    exact hc.1
  · change ¬ Z (swapFamily F₀) (swapVertex F₀ (base F₀ true)) ≤
      U (swapFamily F₀) (swapVertex F₀ w)
    simpa only [swap_Z, swap_U] using hc.2
  · change ⁅Z (swapFamily F₀) (swapVertex F₀ (base F₀ true)),
      Z (swapFamily F₀) (swapVertex F₀ w)⁆ ≠ ⊥
    simpa only [swap_Z] using hne
  · change (graph (swapFamily F₀)).Adj
      ((swapGraphIso F₀) (base F₀ false)) ((swapGraphIso F₀) w)
    exact (swapGraphIso F₀).map_adj_iff.mpr hmw

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction.CriticalReorientation
