module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.IntersectionOmega
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RadiusThreeSectionIndex
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.OmegaCommutatorComplete

/-!
# Literal radius-three intersection and residual-index applications

The complete first omega placement gives the strict index of the original
residual denominator for every ordered critical configuration with b > 3.
The second placement is proved when b >= 7 or the moving quotient is linear
or D₁₀. In these cases it feeds directly into the proved 8.3 inclusion at
the same moving neighbor and the same full-edge Sylow.

The final theorem constructs both marked Sylows for the b >= 7 branch.
No hypothesis identifies an intersection of involution-generated groups
with an elementary group. The nonlinear b = 5 intersection argument, the
full neighboring-span commutator, and the residual contradiction are still
separate steps of 8.4.

Source: DGS, *Groups and Graphs* (1985), 8.4(3) and its following paragraph,
printed p.138. Every application is on the reduced F1.11 graph and works
in either orientation.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The source denominator and its strict marked index on the actual reduced
graph. The exponent assertion on the moving intersection is not needed here. -/
theorem reduced_radius_three_section_index
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 3 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥) :
    let F := Reduction.reducedFamily J S₀
    let W := V F beta 3
    ∃ (prev : Vertex F) (R : Sylow 2 (graphLocalGroup F a')),
      (graph F).Adj a' prev ∧
      (graph F).dist beta prev + 1 = (graph F).dist beta a' ∧
      W ≤ Q F prev ∧
      (R : Subgroup (graphLocalGroup F a')).map (graphLocalGroup F a').subtype =
        (stabilizer F a' ⊓ stabilizer F prev).pCoreIn 2 ∧
      W ≤ quotientSylowOmegaPreimage (graphLocalGroup F a') R ∧
      ((V F beta 1).subgroupOf W).Normal ∧
      (((W ⊓ Q F a') ⊔ V F beta 1).subgroupOf W).Normal ∧
      ((W ⊓ Q F a') ⊔ V F beta 1).relIndex W <
        Nat.card (omegaCenterIn ((R : Subgroup (graphLocalGroup F a')).map
          (QuotientGroup.mk' (pCore 2 (graphLocalGroup F a'))))) := by
  exact source_radius_three_section_index (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reducedEarlierLocalTheorems h hob)
    hob models hc hab hd hb hcomm hne

/-- In the proved intersection branches, 8.3 bounds the action of the actual
radius-three intersection at the specified moving neighbor. -/
theorem reduced_moving_radius_three_intersection_bound
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val))
    (hR : (R : Subgroup (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)).map
      (graphLocalGroup (Reduction.reducedFamily J S₀) w.val).subtype =
      (stabilizer (Reduction.reducedFamily J S₀) w.val ⊓
        stabilizer (Reduction.reducedFamily J S₀) a').pCoreIn 2)
    (hcase : 6 < b (Reduction.reducedFamily J S₀) ∨
      (∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL
        (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
          pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) 2 (2 ^ n)) ∨
      Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) ≃* DihedralGroup 5)) :
    let F := Reduction.reducedFamily J S₀
    let A := V F beta 3 ⊓ Q F a'
    A ≤ quotientSylowOmegaPreimage (graphLocalGroup F w.val) R ∧
      ⁅A,Z F w.val⁆ ≤ ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ := by
  have hA := source_radius_three_intersection_omega_of_large_or_elementary_model
    (Reduction.reduced_triple h) (Reduction.reducedEarlierLocalTheorems h hob)
    (beta := beta) w (models w.val) R hR hcase
  exact ⟨hA,(commutator_mono hA le_rfl).trans
    (reduced_moving_omega_commutator h hob models hc hab hd hb hcomm w hm R hR)⟩

/-- Both original omega placements, and the literal moving-neighbor
commutator application, for the b >= 7 part of the source contradiction. -/
theorem reduced_radius_three_omega_placements_of_large
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 6 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥) :
    let F := Reduction.reducedFamily J S₀
    let W := V F beta 3
    let H := ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆
    ∃ (prev : Vertex F) (R : Sylow 2 (graphLocalGroup F a'))
      (w : (graph F).neighborSet a') (T : Sylow 2 (graphLocalGroup F w.val)),
      (graph F).Adj a' prev ∧ W ≤ Q F prev ∧
      (R : Subgroup (graphLocalGroup F a')).map (graphLocalGroup F a').subtype =
        (stabilizer F a' ⊓ stabilizer F prev).pCoreIn 2 ∧
      W ≤ quotientSylowOmegaPreimage (graphLocalGroup F a') R ∧
      (T : Subgroup (graphLocalGroup F w.val)).map (graphLocalGroup F w.val).subtype =
        (stabilizer F w.val ⊓ stabilizer F a').pCoreIn 2 ∧
      ⁅V F beta 1 ⊓ Q F a',Z F w.val⁆ ≠ ⊥ ∧
      W ⊓ Q F a' ≤ quotientSylowOmegaPreimage (graphLocalGroup F w.val) T ∧
      ⁅W ⊓ Q F a',Z F w.val⁆ ≤ H ∧
      ((V F beta 1).subgroupOf W).Normal ∧
      (((W ⊓ Q F a') ⊔ V F beta 1).subgroupOf W).Normal ∧
      ((W ⊓ Q F a') ⊔ V F beta 1).relIndex W <
        Nat.card (omegaCenterIn ((R : Subgroup (graphLocalGroup F a')).map
          (QuotientGroup.mk' (pCore 2 (graphLocalGroup F a'))))) := by
  obtain ⟨prev,R,hprev,_,hWprev,hR,hWO,hVN,hDN,hi⟩ :=
    reduced_radius_three_section_index h hob models hc hab hd (by omega) hcomm hne
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  obtain ⟨w,hm,_⟩ := exists_moving_neighbor F (fun v => (source_Z_Q_U ht v).1) beta a' hne
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow ht (Reduction.reduced_borel_core_sylow h)
    d w.property.symm
  obtain ⟨hI,hcommI⟩ := reduced_moving_radius_three_intersection_bound h hob models hc hab hd
    (by omega) hcomm w hm T hT (Or.inl hb)
  exact ⟨prev,R,w,T,hprev,hWprev,hR,hWO,hT,hm,hI,hcommI,hVN,hDN,hi⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
