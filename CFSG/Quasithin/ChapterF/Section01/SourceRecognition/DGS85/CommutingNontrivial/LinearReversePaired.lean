module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LinearUniformPaired
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.Transport

/-!
# The reverse linear comparison in the original 8.3 failure branch

Translate the reverse critical configuration of 8.2 to end at the original
ending vertex. Its full-neighborhood actor acts on the original nonnatural
residual representation. The uniform estimate therefore gives the reverse
inequality using the original failure, without selecting a reverse failure.
Transporting the two original core indices back gives exactly 8.3(2).

Source: DGS85, Groups and Graphs, proof of (8.3), printed p.136.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.NormalElementaryQuotient Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph CommutingTrivial
universe u
variable {G : Type u} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

theorem reduced_counterexample_linear_paired_square
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
        (stabilizer (Reduction.reducedFamily J S₀) w.val ⊓ stabilizer (Reduction.reducedFamily J S₀) a').pCoreIn 2)
    (hbad : ¬ ⁅quotientSylowOmegaPreimage (graphLocalGroup (Reduction.reducedFamily J S₀) w.val) R,
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≤
        ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
          V (Reduction.reducedFamily J S₀) a' 1⁆)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≃* SL(2,K))
    (m : ℕ) (hm2 : 2 ≤ m)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) 3 (2^m) ∨
      IsSU (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) 3 (2^m)) :
    let F := Reduction.reducedFamily J S₀
    Nat.pow ((Q F a').relIndex (V F beta 1)) 2 ≤ (Q F beta).relIndex (V F a' 1) * 2^m ∧
      Nat.pow ((Q F beta).relIndex (V F a' 1)) 2 ≤ (Q F a').relIndex (V F beta 1) * 2^m := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let : ∀ i, Finite (F i) := finite_endpoints ht
  have hfirst := reduced_counterexample_linear_uniform_paired_square h hob models hc hab hd hb hcomm
    w hm R hR hbad hn hK e hc hab hd hcomm m hm2 hu
  have hne : ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ ≠ ⊥ := by
    intro hz
    exact hm (bot_unique ((commutator_mono le_rfl (Z_neighbor_le_V F w.property)).trans hz.le))
  obtain ⟨_,z,hz,hzc,hd',hzcomm,_⟩ := reduced_reciprocal_critical_configuration h hob models
    hc hab hd hb hcomm hne
  have heven : Even ((graph F).dist beta a') := by
    obtain ⟨r,hr⟩ := (source_critical_geometry ht d hc hab hd hb hcomm).1
    change b F = 2*r+1 at hr
    change (graph F).dist beta a' + 1 = b F at hd
    refine ⟨r,?_⟩
    have he : (graph F).dist beta a' = 2*r := Nat.add_right_cancel (hd.trans hr)
    simpa only [two_mul] using he
  obtain ⟨g,hg⟩ := (same_orbit_iff F beta a').mpr ((even_dist_iff F ht.generate beta a').mp heven)
  have hgc := criticalPair_translate F hzc g
  rw [hg] at hgc
  have hgg : (graph F).Adj (g • z) (g • a') := by
    apply SimpleGraph.dist_eq_one_iff_adj.mp
    rw [Subgroup.CosetGeometry.RankTwo.dist_smul]
    exact SimpleGraph.dist_eq_one_iff_adj.mpr hz
  have hgd : (graph F).dist (g • a') (g • beta) + 1 = b F := by
    rw [Subgroup.CosetGeometry.RankTwo.dist_smul]
    exact hd'
  rw [hg] at hgd
  have hgcomm : ⁅Z F (g • z),Z F (g • beta)⁆ = ⊥ := by
    rw [commuting_centers_translate,hzcomm,Subgroup.map_bot]
  rw [hg] at hgcomm
  have hsecond := reduced_counterexample_linear_uniform_paired_square h hob models hc hab hd hb hcomm
    w hm R hR hbad hn hK e hgc hgg hgd hgcomm m hm2 hu
  have hindex₁ : (Q F a').relIndex (V F (g • a') 1) = (Q F beta).relIndex (V F a' 1) := by
    calc
      _ = (Q F (g • beta)).relIndex (V F (g • a') 1) := by rw [hg]
      _ = _ := by rw [Q_translate,V_translate,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  have hindex₂ : (Q F (g • a')).relIndex (V F a' 1) = (Q F a').relIndex (V F beta 1) := by
    calc
      _ = (Q F (g • a')).relIndex (V F (g • beta) 1) := by rw [hg]
      _ = _ := by rw [Q_translate,V_translate,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  change (Q F a').relIndex (V F (g • a') 1)^2 ≤ (Q F (g • a')).relIndex (V F a' 1) * 2^m at hsecond
  rw [hindex₁,hindex₂] at hsecond
  exact ⟨hfirst,hsecond⟩

/-- The large-field linear ending satisfies 8.3 at the original specified
moving neighbor. Both estimates are constructed inside its failure branch. -/
theorem reduced_linear_moving_omega_commutator
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
        (stabilizer (Reduction.reducedFamily J S₀) w.val ⊓ stabilizer (Reduction.reducedFamily J S₀) a').pCoreIn 2)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≃* SL(2,K)) :
    ⁅quotientSylowOmegaPreimage (graphLocalGroup (Reduction.reducedFamily J S₀) w.val) R,
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≤
        ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
          V (Reduction.reducedFamily J S₀) a' 1⁆ := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedEarlierLocalTheorems h hob
  by_contra hbad
  apply hbad
  apply source_omega_commutator_of_paired_indices ht (Reduction.reduced_borel_core_sylow h)
    d hc hab hd hb hcomm models w hm R hR
  intro m hm2 hu
  exact reduced_counterexample_linear_paired_square h hob models hc hab hd hb hcomm
    w hm R hR hbad hn hK e m hm2 hu

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
