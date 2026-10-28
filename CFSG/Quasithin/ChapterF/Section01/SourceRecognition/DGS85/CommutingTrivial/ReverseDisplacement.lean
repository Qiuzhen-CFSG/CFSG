module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.LocalExchange
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReorientedConfiguration

/-!
# Source 9.2 and the reciprocal actors in the first case of 9.3

If reverse displacement were nontrivial, the previously selected reverse
critical pair satisfies Chapter 8. Its distance-three and actual SL₂
quotient conclusions transport to the middle vertex. The local matrix
exchange then swaps the original beta and alpha-prime. Conjugating the
assumed zero displacement contradicts the reverse nonzero displacement.
Both actual conjugation images consequently have the precise core kernels,
and their reciprocal indices force a strict square comparison.

The explicit h8 premise is the earlier 8.4/8.6 output owned by
qt-dgs85-critical-commuting-nontrivial; final source assembly must discharge
it. No distance-three conclusion for the Chapter 9 configuration is assumed.
Residual-section faithfulness, Sylow-fixed generation, natural recognition
and the later Chapter 9 bounds remain with this branch owner.

Source: DGS, *Groups and Graphs* (1985), 9.2--9.3, printed p.142.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G]
variable {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- Source 9.2 on the reduced graph, using exactly the earlier Chapter 8
distance and actual linear-quotient conclusions at the selected reverse pair.
The exchange and its original action are constructed here. -/
theorem reduced_reverse_displacement_of_chapterEight (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (he : ¬ V (Reduction.reducedFamily L S₀) a' 1 ≤ Q (Reduction.reducedFamily L S₀) beta)
    (h8 : ∀ z : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj z a' →
      IsCriticalPair (Reduction.reducedFamily L S₀) z beta →
      ⁅Z (Reduction.reducedFamily L S₀) z, Z (Reduction.reducedFamily L S₀) beta⁆ = ⊥ →
      ⁅V (Reduction.reducedFamily L S₀) a' 1 ⊓ Q (Reduction.reducedFamily L S₀) beta,
        V (Reduction.reducedFamily L S₀) beta 1⁆ ≠ ⊥ →
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        b (Reduction.reducedFamily L S₀) = 3 ∧
          Nonempty ((graphLocalGroup (Reduction.reducedFamily L S₀) z ⧸
            pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) z)) ≃* SL(2,F))) :
    ⁅V (Reduction.reducedFamily L S₀) a' 1 ⊓ Q (Reduction.reducedFamily L S₀) beta,
      V (Reduction.reducedFamily L S₀) beta 1⁆ = ⊥ := by
  by_contra hrev
  let ht := Reduction.reduced_triple h
  let F₀ := Reduction.reducedFamily L S₀
  let : ∀ i, Finite (F₀ i) := finite_endpoints ht
  obtain ⟨z, hz, hzc, _, hzcomm, _, _⟩ :=
    reduced_reverse_branch_configuration h hc hab hd hb hcomm he hrev
  obtain ⟨K, _, _, _, hb3, ⟨e⟩⟩ := h8 z hz hzc hzcomm hrev
  have hd₀ : (graph F₀).dist beta a' + 1 = b F₀ := hd
  have hb₀ : b F₀ = 3 := hb3
  have hdist : (graph F₀).dist beta a' = 2 := by omega
  have hne : beta ≠ a' := by
    intro heq
    rw [heq, SimpleGraph.dist_self] at hdist
    omega
  obtain ⟨m, hma', hdm⟩ := exists_predecessor F₀ ht.generate beta a' hne
  have hbm : (graph F₀).Adj beta m := SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
  have htypes : z.type = m.type := by
    have hzt := hz.1
    have hmt := hma'.1
    cases hz' : z.type <;> cases hm' : m.type <;> cases ha' : a'.type <;> simp_all
  obtain ⟨g, hg⟩ := (same_orbit_iff F₀ z m).mpr htypes
  obtain ⟨_, f, _, _, _⟩ := local_quotient_parameter_transport ht g hg
  obtain ⟨t, ht₁, ht₂, _⟩ := linear_local_neighbor_exchange ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    hbm.symm hma'.symm (f.symm.trans e)
  exact hrev (reduced_reverse_commutator_of_exchange h htriv t ht₁ ht₂)

/-- The first case of 9.3 now has both literal action kernels, nontrivial
quotient actors, exact core indices and a strict reciprocal square comparison.
The reverse displacement is discharged by the proved 9.2 exchange. -/
theorem reduced_large_neighbor_actions (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (he : ¬ V (Reduction.reducedFamily L S₀) a' 1 ≤ Q (Reduction.reducedFamily L S₀) beta)
    (h8 : ∀ z : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj z a' →
      IsCriticalPair (Reduction.reducedFamily L S₀) z beta →
      ⁅Z (Reduction.reducedFamily L S₀) z, Z (Reduction.reducedFamily L S₀) beta⁆ = ⊥ →
      ⁅V (Reduction.reducedFamily L S₀) a' 1 ⊓ Q (Reduction.reducedFamily L S₀) beta,
        V (Reduction.reducedFamily L S₀) beta 1⁆ ≠ ⊥ →
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        b (Reduction.reducedFamily L S₀) = 3 ∧
          Nonempty ((graphLocalGroup (Reduction.reducedFamily L S₀) z ⧸
            pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) z)) ≃* SL(2,F))) :
    let F := Reduction.reducedFamily L S₀
    let hd' : (graph F).dist a' beta + 1 ≤ b F := by
      rw [SimpleGraph.dist_comm]; exact hd.le
    let f := reduced_neighbor_action h beta a' hd.le
    let g := reduced_neighbor_action h a' beta hd'
    ⁅V F a' 1 ⊓ Q F beta, V F beta 1⁆ = ⊥ ∧
      f.ker = (Q F a').subgroupOf (V F beta 1) ∧
      g.ker = (Q F beta).subgroupOf (V F a' 1) ∧
      Nat.card f.range = (Q F a').relIndex (V F beta 1) ∧
      Nat.card g.range = (Q F beta).relIndex (V F a' 1) ∧
      1 < Nat.card f.range ∧ 1 < Nat.card g.range ∧
      ((centralizer (V F a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V F beta 1) <
          Nat.card g.range ^ 2 ∨
        (centralizer (V F beta 1 : Set (Reduction.G₀ L S₀))).relIndex (V F a' 1) <
          Nat.card f.range ^ 2) := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily L S₀
  let : ∀ i, Finite (F i) := finite_endpoints ht
  have hd' : (graph F).dist a' beta + 1 ≤ b F := by
    rw [SimpleGraph.dist_comm]
    exact hd.le
  have hrev := reduced_reverse_displacement_of_chapterEight h hc hab hd hb hcomm htriv he h8
  have he' : ¬ V F beta 1 ≤ Q F a' :=
    V_not_le_Q_of_criticalPair F hc hab.symm (source_Z_Q_U ht a').2
  exact ⟨hrev, reduced_neighbor_action_kernel h beta a' hb hd.le htriv,
    reduced_neighbor_action_kernel h a' beta hb hd' hrev,
    neighborAction_range_card ht (Reduction.reduced_kernel_sylow h) beta a' hb hd.le htriv,
    neighborAction_range_card ht (Reduction.reduced_kernel_sylow h) a' beta hb hd' hrev,
    reduced_neighbor_action_nontrivial h beta a' hb hd.le htriv he',
    reduced_neighbor_action_nontrivial h a' beta hb hd' hrev he,
    mutual_neighbor_strict_bound ht (Reduction.reduced_kernel_sylow h) beta a' hb hd.le htriv hrev he' he⟩
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
