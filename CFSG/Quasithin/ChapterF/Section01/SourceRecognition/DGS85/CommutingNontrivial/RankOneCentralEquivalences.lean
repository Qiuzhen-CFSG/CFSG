module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CentralIntersectionNatural
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NaturalBranch
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.DistanceSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReorientedConfiguration

/-!
# The rank-one 8.6 equivalence package

This extension packages the already proved distance-three, neighbor-exchange, and
natural-start arguments. For a terminal quotient of two-rank one it gives the
full (a)--(d) equivalence of DGS 8.6, with the literal centers, commutators,
and conjugation maps. It also discharges the corresponding Chapter 9 reverse
displacement callback.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

theorem reduced_rank_one_terminal_intersection_natural
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    (hr : primeRank 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≤ 1)
    (hinter : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1 ⊓ Q (Reduction.reducedFamily J S₀) beta⁆ = ⊥) :
    let F := Reduction.reducedFamily J S₀
    b F = 3 ∧ ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ = Z F a' ∧
      Noncommuting.HasNaturalCenter (graphLocalGroup F a) (Z F a) (Q F a) := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (F i) := finite_endpoints ht
  obtain ⟨w,hm,_⟩ := exists_moving_neighbor F (fun v => (source_Z_Q_U ht v).1) beta a' hne
  obtain ⟨hn,he⟩ := source_rank_one_terminal_commuting_intersection_natural ht
    (Reduction.reduced_borel_core_sylow h) d models hc hab hd hb hcomm w hm hinter hr
  have hb3 := reduced_distance_three_of_catalogue h models hc hab hd hb hcomm hne
  have hodd : Odd ((graph F).dist a a') := by rw [hc.1,hb3]; decide
  have hna : a.type ≠ a'.type := (odd_dist_iff F ht.generate a a').mp hodd
  have hnw : a'.type ≠ w.val.type := w.property.1
  have hwa : w.val.type = a.type := by
    cases hw : w.val.type <;> cases ha : a.type <;> cases ha' : a'.type <;> simp_all
  exact ⟨hb3,he,source_natural_center_of_type ht d hwa hn⟩

theorem reduced_rank_one_terminal_central_equivalences
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    (hr : primeRank 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≤ 1) :
    let F := Reduction.reducedFamily J S₀
    let H := ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆
    let I := ⁅V F beta 1 ⊓ Q F a',V F a' 1 ⊓ Q F beta⁆ = ⊥
    let N := Noncommuting.HasNaturalCenter (graphLocalGroup F a) (Z F a) (Q F a)
    b F = 3 ∧ ∃ mid : Vertex F,
      (graph F).Adj beta mid ∧ (graph F).Adj a' mid ∧
      let D := ∀ g : Reduction.G₀ J S₀, g ∈ stabilizer F mid → g ∉ stabilizer F a' →
        Disjoint H (H.map (MulAut.conj g).toMonoidHom)
      ((H ≤ Z F a') ↔ D) ∧ (D ↔ I) ∧ (I ↔ N) ∧ (N ↔ H = Z F a') := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (F i) := finite_endpoints ht
  have hb3 := reduced_distance_three_of_catalogue h models hc hab hd hb hcomm hne
  have hba : beta ≠ a' := by
    intro he
    rw [he,SimpleGraph.dist_self,hb3] at hd
    omega
  obtain ⟨mid,ham,hdm⟩ := exists_predecessor F ht.generate beta a' hba
  have hdist : (graph F).dist beta a' + 1 = 3 := hd.trans hb3
  have hbm : (graph F).Adj beta mid := SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
  let H := ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆
  let I := ⁅V F beta 1 ⊓ Q F a',V F a' 1 ⊓ Q F beta⁆ = ⊥
  let N := Noncommuting.HasNaturalCenter (graphLocalGroup F a) (Z F a) (Q F a)
  let D := ∀ g : Reduction.G₀ J S₀, g ∈ stabilizer F mid → g ∉ stabilizer F a' →
    Disjoint H (H.map (MulAut.conj g).toMonoidHom)
  have hcentral := critical_end_center_of_commuting F ht.generate
    (fun v => (source_Z_Q_U ht v).1) (fun v => (source_Z_Q_U ht v).2)
    hc hcomm (d.localGroup a') (d.sylow_or_center a')
  have hAD : H ≤ Z F a' → D := fun hH g hg he =>
    source_central_subgroup_disjoint_conjugate ht (Reduction.reduced_borel_core_sylow h)
      d ham.symm (models mid) hcentral H hH g hg he
  have hDI : D → I := source_disjoint_conjugates_intersection_commutes ht
    (Reduction.reduced_borel_core_sylow h) d hbm ham hba (models mid)
  have hIN : I → N := fun hi =>
    (reduced_rank_one_terminal_intersection_natural h models hc hab hd hb hcomm hne hr hi).2.2
  have hNE : N → H = Z F a' := source_natural_center_commutator_eq_terminal ht
    (Reduction.reduced_borel_core_sylow h) d hc hab hd hb hcomm hne
  have hNA : N → H ≤ Z F a' := fun hn => (hNE hn).le
  exact ⟨hb3,mid,hbm,ham,⟨hAD,fun hd => hNA (hIN (hDI hd))⟩,
    ⟨hDI,fun hi => hAD (hNA (hIN hi))⟩,
    ⟨hIN,fun hn => hDI (hAD (hNA hn))⟩,
    ⟨hNE,fun he => hIN (hDI (hAD he.le))⟩⟩

theorem reduced_reverse_displacement_of_rank_one_terminal
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ = ⊥)
    (he : ¬ V (Reduction.reducedFamily J S₀) a' 1 ≤ Q (Reduction.reducedFamily J S₀) beta)
    (hr : primeRank 2 (graphLocalGroup (Reduction.reducedFamily J S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) beta)) ≤ 1) :
    let F := Reduction.reducedFamily J S₀
    ⁅V F a' 1 ⊓ Q F beta,V F beta 1⁆ = ⊥ := by
  let F := Reduction.reducedFamily J S₀
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  apply CommutingTrivial.reduced_reverse_displacement_of_chapterEight h hc hab hd hb hcomm htriv he
  intro z hz hzc hzcomm hrev
  have hd' : (graph F).dist a' beta + 1 = b F := by rwa [SimpleGraph.dist_comm]
  have hi : ⁅V F a' 1 ⊓ Q F beta,V F beta 1 ⊓ Q F a'⁆ = ⊥ := by
    rw [commutator_comm]
    exact bot_unique ((commutator_mono le_rfl inf_le_left).trans htriv.le)
  obtain ⟨hb3,_,hn⟩ := reduced_rank_one_terminal_intersection_natural h models hzc hz hd'
    hb hzcomm hrev hr hi
  obtain ⟨K,_,_,_,heK⟩ := source_natural_center_linear_quotient ht d z hn
  exact ⟨K,inferInstance,inferInstance,inferInstance,hb3,heK⟩

/-! The parameter equality in 8.7 is the literal quotient-Sylow equality
from the reduced completion.  Combining it with the rank-one 8.6 branch records
the same-type parameter transport. The adjacent equality q_alpha = q_beta
in 8.7 and the unconditional centrality conclusion remain separate. -/

theorem reduced_rank_one_terminal_eight_seven
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    (hr : primeRank 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≤ 1)
    (hinter : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1 ⊓ Q (Reduction.reducedFamily J S₀) beta⁆ = ⊥) :
    let F := Reduction.reducedFamily J S₀
    let H := ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆
    b F = 3 ∧ H = Z F a' ∧
      ∀ (T : Sylow 2 (graphLocalGroup F a' ⧸ pCore 2 (graphLocalGroup F a')))
        (R : Sylow 2 (graphLocalGroup F beta ⧸ pCore 2 (graphLocalGroup F beta))),
        Nat.card (omegaCenterIn (T : Subgroup (graphLocalGroup F a' ⧸
          pCore 2 (graphLocalGroup F a')))) =
        Nat.card (omegaCenterIn (R : Subgroup (graphLocalGroup F beta ⧸
          pCore 2 (graphLocalGroup F beta)))) := by
  let F := Reduction.reducedFamily J S₀
  obtain ⟨hb3,hH,_⟩ := reduced_rank_one_terminal_intersection_natural h models hc hab hd hb hcomm hne hr hinter
  obtain ⟨g,e,f,hg,he,hf,hparam⟩ :=
    CommutingTrivial.reduced_critical_parameter_transport h hc hab hd hb hcomm
  exact ⟨hb3,hH, hparam⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
