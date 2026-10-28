module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LinearCentralSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NonlinearCentralSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NaturalBranch
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.DistanceSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReorientedConfiguration

/-!
# All four source conditions of DGS 8.6

The complete retained catalogue closes the commuting-intersection implication:
linear quotients use the natural residual exclusion, nonlinear quotients use
their residual square bounds, and the small rows use two-rank one. Thus
8.6(c) forces the actual starting center to be natural and H to equal the
terminal center. The geometric disjointness implications give all four
equivalences, with the original conjugation maps.

The final application discharges the actual reverse-displacement premise of
Chapter 9. It requires neither a model marking nor an earlier Chapter 8
callback. Unconditional centrality and adjacent parameter equality in 8.7
remain separate conclusions.
Source: DGS, *Groups and Graphs* (1985), 8.6 and 9.2, pp.139–142.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

theorem reduced_terminal_intersection_natural
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
    (hinter : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1 ⊓ Q (Reduction.reducedFamily J S₀) beta⁆ = ⊥) :
    let F := Reduction.reducedFamily J S₀
    b F = 3 ∧ ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ = Z F a' ∧
      Noncommuting.HasNaturalCenter (graphLocalGroup F a) (Z F a) (Q F a) := by
  classical
  let Γ := Reduction.reducedFamily J S₀
  by_cases hlin : ∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL
      (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) 2 (2^n)
  · obtain ⟨n,hn,K,_,_,hK,⟨eK⟩⟩ := hlin
    let := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hK)
    let e := eK.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
    exact reduced_linear_terminal_intersection_natural h models hc hab hd hb hcomm hne hinter e
  · have hnlin : ∀ n : ℕ, 0 < n → ¬ ClassicalGroup.IsPSL
        (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) 2 (2^n) :=
      fun n hn he => hlin ⟨n,hn,he⟩
    obtain ⟨hnat,hH⟩ := reduced_nonlinear_terminal_commuting_intersection_natural
      h models hc hab hd hb hcomm hne hnlin hinter
    exact ⟨reduced_distance_three_of_catalogue h models hc hab hd hb hcomm hne,hH,hnat⟩


theorem reduced_critical_central_equivalences
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
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥) :
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
    (reduced_terminal_intersection_natural h models hc hab hd hb hcomm hne hi).2.2
  have hNE : N → H = Z F a' := source_natural_center_commutator_eq_terminal ht
    (Reduction.reduced_borel_core_sylow h) d hc hab hd hb hcomm hne
  have hNA : N → H ≤ Z F a' := fun hn => (hNE hn).le
  exact ⟨hb3,mid,hbm,ham,⟨hAD,fun hd => hNA (hIN (hDI hd))⟩,
    ⟨hDI,fun hi => hAD (hNA (hIN hi))⟩,
    ⟨hIN,fun hn => hDI (hAD (hNA hn))⟩,
    ⟨hNE,fun he => hIN (hDI (hAD he.le))⟩⟩

theorem reduced_reverse_displacement_of_catalogue
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
    (he : ¬ V (Reduction.reducedFamily J S₀) a' 1 ≤ Q (Reduction.reducedFamily J S₀) beta) :
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
  obtain ⟨hb3,_,hn⟩ := reduced_terminal_intersection_natural h models hzc hz hd'
    hb hzcomm hrev hi
  obtain ⟨K,_,_,_,heK⟩ := source_natural_center_linear_quotient ht d z hn
  exact ⟨K,inferInstance,inferInstance,inferInstance,hb3,heK⟩


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
