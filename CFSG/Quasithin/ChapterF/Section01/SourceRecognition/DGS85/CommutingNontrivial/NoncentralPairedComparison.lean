module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NoncentralOmegaActor
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NoncentralParameterComparison
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NeighborExchange

/-!
# The paired original core indices in DGS 8.7

An element of the middle local group exchanges the two endpoints of a
two-edge path. Conjugating both the neighborhood span and the opposite core
therefore identifies the two literal actor indices. At critical distance
three this converts the known opposite omega image into the corresponding
terminal omega index, without a reverse-displacement or naturality premise.

The unitary ending comparison then bounds the common index by the moving
binary parameter. This supplies the parameter comparison used before the
fixed-centralizer escape on printed p.140; it does not assert that escape.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
8.6--8.7, printed pp.139--140.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G]

/-- A literal exchange of two neighbors identifies their opposite core
indices, for every retained middle quotient model. -/
theorem source_two_edge_core_indices_eq
    {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {beta mid a' : Vertex (family P)}
    (hbm : (graph (family P)).Adj beta mid)
    (ham : (graph (family P)).Adj a' mid)
    (M : IsRankOneModel (d.localGroup mid ⧸ pCore 2 (d.localGroup mid))) :
    (Q (family P) a').relIndex (V (family P) beta 1) =
      (Q (family P) beta).relIndex (V (family P) a' 1) := by
  let := finite_endpoints h
  obtain ⟨g, _, hgb, hga⟩ :=
    source_rank_one_neighbor_exchange h hB d hbm.symm ham.symm M
  have he := relIndex_map_map_of_injective
    (f := (MulAut.conj g).toMonoidHom)
    (Q (family P) a') (V (family P) beta 1) (MulAut.conj g).injective
  rw [← Q_translate, ← V_translate, hga, hgb] at he
  exact he.symm

variable {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "Γ" => Reduction.reducedFamily L S₀

/-- In the original nontrivial commuting configuration, the two opposite
actor indices agree. The catalogue supplies distance three. -/
theorem reduced_critical_paired_core_indices_eq
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a, Z Γ a'⁆ = ⊥)
    (hne : ⁅V Γ beta 1 ⊓ Q Γ a', V Γ a' 1⁆ ≠ ⊥) :
    (Q Γ a').relIndex (V Γ beta 1) =
      (Q Γ beta).relIndex (V Γ a' 1) := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  have hb3 := reduced_distance_three_of_catalogue h models hc hab hd hb hcomm hne
  obtain ⟨_, _, _, _, mid, ham, hdm, _, _⟩ :=
    source_critical_geometry ht d hc hab hd hb hcomm
  change (graph Γ).dist beta mid + 1 = (graph Γ).dist beta a' at hdm
  change (graph Γ).Adj a' mid at ham
  have hbm : (graph Γ).Adj beta mid :=
    SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
  exact source_two_edge_core_indices_eq ht (Reduction.reduced_borel_core_sylow h)
    d hbm ham (models mid)

/-- Both original core indices equal the actual beta quotient omega order
when the starting type is non-dihedral. No condition from 8.6 is assumed. -/
theorem reduced_noncentral_paired_omega_indices
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a, Z Γ a'⁆ = ⊥)
    (hne : ⁅V Γ beta 1 ⊓ Q Γ a', V Γ a' 1⁆ ≠ ⊥)
    (hnd : ¬ Nonempty ((graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)) ≃*
      DihedralGroup 5))
    (Rβ : Sylow 2 (graphLocalGroup Γ beta)) :
    let qβ := Nat.card (omegaCenterIn
      ((Rβ : Subgroup (graphLocalGroup Γ beta)).map
        (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ beta)))))
    (Q Γ a').relIndex (V Γ beta 1) = qβ ∧
      (Q Γ beta).relIndex (V Γ a' 1) = qβ := by
  have hβ := reduced_noncentral_opposite_omega_index_of
    h models hc hab hd hb hcomm hne hnd Rβ
  exact ⟨(reduced_critical_paired_core_indices_eq h models hc hab hd hb hcomm hne).trans hβ,
    hβ⟩

/-- The actual first two core indices satisfy the moving-parameter upper
bound in the large-unitary terminal branch. The original paired square
estimate supplies the bound; the exchange discharges its opposite index. -/
theorem reduced_noncentral_unitary_paired_index_le
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a, Z Γ a'⁆ = ⊥)
    (hne : ⁅V Γ beta 1 ⊓ Q Γ a', V Γ a' 1⁆ ≠ ⊥)
    {k m : ℕ} (hk : 2 ≤ k) (hm : 2 ≤ m)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ a' ⧸
        pCore 2 (graphLocalGroup Γ a')) 3 (2 ^ k) ∨
      IsSU (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a')) 3 (2 ^ k))
    (w : (graph Γ).neighborSet a')
    (hmove : ⁅V Γ beta 1 ⊓ Q Γ a', Z Γ w.val⁆ ≠ ⊥)
    (hrw : primeRank 2 (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) ≤ m) :
    (Q Γ a').relIndex (V Γ beta 1) ≤ 2 ^ m ∧
      (Q Γ beta).relIndex (V Γ a' 1) ≤ 2 ^ m := by
  have hpair := reduced_noncentral_unitary_first_comparisons h
    (Reduction.reduced_graph_core_obstruction h) models hc hab hd hb hcomm hne
    hk hm hu w hmove hrw
  have he := reduced_critical_paired_core_indices_eq h models hc hab hd hb hcomm hne
  have hs := hpair.1
  rw [he] at hs
  have hle : (Q Γ beta).relIndex (V Γ a' 1) ≤ 2 ^ m := by
    by_cases hz : (Q Γ beta).relIndex (V Γ a' 1) = 0
    · simp only [hz, Nat.zero_le]
    · exact Nat.le_of_mul_le_mul_left (by simpa only [pow_two] using hs)
        (Nat.pos_of_ne_zero hz)
  exact ⟨he.le.trans hle, hle⟩

/-- The literal beta quotient omega parameter is at most the moving
parameter in the same noncentral large-unitary ending configuration. -/
theorem reduced_noncentral_unitary_beta_parameter_le
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a, Z Γ a'⁆ = ⊥)
    (hne : ⁅V Γ beta 1 ⊓ Q Γ a', V Γ a' 1⁆ ≠ ⊥)
    (hnd : ¬ Nonempty ((graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)) ≃*
      DihedralGroup 5))
    {k m : ℕ} (hk : 2 ≤ k) (hm : 2 ≤ m)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ a' ⧸
        pCore 2 (graphLocalGroup Γ a')) 3 (2 ^ k) ∨
      IsSU (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a')) 3 (2 ^ k))
    (w : (graph Γ).neighborSet a')
    (hmove : ⁅V Γ beta 1 ⊓ Q Γ a', Z Γ w.val⁆ ≠ ⊥)
    (hrw : primeRank 2 (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) ≤ m)
    (Rβ : Sylow 2 (graphLocalGroup Γ beta)) :
    Nat.card (omegaCenterIn ((Rβ : Subgroup (graphLocalGroup Γ beta)).map
      (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ beta))))) ≤ 2 ^ m := by
  rw [← (reduced_noncentral_paired_omega_indices h models hc hab hd hb hcomm hne hnd Rβ).1]
  exact (reduced_noncentral_unitary_paired_index_le
    h models hc hab hd hb hcomm hne hk hm hu w hmove hrw).1

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
