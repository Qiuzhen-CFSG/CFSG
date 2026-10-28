module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoCartanVanishing
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoCartanResidualOrder

/-!
# Residual order at the terminal edge

The path Cartan fixes both endpoints of the prescribed terminal edge.  Its
odd complement therefore remains a full edge complement there.  The residual
lies in the preceding vertex core, hence in the terminal edge two-core, while
its trivial terminal-core intersection supplies the disjointness needed by
the normalized SL₂ quotient calculation.  The resulting complement has the
coefficient-field order.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Reduction Noncommuting NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))
local notation "α" => base F false
local notation "β" => base F true

/-- The same odd Cartan complement computes the order of the path residual at
its terminal edge. -/
theorem path_cartan_residual_card
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hy : (graph F).Adj u y)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    {K R : Subgroup (G₀ L S)}
    (hfix : K ≤ stabilizer F t ⊓ stabilizer F α ⊓ stabilizer F β ⊓
      stabilizer F u ⊓ stabilizer F y)
    (hd : Disjoint K ((stabilizer F α ⊓ stabilizer F β).pCoreIn 2))
    (hgen : K ⊔ (stabilizer F α ⊓ stabilizer F β).pCoreIn 2 =
      stabilizer F α ⊓ stabilizer F β)
    (ho : Odd (Nat.card K))
    (g : G₀ L S)
    (hR : R = (D F β t ⊓ Q F u) ⊓ Q F (g • u))
    (hRne : R ≠ ⊥) (hzero : Disjoint R (Q F y))
    (hn : K ≤ normalizer (R : Set (G₀ L S)))
    (e : (graphLocalGroup F y ⧸ pCore 2 (graphLocalGroup F y)) ≃*
      SL(2,k)) : Nat.card R = Nat.card k := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide, Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hB := reduced_borel_core_sylow h
  have hS := reduced_vertex_sylow h
  have hKuy : K ≤ stabilizer F u ⊓ stabilizer F y := by
    exact le_inf (fun k hk => (hfix hk).1.2) (fun k hk => (hfix hk).2)
  have hKE : K ≤ stabilizer F α ⊓ stabilizer F β := by
    exact le_inf (fun k hk => (hfix hk).1.1.1.2) (fun k hk => (hfix hk).1.1.2)
  obtain ⟨hdy,hgeny⟩ := CommutingTrivial.path_cartan_complement_at_edge H hab hy.symm K
    hKE (by simpa only [inf_comm] using hKuy) ho hd hgen
  have hRu : R ≤ Q F u := by
    rw [hR]
    exact inf_le_left.trans inf_le_right
  have hAS : R ≤ (stabilizer F y ⊓ stabilizer F u).pCoreIn 2 := by
    exact hRu.trans (by simpa only [inf_comm] using graph_Q_le_edgeCore H hy)
  have hRbeta : R ≤ Q F β := by
    rw [hR]
    exact (inf_le_left.trans inf_le_left).trans inf_le_left
  have hRtwo : IsPGroup 2 R :=
    (isPGroup_pCoreIn 2 (stabilizer F β)).of_injective
      (inclusion hRbeta) (inclusion_injective _)
  exact (cartan_normalized_disjoint_two_subgroup_card H hB hS hy.symm e K R
    (by simpa only [inf_comm] using hKuy) hdy hgeny hAS hRtwo hn hRne hzero).2

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
