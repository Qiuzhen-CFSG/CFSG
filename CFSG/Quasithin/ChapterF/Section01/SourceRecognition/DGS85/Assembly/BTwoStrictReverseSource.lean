module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictReverseSixPath

/-!
# Source reverse six-path regularity

The transported Cartan subgroup fixes the entire reverse six-path and
supplements the last edge two-core.  The symmetric residual is the
intersection of four source cores.  These facts discharge the conditional
inputs of the reverse path action theorem, including its endpoint model.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(10.8) and the strict branch of (10.10), printed pp.160--164.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Theory.GroupAction.CubicTree
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Reduction Noncommuting NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))
local notation "α" => base F false
local notation "β" => base F true

/-- The strict reverse six-path is right-regular under the original source
hypotheses.  Its Cartan supplement and all residual core containments are
provided by the symmetric source construction. -/
theorem original_bTwo_reverse_six_path_rightRegular_of_source_linear
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β)
    (hns : ¬ Group.IsSolvable (parabolic L S 0)) :
    ∃ g : G₀ L S, g ∈ graphLocalGroup F u ∧ g • β = y ∧
      ∃ p : BasedWalk (graph F) 6 (g • t),
        p.Nonbacktracking ∧ RightRegular (A := G₀ L S) p := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  obtain ⟨g, hg, hgy, hR, hRne, hRzero, K, hgK, hKall, hKgen⟩ :=
    original_bTwo_reverse_residual_four_core_cartan h hc hne hb hβu ht htne hy hyne hns
  let p : BasedWalk (graph F) 6 (g • t) := reversePath g hgy hβu ht hy
  have hKp : K ≤ pathStabilizer F p := by
    intro z hz w hw
    rw [show p.vertices = [g • t, g • α, y, u, β, α, t] from
      reversePath_vertices g hgy hβu ht hy] at hw
    have hz' := hKall hz
    simp only [mem_inf] at hz'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hz'.1.1.1.1.1.1
    · exact hz'.1.1.1.1.1.2
    · exact hz'.1.1.1.1.2
    · exact hz'.1.1.1.2
    · exact hz'.1.1.2
    · exact hz'.1.2
    · exact hz'.2
  have hgenp : pathStabilizer F p ⊔
      (stabilizer F p.endpoint ⊓ stabilizer F p.penultimate).pCoreIn 2 =
      stabilizer F p.endpoint ⊓ stabilizer F p.penultimate := by
    have hpE : p.endpoint = t := reversePath_endpoint g hgy hβu ht hy
    have hpP : p.penultimate = α := reversePath_penultimate g hgy hβu ht hy
    rw [hpE, hpP]
    have hTmem : t ∈ p.vertices := by
      rw [show p.vertices = [g • t, g • α, y, u, β, α, t] from
        reversePath_vertices g hgy hβu ht hy]
      simp
    have hAmem : α ∈ p.vertices := by
      rw [show p.vertices = [g • t, g • α, y, u, β, α, t] from
        reversePath_vertices g hgy hβu ht hy]
      simp
    apply le_antisymm
      (sup_le (pathStabilizer_le_edge F p hTmem hAmem) (pCoreIn_le _ _))
    exact hKgen.symm.le.trans (sup_le_sup_right hKp _)
  let R := bTwoResidual F β y α (g • α)
  have hRbeta : R ≤ Q F β := by
    rw [show R = (D F β y ⊓ Q F α) ⊓ Q F (g • α) from hR]
    exact (inf_le_left.trans inf_le_left).trans inf_le_left
  have hRy : R ≤ Q F y := by
    rw [show R = (D F β y ⊓ Q F α) ⊓ Q F (g • α) from hR]
    exact (inf_le_left.trans inf_le_left).trans inf_le_right
  have hRalpha : R ≤ Q F α := by
    rw [show R = (D F β y ⊓ Q F α) ⊓ Q F (g • α) from hR]
    exact inf_le_left.trans inf_le_right
  have hRga : R ≤ Q F (g • α) := by
    rw [show R = (D F β y ⊓ Q F α) ⊓ Q F (g • α) from hR]
    exact inf_le_right
  obtain ⟨q, hq, hqr⟩ :=
    reverse_six_path_rightRegular_of_source_linear h hc hne hb hβu ht htne hy hyne
      hg hgy (R := R) rfl hRne hRzero hRbeta hRy hRalpha hRga
      ((isPGroup_pCoreIn 2 (stabilizer F β)).to_le hRbeta) hgenp
  exact ⟨g, hg, hgy, q, hq, hqr⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
