module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SecondKernelLayer

/-!
# Second-kernel control at every neighbor of a natural center

The natural center at the fixed base vertex detects the action of each
neighbor core placed in its starred group. Normality propagates this
control around the neighbor's first ball. The reverse containment uses
the actual kernel Sylow theorem at every vertex. Consequently the core
centralizer of the neighbor span is its intersection with the full
second kernel, for arbitrary neighbors rather than only the base edge.

SuzukiIntersectionKernels applies this to the original source spans.
The natural center and common-Sylow placement remain earlier (12.1)
inputs. No equality between the full kernel and its two-core is imposed.
Source: DGS85, Groups and Graphs, (6.2)(d), (12.1), (12.6), (12.8),
printed pp.119,178,183,185.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The actual neighbor core centralizer uses the full second-ball denominator. -/
theorem source_neighbor_core_span_centralizer (h : HypothesisF11 L S) (i : Bool)
    {x : Vertex (reducedFamily L S)}
    (hx : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) i))
    (hplace : Q (reducedFamily L S) x ≤ ReducedLayer.star L S i)
    (hnat : Noncommuting.HasNaturalCenter (ReducedLayer.star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i))) :
    let F := reducedFamily L S
    Q F x ⊓ centralizer (V F x 1 : Set (G₀ L S)) = Q F x ⊓ ballKernel F x 2 := by
  let F := reducedFamily L S
  let v := x
  let w := base F i
  let C := Q F v ⊓ centralizer (V F v 1 : Set (G₀ L S))
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hadj : (graph F).Adj v w := hx
  have hZ := fun z => (source_Z_Q_U (reduced_triple h) z).1
  have hQU := fun z => (source_Z_Q_U (reduced_triple h) z).2
  have hn : stabilizer F v ≤ normalizer (C : Set (G₀ L S)) :=
    (le_inf (CommutingTrivial.stabilizer_normalizes_Q F v)
      ((stabilizer_normalizes_V F v 1).trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hCv : C ≤ stabilizer F v := inf_le_left.trans (Q_le_stabilizer F v)
  have hCw : C ≤ Q F w := by
    intro x hx
    exact natural_center_centralizer_le_core _ _ _ hnat
      ⟨hplace hx.1, centralizer_le (Z_neighbor_le_V F hadj) hx.2⟩
  have hC2 : C ≤ ballKernel F v 2 := by
    let : (C.subgroupOf (stabilizer F v)).Normal :=
      (normal_subgroupOf_iff_le_normalizer hCv).mpr hn
    have hh : C.subgroupOf (stabilizer F v) ≤
        (ballKernel F v 2).subgroupOf (stabilizer F v) := by
      rw [ballKernel_two_eq_normalCore F hadj]
      apply normal_le_normalCore.mpr
      intro x hx
      exact ⟨hQU v hx.1, hQU w (hCw hx)⟩
    intro x hx
    exact hh (show (⟨x,hCv hx⟩ : stabilizer F v) ∈ C.subgroupOf (stabilizer F v) from hx)
  apply le_antisymm (le_inf inf_le_left hC2)
  have hp : IsPGroup 2 (Q F v ⊓ ballKernel F v 2 : Subgroup (G₀ L S)) :=
    (isPGroup_pCoreIn 2 _).to_le inf_le_left
  have hcw : ∀ z, (graph F).Adj v z → Q F v ⊓ ballKernel F v 2 ≤ Q F z := by
    intro z hz
    exact CommutingTrivial.two_subgroup_le_Q F z (reduced_kernel_sylow h z) hp
      (inf_le_right.trans (ballKernel_succ_le F hz 1))
  intro x hx
  refine ⟨hx.1,?_⟩
  have hc : V F v 1 ≤ centralizer ({x} : Set (G₀ L S)) := by
    apply iSup_le
    intro z
    apply iSup_le
    intro hz
    have hxz : x ∈ Q F z := by
      rcases (mem_ball_one F v z).mp hz with hz | rfl
      · exact hcw z hz hx
      · exact hx.1
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (Z_centralizes_Q F z (hZ z) ha x hxz).symm
  intro a ha
  exact mem_centralizer_singleton_iff.mp (hc ha)


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
