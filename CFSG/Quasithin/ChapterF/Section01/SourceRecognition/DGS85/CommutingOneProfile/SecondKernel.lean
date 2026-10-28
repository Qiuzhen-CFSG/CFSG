module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.NeighborIntersection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.Neighborhood
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.KernelSylow
public import Theory.GroupAction.RankTwoCosetGeometry.SecondBallKernel

/-!
# The actual second-kernel radical behind the Chapter 11 intersection

The intersection I of all neighboring two-cores is normal in Gβ and lies
in Qβ. The relative normal-core description of the second ball therefore
puts I in Gβ^(2). Conversely any two-subgroup of that kernel lies in every
neighbor's first kernel; source (6.2)(d) puts it in the corresponding Qδ.
Thus I is precisely the embedded O₂(Gβ^(2)).

The reduced F1.11 application discharges every kernel-Sylow premise. This
connects the subgroup studied in (11.6) to the actual graph kernel used by
the later path analysis. Neither Gβ^(1) nor Gβ^(2) is equated to its radical.
Identifying I with Zβ and the odd length-five stabilizer conclusions remain
part of the Chapter 11 proof.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.6), printed p.172; (6.2)(d), p.119; closed-ball kernel conventions,
pp.71--75.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The neighboring-core intersection fixes the entire radius-two ball. -/
theorem source_neighborCoreIntersection_le_second_kernel
    (h : LocallyRankOneTriple P B) {a b : Vertex (family P)}
    (hab : (graph (family P)).Adj a b) :
    neighborCoreIntersection (family P) b ≤ ballKernel (family P) b 2 := by
  let I := neighborCoreIntersection (family P) b
  have hIQ : I ≤ Q (family P) b := source_neighborCoreIntersection_le_core h hab
  have hIM : I ≤ stabilizer (family P) b := hIQ.trans (Q_le_stabilizer _ b)
  let : (I.subgroupOf (stabilizer (family P) b)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hIM).mpr (neighborCoreIntersection_normalized _ b)
  have hn : I.subgroupOf (stabilizer (family P) b) ≤
      (ballKernel (family P) b 2).subgroupOf (stabilizer (family P) b) := by
    rw [ballKernel_two_eq_normalCore _ hab.symm]
    apply normal_le_normalCore.mpr
    intro x hx
    exact ⟨(source_Z_Q_U h b).2 (hIQ hx),
      (source_Z_Q_U h a).2 (neighborCoreIntersection_le (family P) hab hx)⟩
  intro x hx
  exact hn (show (⟨x,hIM hx⟩ : stabilizer (family P) b) ∈
    I.subgroupOf (stabilizer (family P) b) from hx)

/-- The intersection in (11.6) is the embedded two-core of the actual
radius-two kernel. The full radius-one kernels stay separate from Q. -/
theorem source_neighborCoreIntersection_eq_second_core
    (h : LocallyRankOneTriple P B)
    (hSyl : ∀ v, ∃ T : Sylow 2 (U (family P) v),
      (T : Subgroup (U (family P) v)).map (U (family P) v).subtype = Q (family P) v)
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b) :
    neighborCoreIntersection (family P) b = (ballKernel (family P) b 2).pCoreIn 2 := by
  let := finite_endpoints h
  apply le_antisymm
  · exact le_pCoreIn_of_normalizes
      ((isPGroup_pCoreIn 2 _).to_le (neighborCoreIntersection_le (family P) hab))
      (source_neighborCoreIntersection_le_second_kernel h hab)
      ((ballKernel_le_stabilizer _ _ _).trans (neighborCoreIntersection_normalized _ b))
  · change (ballKernel (family P) b 2).pCoreIn 2 ≤
      ⨅ c : (graph (family P)).neighborSet b, Q (family P) c.val
    apply le_iInf
    intro c
    exact CommutingTrivial.two_subgroup_le_Q (family P) c.val (hSyl c.val)
      (isPGroup_pCoreIn 2 _) ((pCoreIn_le 2 _).trans
        (ballKernel_succ_le (family P) c.property 1))

/-- On the original reduced graph, the kernel-Sylow premise is discharged. -/
theorem reduced_neighborCoreIntersection_eq_second_core
    {L : Fin 2 → Subgroup G} {S : Subgroup G} (h : HypothesisF11 L S)
    {a b : Vertex (Reduction.reducedFamily L S)}
    (hab : (graph (Reduction.reducedFamily L S)).Adj a b) :
    neighborCoreIntersection (Reduction.reducedFamily L S) b =
      (ballKernel (Reduction.reducedFamily L S) b 2).pCoreIn 2 :=
  source_neighborCoreIntersection_eq_second_core (Reduction.reduced_triple h)
    (Reduction.reduced_kernel_sylow h) hab

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
