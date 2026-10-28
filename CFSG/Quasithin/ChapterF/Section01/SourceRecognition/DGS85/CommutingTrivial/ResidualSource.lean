module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.LocalActor
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.Source

/-!
# The nonzero residual section on the actual reduced critical configuration

The source commuting geometry gives b ≥ 3. Kernel Sylow control and local
actor containment then construct V_beta/C_V_beta(O²(L_beta)), retaining
its literal coordinate kernel and conjugation. Two-perfectness supplies
zero residual fixed space. Local residual movement proves the quotient
nonzero, and the entire original opposite V is a quadratic actor.

These discharge section construction, nontriviality, residual fixed-space
vanishing and quadraticity in 9.3. Faithfulness, Sylow-fixed generation,
natural recognition and the later distance and field conclusions remain
Chapter 9 obligations.

Source: DGS, *Groups and Graphs* (1985), 9.1--9.3, pp.141--142.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.NormalElementaryQuotient
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The literal residual section at beta, with all earlier kernel, distance,
normality and nonzero-section premises discharged on the reduced source graph. -/
theorem reduced_critical_residual_section (h : HypothesisF11 L S)
    {a beta a' : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) a a')
    (hab : (graph (Reduction.reducedFamily L S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S)).dist beta a' + 1 = b (Reduction.reducedFamily L S))
    (hb : 1 < b (Reduction.reducedFamily L S))
    (hcomm : ⁅Z (Reduction.reducedFamily L S) a, Z (Reduction.reducedFamily L S) a'⁆ = ⊥) :
    let F := Reduction.reducedFamily L S
    let H := graphLocalGroup F beta
    let A := (V F beta 1).subgroupOf H
    letI : ∀ i, Finite (F i) := finite_endpoints (Reduction.reduced_triple h)
    letI := neighborhoodIn_normal F beta H (sylowGenerated_le _)
    ∃ hb2 : 2 < b F,
      letI := neighborhoodIn_elementary F (Reduction.reduced_triple h).generate
        (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
        (Reduction.reduced_kernel_sylow h) beta hb2 H
      Nontrivial (FixedQuotient A (pResidual 2 H)) ∧
      Nonempty (BinaryConjugationSection H (V F beta 1)
        (V F beta 1 ⊓ centralizer ((pResidual 2 H).map H.subtype : Set (Reduction.G₀ L S)))
        (fixedQuotientAction A (pResidual 2 H))) ∧
      fixedSpace (fixedQuotientAction A (pResidual 2 H)) (pResidual 2 H) = ⊥ ∧
      V F a' 1 ≤ H ∧
      IsQuadratic (fixedQuotientAction A (pResidual 2 H)) ((V F a' 1).subgroupOf H) := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily L S
  let H := graphLocalGroup F beta
  let A := (V F beta 1).subgroupOf H
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let := neighborhoodIn_normal F beta H (sylowGenerated_le _)
  have hb3 := (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.1
  have hb2 : 2 < b F := by
    change 3 ≤ b F at hb3
    omega
  refine ⟨hb2, ?_⟩
  let : IsElementaryAbelian 2 A := neighborhoodIn_elementary F ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  obtain ⟨⟨c⟩, hf, hquad⟩ := neighborhood_residual_section ht (Reduction.reduced_kernel_sylow h)
    beta hb2 H (core_le_graphLocalGroup ht beta) (sylowGenerated_le _)
  have hd' : (graph F).dist a' beta + 1 ≤ b F := by
    rw [SimpleGraph.dist_comm]
    exact hd.le
  have hn : Nontrivial (FixedQuotient A (pResidual 2 H)) :=
    local_residual_section_nontrivial ht (Reduction.reduced_borel_core_sylow h)
      (Reduction.reduced_vertex_sylow h) hab.symm (fixedQuotientAction A (pResidual 2 H)) c
  exact ⟨hn, ⟨c⟩, hf,
    neighbor_le_graphLocalGroup ht (Reduction.reduced_kernel_sylow h) a' beta hb hd',
    hquad a' hd'⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
