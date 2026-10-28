module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.LocalActor
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CommutatorGeometry
public import Theory.Representation.BinaryConjugationSection.InvariantPreimage

/-!
# A neighboring center generates the residual neighborhood section

Local transitivity expresses the whole radius-one span as its central
vertex term joined with the conjugates of one neighboring center. On
V_beta/C_V_beta(O²(L_beta)), the central vertex term vanishes. Pulling an
invariant subspace back to the original span therefore shows that the
image of the adjacent Z_alpha generates this exact quotient module.

The reduced critical application supplies the required central vertex
identity directly from the genuine graph geometry. Generation by this
neighboring image does not assert the corrected Sylow-fixed generation
condition; its remaining fixed-space argument must use these same vectors.

Source: DGS, *Groups and Graphs* (1985), 9.1(b) and 9.3, pp.141--142;
the fixed-space-generation correction to 5.12 is retained separately.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- On the literal residual section, the image of one neighboring Z generates
under the local actor. This is not yet Sylow-fixed-space generation. -/
theorem residual_section_neighbor_generation (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hz : Z (family P) v = omegaCenterIn (graphLocalGroup (family P) v))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (graphLocalGroup (family P) v) W)
    (c : BinaryConjugationSection (graphLocalGroup (family P) v) (V (family P) v 1)
      (V (family P) v 1 ⊓ centralizer ((pResidual 2 (graphLocalGroup (family P) v)).map
        (graphLocalGroup (family P) v).subtype : Set G)) ρ)
    (M : Subrepresentation ρ)
    (hseed : ∀ z : V (family P) v 1, (z : G) ∈ Z (family P) w →
      (c.coordinates z).toAdd ∈ M.toSubmodule) : M = ⊤ := by
  let := finite_endpoints h
  have hspan := CommutingThreeProfile.V_eq_center_sup_neighbor_conjugates (family P)
    (graphLocalGroup (family P) v) (sylowGenerated_le _) hvw
    (fun z hz => graphLocalGroup_transitive h hB hS v ⟨w, hvw⟩ ⟨z, hz⟩)
  have hcenter : Z (family P) v ≤ c.invariantPreimage M := by
    apply le_trans _ (c.kernel_le_invariantPreimage M)
    refine le_inf (Z_le_V (family P) v 1) ?_
    intro z hz'
    exact centralizer_le (map_subtype_le _) ((mem_omegaCenterIn_iff _ _).mp (hz ▸ hz')).2.1
  have hwV : Z (family P) w ≤ V (family P) v 1 :=
    le_iSup_of_le w (le_iSup_of_le ((mem_ball_one (family P) v w).mpr (Or.inl hvw)) le_rfl)
  have hwM : Z (family P) w ≤ c.invariantPreimage M := by
    intro z hz'
    exact (c.mem_invariantPreimage M z).mpr ⟨hwV hz', hseed ⟨z, hwV hz'⟩ hz'⟩
  have hV : V (family P) v 1 ≤ c.invariantPreimage M := by
    exact hspan.le.trans (sup_le hcenter
      (conjugateSpanBy_le hwM (c.invariantPreimage_normalized M)))
  apply top_unique
  intro z _
  obtain ⟨a, ha⟩ := c.onto (Multiplicative.ofAdd z)
  have hm := (c.mem_invariantPreimage M a).mp (hV a.property) |>.choose_spec
  change z ∈ M.toSubmodule
  simpa only [ha, toAdd_ofAdd] using hm

variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The actual critical configuration supplies the central term and local
transitivity, so the same neighboring image generates every residual section. -/
theorem reduced_critical_neighbor_generation (h : HypothesisF11 L S)
    {a beta a' : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) a a')
    (hab : (graph (Reduction.reducedFamily L S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S)).dist beta a' + 1 = b (Reduction.reducedFamily L S))
    (hb : 1 < b (Reduction.reducedFamily L S))
    (hcomm : ⁅Z (Reduction.reducedFamily L S) a, Z (Reduction.reducedFamily L S) a'⁆ = ⊥)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (graphLocalGroup (Reduction.reducedFamily L S) beta) W)
    (c : BinaryConjugationSection (graphLocalGroup (Reduction.reducedFamily L S) beta)
      (V (Reduction.reducedFamily L S) beta 1)
      (V (Reduction.reducedFamily L S) beta 1 ⊓ centralizer
        ((pResidual 2 (graphLocalGroup (Reduction.reducedFamily L S) beta)).map
          (graphLocalGroup (Reduction.reducedFamily L S) beta).subtype : Set (Reduction.G₀ L S))) ρ)
    (M : Subrepresentation ρ)
    (hseed : ∀ z : V (Reduction.reducedFamily L S) beta 1,
      (z : Reduction.G₀ L S) ∈ Z (Reduction.reducedFamily L S) a →
      (c.coordinates z).toAdd ∈ M.toSubmodule) : M = ⊤ :=
  residual_section_neighbor_generation (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hab.symm
    (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1 ρ c M hseed

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
