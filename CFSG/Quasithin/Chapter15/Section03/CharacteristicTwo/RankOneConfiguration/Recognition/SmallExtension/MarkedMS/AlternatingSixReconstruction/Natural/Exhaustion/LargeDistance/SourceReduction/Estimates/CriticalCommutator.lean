module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Critical
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSeed
public import Theory.GroupTheory.Commutator.NormalClosureSupplement

/-!
# Actual critical commutators on the replacement graph

The full vertex group and its two-residual have the same commutator on Z,
because the radical centralizes its omega-center seed. At a critical pair,
the far X-layer lies in the first edge kernel. Thus the X-commutator is
nontrivial and contained in both X-layers, while the Z-commutator is
contained in both U-layers. All containments use the original free-amalgam
embedding and relative vertex stabilizers.

The final edge application supplies the containment used in MS93 (2.3)(d).
Relative edge normality, failure of vertex normality and common-commutator
containment are still required. Source: MS93 (2.2)--(2.3), pp.856--859,
and the first paragraph of (3.8), p.877.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Estimates
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (d : Replacement L R)

include h in
/-- The radical centralizes its omega-center seed, so the full group and its
two-residual have the same commutator on the actual graph Z-layer. -/
theorem Z_full_commutator_alpha :
    ⁅Z d.radical (alpha d.radical), stabilizer d.radical (alpha d.radical)⁆ =
      U d.radical (alpha d.radical) := by
  let := replacementComponent_normal h d
  have hgen : replacementComponent d ⊔ d.radical = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨k, hk, t, ht, rfl⟩ := replacement_product h d g
    exact (replacementComponent d ⊔ d.radical).mul_mem (mem_sup_left hk) (mem_sup_right ht)
  have hcentral : omegaCenter d.radical ≤ centralizer (d.radical : Set d.overgroup) :=
    fun _ hx => (mem_omegaCenter_iff.mp hx).2.2
  have he := normalClosure_commutator_eq_of_centralizing_supplement
    (omegaCenter d.radical) (replacementComponent d) d.radical hgen hcentral
  have hfull :
      ⁅normalClosure (omegaCenter d.radical : Set d.overgroup), (⊤ : Subgroup d.overgroup)⁆ =
        ⁅normalClosure (omegaCenter d.radical : Set d.overgroup), replacementComponent d⁆ := by
    apply le_antisymm _ (commutator_mono le_rfl le_top)
    rw [he]
    exact commutator_mono le_normalClosure le_rfl
  rw [U, ChapterC.NaturalSixControl.SymplecticSeed.Z_eq_seedHull, Ltilde_alpha,
    replacement_residual h d]
  have htop : stabilizer d.radical (alpha d.radical) =
      (⊤ : Subgroup d.overgroup).map (embedM d.radical) := by
    rw [← MonoidHom.range_eq_map]
    exact stabilizer_m_base d.radical
  rw [htop, ← map_commutator, ← map_commutator, hfull]

include h in
theorem Z_full_commutator (a : Vertex d.radical) (ha : color d.radical a = false) :
    ⁅Z d.radical a, stabilizer d.radical a⁆ = U d.radical a := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color d.radical ha
  have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom)
    (Z_full_commutator_alpha h d)
  rw [map_commutator, ← Z_act, ← stabilizer_act, ← U_act] at hh
  simpa only [alpha, act_mVertex, one_mul] using hh

variable (e : CentralMarking L) (hz : center (L ⧸ pCore 2 L) = ⊥)
  (hn : InitialNatural h e hz)

private theorem critical_far_X_le_stabilizer
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false)
    (a' : Vertex d.radical)
    (hc : CriticalPair d.radical a a' ((replacementGeometry h d).exists_critical a ha)) :
    X d.radical a' ≤ stabilizer d.radical a := by
  have hp : 0 < criticalDistance d.radical a ((replacementGeometry h d).exists_critical a ha) := by
    rw [(replacementGeometry h d).distance_constant a ha]
    exact replacementDistance_pos h d
  obtain ⟨t, hat, ht⟩ := exists_adjacent_dist_sub_one d.radical a a' (hc.1 ▸ hp)
  have ha' := critical_endpoint_color d.radical a ha _ hc
  have hX : X d.radical a' ≤ Q d.radical t := by
    apply X_le_Q_of_dist_lt d.radical (replacementGeometry h d)
      (edgeCentralizerCondition h e hz hn d himage) a' ha' t
    rw [SimpleGraph.dist_comm, (replacementGeometry h d).distance_constant a' ha',
      ← (replacementGeometry h d).distance_constant a ha]
    have hd := hc.1
    omega
  exact hX.trans (CriticalCriterion.edge_le_stabilizer d.radical ha hat)

/-- Literal containment and nontriviality of the X-commutator used in (2.3)(d).
No elementary moving-layer identification or split cover is assumed. -/
theorem critical_X_commutator
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false)
    (a' : Vertex d.radical)
    (hc : CriticalPair d.radical a a' ((replacementGeometry h d).exists_critical a ha)) :
    ⁅X d.radical a, X d.radical a'⁆ ≤ X d.radical a ⊓ X d.radical a' ∧
      ⁅X d.radical a, X d.radical a'⁆ ≠ ⊥ := by
  have hp : 0 < criticalDistance d.radical a ((replacementGeometry h d).exists_critical a ha) := by
    rw [(replacementGeometry h d).distance_constant a ha]
    exact replacementDistance_pos h d
  have ha' := critical_endpoint_color d.radical a ha _ hc
  have hC := edgeCentralizerCondition h e hz hn d himage
  have hc' := critical_reverse d.radical (replacementGeometry h d) hC a ha hp a' ha' hc
  have hfirst := critical_far_X_le_stabilizer h d e hz hn himage a ha a' hc
  have hsecond := critical_far_X_le_stabilizer h d e hz hn himage a' ha' a hc'
  refine ⟨le_inf ?_ ?_, ?_⟩
  · exact le_normalizer_iff_commutator_le_left.mp (hfirst.trans (X_normalized d.radical a))
  · rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp (hsecond.trans (X_normalized d.radical a'))
  · intro hzero
    apply critical_noncommutation d.radical (replacementGeometry h d) hC a ha hp hc
    apply le_bot_iff.mp
    rw [← hzero]
    apply commutator_mono
    · exact (replacementGeometry h d).omega_bound a ha hp
    · apply (replacementGeometry h d).omega_bound a' ha'
      rw [(replacementGeometry h d).distance_constant a' ha',
        ← (replacementGeometry h d).distance_constant a ha]
      exact hp

/-- The corresponding Z-commutator lies in both literal moving layers. -/
theorem critical_Z_commutator_le_U
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false)
    (a' : Vertex d.radical)
    (hc : CriticalPair d.radical a a' ((replacementGeometry h d).exists_critical a ha)) :
    ⁅Z d.radical a, Z d.radical a'⁆ ≤ U d.radical a ⊓ U d.radical a' := by
  have hp : 0 < criticalDistance d.radical a ((replacementGeometry h d).exists_critical a ha) := by
    rw [(replacementGeometry h d).distance_constant a ha]
    exact replacementDistance_pos h d
  have ha' := critical_endpoint_color d.radical a ha _ hc
  have hc' := critical_reverse d.radical (replacementGeometry h d)
    (edgeCentralizerCondition h e hz hn d himage) a ha hp a' ha' hc
  have hza : Z d.radical a ≤ X d.radical a := (replacementGeometry h d).omega_bound a ha hp
  have hza' : Z d.radical a' ≤ X d.radical a' := by
    apply (replacementGeometry h d).omega_bound a' ha'
    rw [(replacementGeometry h d).distance_constant a' ha',
      ← (replacementGeometry h d).distance_constant a ha]
    exact hp
  apply le_inf
  · rw [← Z_full_commutator h d a ha]
    exact commutator_mono le_rfl
      (hza'.trans (critical_far_X_le_stabilizer h d e hz hn himage a ha a' hc))
  · rw [commutator_comm, ← Z_full_commutator h d a' ha']
    exact commutator_mono le_rfl
      (hza.trans (critical_far_X_le_stabilizer h d e hz hn himage a' ha' a hc'))

/-- Application to the actual first edge in the critical criterion. -/
theorem critical_X_commutator_le_edge
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false)
    (a' : Vertex d.radical)
    (hc : CriticalPair d.radical a a' ((replacementGeometry h d).exists_critical a ha))
    (t : Vertex d.radical) (hat : Adjacent d.radical a t) :
    ⁅X d.radical a, X d.radical a'⁆ ≤ Q d.radical t :=
  ((critical_X_commutator h d e hz hn himage a ha a' hc).1.trans inf_le_left).trans
    (CriticalCriterion.X_le_edge d.radical ha hat)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Estimates
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
