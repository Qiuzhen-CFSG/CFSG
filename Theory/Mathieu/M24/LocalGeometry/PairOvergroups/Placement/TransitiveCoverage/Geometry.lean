module
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.Alternatives
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineLifts.CodePreservation

/-!
# Marked geometry for the M₂₄ small Sylow overgroups

The already enumerated Sylow subgroup preserves a specific octad and trio.
Twelve checked Golay row images certify an explicit native M₂₄ element that
transports `standardTrio.parts` to this marked trio. This supplies the actual
conjugator required by the placement theorem. A subgroup preserving the marked
octad cannot act transitively on the 24 points.

Source: Aschbacher, *Sporadic Groups*, Chapter 7, §20, especially Lemma 20.2;
Aschbacher–Smith, printed p.511; GLS3 Table 5.3e. The concrete marking was
recovered from attempt 9bb9a957965940d298e94f8608e0eb8f; its original is preserved.
All displayed permutation and code identities are checked by the kernel.
-/

public section
open Subgroup MulAction
open scoped Pointwise
namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.TransitiveCoverage
open SylowNormalizer

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

@[expose] def markedOctadPoints : Finset (Fin 24) := {0, 3, 4, 8, 9, 11, 19, 21}

theorem markedOctadPoints_mem : markedOctadPoints ∈ m24Blocks := by
  have he : markedOctadPoints = m24GolayWord 1817 := by decide +kernel
  rw [he]
  exact m24GolayWord_mem_blocks_of_card_eq_eight _ (by rw [← he]; decide +kernel)

@[expose] def markedOctad : Octad := ⟨markedOctadPoints, markedOctadPoints_mem⟩

@[expose] def markedTrioParts : Finset (Finset (Fin 24)) :=
  {{1, 2, 12, 13, 16, 18, 20, 22}, markedOctadPoints, {5, 6, 7, 10, 14, 15, 17, 23}}

private def conjugatorPerm : Equiv.Perm (Fin 24) where
  toFun := ![3, 19, 0, 11, 7, 5, 16, 22, 14, 13, 9, 15, 18, 10, 1, 2, 21, 6, 17, 20, 12, 23, 8, 4]
  invFun := ![2, 14, 15, 0, 23, 5, 17, 4, 22, 10, 13, 3, 20, 9, 8, 11, 6, 18, 12, 1, 19, 16, 7, 21]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def conjugatorRow : Fin 12 → Fin 4096 := ![94, 852, 851, 1856, 710, 114, 272, 788, 534, 2562, 324, 262]

private theorem conjugatorPerm_mem : conjugatorPerm ∈ M24 := by
  apply QuotientConstruction.AffineLiftConstruction.mem_M24_of_rows
  intro i
  refine ⟨conjugatorRow i, ?_⟩
  revert i
  decide +kernel

noncomputable def markedConjugator : M24 := ⟨conjugatorPerm, conjugatorPerm_mem⟩

theorem markedConjugator_parts : markedConjugator • standardTrio.parts = markedTrioParts := by
  change conjugatorPerm • standardTrio.parts = markedTrioParts
  decide +kernel

@[expose] noncomputable def markedTrioStabilizer : Subgroup M24 :=
  MulAction.stabilizer M24 markedTrioParts

theorem markedTrioStabilizer_eq :
    markedTrioStabilizer = conjugateTrioStabilizer markedConjugator := by
  unfold conjugateTrioStabilizer
  rw [markedConjugator_parts]
  rfl

theorem candidate_le_markedOctad : candidate ≤ octadStabilizer markedOctad := by
  change Subgroup.closure (Set.range generator) ≤ _
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  change generatorPerm i • markedOctadPoints = markedOctadPoints
  revert i
  decide +kernel

theorem candidate_le_markedTrio : candidate ≤ markedTrioStabilizer := by
  change Subgroup.closure (Set.range generator) ≤ _
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  change generatorPerm i • markedTrioParts = markedTrioParts
  revert i
  decide +kernel

theorem not_pretransitive_of_le_markedOctad (H : Subgroup M24)
    (hH : H ≤ octadStabilizer markedOctad) : ¬ IsPretransitive H (Fin 24) := by
  intro ht
  obtain ⟨g, hg⟩ := ht.exists_smul_eq (0 : Fin 24) 1
  have hfix := (MulAction.mem_stabilizer_finset'.mp (hH g.property))
    (by decide : (0 : Fin 24) ∈ markedOctadPoints)
  change (g : M24) • (0 : Fin 24) ∈ markedOctadPoints at hfix
  change (g : M24) • (0 : Fin 24) = 1 at hg
  rw [hg] at hfix
  exact (by decide : (1 : Fin 24) ∉ markedOctadPoints) hfix

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.TransitiveCoverage
end
