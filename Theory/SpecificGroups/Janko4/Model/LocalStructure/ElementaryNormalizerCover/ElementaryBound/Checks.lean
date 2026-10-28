module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Block0
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Block1
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Block2
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Block3
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Block4
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Block5
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Block6
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Block7
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Block8
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Block9
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Block10
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.Block11

/-!
# Meaning of the checked native tables

Every square-one element has a vertex. Native commutation implies membership
in the checked neighbor bitset, and every actual fixed mask belongs to the
checked mask bitset. The index map is injective, so vertex counting counts the
actual native subgroup without multiplicity. Only these directions are needed
by the finite product-bound checker.
-/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
open Janko4.LocalStructure.SylowCore.FiniteBoundCertificate
open Janko4.LocalStructure.SylowCore.FiniteBoundCertificate.NormalWeights
private theorem point_blocks : ∀ k : Fin 12, (List.finRange 16).all (fun a => pointCheck (actor k a)) = true := by
  intro k
  fin_cases k
  · exact pointBlock0
  · exact pointBlock1
  · exact pointBlock2
  · exact pointBlock3
  · exact pointBlock4
  · exact pointBlock5
  · exact pointBlock6
  · exact pointBlock7
  · exact pointBlock8
  · exact pointBlock9
  · exact pointBlock10
  · exact pointBlock11

private theorem point_valid (v : Fin 192) : pointCheck v = true := by
  have h := List.all_eq_true.mp (point_blocks (block v)) (offset v) (List.mem_finRange _)
  simpa only [actor_block_offset] using h

private theorem row_blocks : ∀ k : Fin 12, (List.finRange 16).all (fun a => rowCheck (actor k a)) = true := by
  intro k
  fin_cases k
  · exact rowBlock0
  · exact rowBlock1
  · exact rowBlock2
  · exact rowBlock3
  · exact rowBlock4
  · exact rowBlock5
  · exact rowBlock6
  · exact rowBlock7
  · exact rowBlock8
  · exact rowBlock9
  · exact rowBlock10
  · exact rowBlock11

private theorem row_valid (v : Fin 192) : rowCheck v = true := by
  have h := List.all_eq_true.mp (row_blocks (block v)) (offset v) (List.mem_finRange _)
  simpa only [actor_block_offset] using h

private theorem fixed_blocks : ∀ k : Fin 12, (List.finRange 16).all (fun a => fastFixedCheck (actor k a)) = true := by
  intro k
  fin_cases k
  · exact fixedBlock0
  · exact fixedBlock1
  · exact fixedBlock2
  · exact fixedBlock3
  · exact fixedBlock4
  · exact fixedBlock5
  · exact fixedBlock6
  · exact fixedBlock7
  · exact fixedBlock8
  · exact fixedBlock9
  · exact fixedBlock10
  · exact fixedBlock11

private theorem fixed_valid (v : Fin 192) : fastFixedCheck v = true := by
  have h := List.all_eq_true.mp (fixed_blocks (block v)) (offset v) (List.mem_finRange _)
  simpa only [actor_block_offset] using h

private theorem code_blocks : ∀ k : Fin 12, (List.finRange 16).all (fun a => codeCheck (actor k a)) = true := by
  intro k
  fin_cases k
  · exact codeBlock0
  · exact codeBlock1
  · exact codeBlock2
  · exact codeBlock3
  · exact codeBlock4
  · exact codeBlock5
  · exact codeBlock6
  · exact codeBlock7
  · exact codeBlock8
  · exact codeBlock9
  · exact codeBlock10
  · exact codeBlock11

private theorem code_valid (v : Fin 192) : codeCheck v = true := by
  have h := List.all_eq_true.mp (code_blocks (block v)) (offset v) (List.mem_finRange _)
  simpa only [actor_block_offset] using h

theorem point_spec (v : Fin 192) (p : Fin 24) : point v p = perm (vertexIndex v) p :=
  beq_iff_eq.mp (List.all_eq_true.mp (point_valid v) p (List.mem_finRange _))

theorem row_spec (v : Fin 192) : row v = rows (vertexIndex v) := by
  funext i
  exact beq_iff_eq.mp (List.all_eq_true.mp (row_valid v) i (List.mem_finRange _))

private theorem low_blocks : ∀ k : Fin 12, (List.finRange 16).all (fun a => lowCheck (actor k a)) = true := by
  intro k
  fin_cases k
  · exact lowBlock0
  · exact lowBlock1
  · exact lowBlock2
  · exact lowBlock3
  · exact lowBlock4
  · exact lowBlock5
  · exact lowBlock6
  · exact lowBlock7
  · exact lowBlock8
  · exact lowBlock9
  · exact lowBlock10
  · exact lowBlock11

private theorem low_valid (v : Fin 192) : lowCheck v = true := by
  have h := List.all_eq_true.mp (low_blocks (block v)) (offset v) (List.mem_finRange _)
  simpa only [actor_block_offset] using h

private theorem high_blocks : ∀ k : Fin 12, (List.finRange 16).all (fun a => highCheck (actor k a)) = true := by
  intro k
  fin_cases k
  · exact highBlock0
  · exact highBlock1
  · exact highBlock2
  · exact highBlock3
  · exact highBlock4
  · exact highBlock5
  · exact highBlock6
  · exact highBlock7
  · exact highBlock8
  · exact highBlock9
  · exact highBlock10
  · exact highBlock11

private theorem high_valid (v : Fin 192) : highCheck v = true := by
  have h := List.all_eq_true.mp (high_blocks (block v)) (offset v) (List.mem_finRange _)
  simpa only [actor_block_offset] using h

theorem fixedBit_spec (v : Fin 192) (m : Fin 2048) (h : fixes v m = true) :
    fixedBit v m = true := by
  have hm := List.all_eq_true.mp (fixed_valid v) m (List.mem_finRange _)
  have he : fastImage v m = m.val :=
    (fastImage_spec v (low_valid v) (high_valid v) m).trans (beq_iff_eq.mp h)
  simpa only [he, bne_self_eq_false, Bool.false_or] using hm

theorem vertexIndex_injective : Function.Injective vertexIndex := by
  intro v w h
  have hv : vertexCode (vertexIndex v) = v := beq_iff_eq.mp (code_valid v)
  have hw : vertexCode (vertexIndex w) = w := beq_iff_eq.mp (code_valid w)
  exact hv.symm.trans ((congrArg vertexCode h).trans hw)

private theorem compatible_blocks : ∀ k : Fin 12,
    (List.finRange 16).all (fun a => (List.finRange 192).all
      (fun w => compatibleCheck (actor k a) w)) = true := by
  intro k
  fin_cases k
  · exact compatibleBlock0
  · exact compatibleBlock1
  · exact compatibleBlock2
  · exact compatibleBlock3
  · exact compatibleBlock4
  · exact compatibleBlock5
  · exact compatibleBlock6
  · exact compatibleBlock7
  · exact compatibleBlock8
  · exact compatibleBlock9
  · exact compatibleBlock10
  · exact compatibleBlock11

theorem compatible_spec (v w : Fin 192)
    (h : ∀ p : Fin 3, point v (point w (p.castLE (by decide))) =
      point w (point v (p.castLE (by decide)))) : compatible v w = true := by
  have h1 := List.all_eq_true.mp (compatible_blocks (block v)) (offset v) (List.mem_finRange _)
  rw [actor_block_offset] at h1
  have h2 := List.all_eq_true.mp h1 w (List.mem_finRange _)
  have h0 : point v (point w 0) = point w (point v 0) := h 0
  have h1 : point v (point w 1) = point w (point v 1) := h 1
  have h3 : point v (point w 2) = point w (point v 2) := h 2
  simpa only [compatibleCheck, h0, h1, h3, bne_self_eq_false, Bool.or_false] using h2

private theorem coverage_blocks : ∀ a : Fin 16, (List.finRange 8).all
    (fun b => (List.finRange 8).all (fun c => coverageCheck (a,b,c))) = true := by
  intro a
  fin_cases a
  · exact coverageBlock0
  · exact coverageBlock1
  · exact coverageBlock2
  · exact coverageBlock3
  · exact coverageBlock4
  · exact coverageBlock5
  · exact coverageBlock6
  · exact coverageBlock7
  · exact coverageBlock8
  · exact coverageBlock9
  · exact coverageBlock10
  · exact coverageBlock11
  · exact coverageBlock12
  · exact coverageBlock13
  · exact coverageBlock14
  · exact coverageBlock15

theorem vertex_coverage (i : Index) (hi : SquareTest i) : vertexIndex (vertexCode i) = i := by
  have hc := List.all_eq_true.mp (List.all_eq_true.mp (coverage_blocks i.1)
    i.2.1 (List.mem_finRange _)) i.2.2 (List.mem_finRange _)
  have hs : squareCheck i = true := by
    apply List.all_eq_true.mpr
    intro p _
    exact beq_iff_eq.mpr (hi p)
  have he : decide (vertexIndex (vertexCode i) = i) = true := by
    simpa only [coverageCheck, hs, Bool.not_true, Bool.false_or] using hc
  exact of_decide_eq_true he

end Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
