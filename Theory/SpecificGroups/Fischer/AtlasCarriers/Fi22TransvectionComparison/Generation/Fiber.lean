module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Evaluation

/-!
# The distinguished fiber of the Fi22 conjugate labeling

Evaluation at point zero separates `atlasA` from every other shared conjugate
word. A kernel check covers all 3510 labels using the proven word evaluator;
we only compare one image, not all pairs of permutations. This is the fiber
premise consumed by Schreier generation and the commuting-conjugate coverage
argument in `Generation`.

Source: the ATLAS F22G1-p3510B0 words, and the conjugation action in the paragraph
after GLS3 Table 5.3t, `refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi22.TransvectionComparison.Generation
open KernelCertificate

private def fiberCheck (i : Nat) : Bool :=
  let x : Fin 3510 := ⟨i % 3510, Nat.mod_lt _ (by decide)⟩
  decide (rootAction x 0 ≠ 523 ∨ x = rootBase)

set_option maxRecDepth 4096 in
private theorem fiberCheck0 : BitNetwork.check fiberCheck 0 256 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem fiberCheck1 : BitNetwork.check fiberCheck 256 256 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem fiberCheck2 : BitNetwork.check fiberCheck 512 256 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem fiberCheck3 : BitNetwork.check fiberCheck 768 256 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem fiberCheck4 : BitNetwork.check fiberCheck 1024 256 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem fiberCheck5 : BitNetwork.check fiberCheck 1280 256 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem fiberCheck6 : BitNetwork.check fiberCheck 1536 256 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem fiberCheck7 : BitNetwork.check fiberCheck 1792 256 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem fiberCheck8 : BitNetwork.check fiberCheck 2048 256 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem fiberCheck9 : BitNetwork.check fiberCheck 2304 256 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem fiberCheck10 : BitNetwork.check fiberCheck 2560 256 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem fiberCheck11 : BitNetwork.check fiberCheck 2816 256 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem fiberCheck12 : BitNetwork.check fiberCheck 3072 256 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem fiberCheck13 : BitNetwork.check fiberCheck 3328 182 = true := by
  decide +kernel

private theorem fiberCheck_all : BitNetwork.check fiberCheck 0 3510 = true :=
  (BitNetwork.check_append fiberCheck 0 256 3254 fiberCheck0
    (BitNetwork.check_append fiberCheck 256 256 2998 fiberCheck1
    (BitNetwork.check_append fiberCheck 512 256 2742 fiberCheck2
    (BitNetwork.check_append fiberCheck 768 256 2486 fiberCheck3
    (BitNetwork.check_append fiberCheck 1024 256 2230 fiberCheck4
    (BitNetwork.check_append fiberCheck 1280 256 1974 fiberCheck5
    (BitNetwork.check_append fiberCheck 1536 256 1718 fiberCheck6
    (BitNetwork.check_append fiberCheck 1792 256 1462 fiberCheck7
    (BitNetwork.check_append fiberCheck 2048 256 1206 fiberCheck8
    (BitNetwork.check_append fiberCheck 2304 256 950 fiberCheck9
    (BitNetwork.check_append fiberCheck 2560 256 694 fiberCheck10
    (BitNetwork.check_append fiberCheck 2816 256 438 fiberCheck11
    (BitNetwork.check_append fiberCheck 3072 256 182 fiberCheck12
    fiberCheck13)))))))))))))

/-- The single coordinate needed for the distinguished fiber certificate. -/
theorem rootAction_zero_fiber (x : Fin 3510) (h : rootAction x 0 = 523) :
    x = rootBase := by
  have hx := BitNetwork.check_sound fiberCheck 0 3510 fiberCheck_all x.val
    (Nat.zero_le _) x.isLt
  have hx' : rootAction x 0 ≠ 523 ∨ x = rootBase := by
    simpa only [fiberCheck, Nat.mod_eq_of_lt x.isLt, decide_eq_true_eq] using hx
  exact hx'.resolve_left (not_not.mpr h)

end Generation

/-- Only the distinguished label gives the original involution. -/
theorem conjugateAt_eq_atlasA_iff (x : Fin 3510) :
    conjugateAt x = atlasA ↔ x = rootBase := by
  constructor
  · intro hx
    apply Generation.rootAction_zero_fiber x
    rw [Generation.rootAction_eq, hx, inclusion_atlasA, KernelCertificate.generatorA_zero]
  · rintro rfl
    exact conjugateAt_base

end Sporadic.Fischer.Fi22.TransvectionComparison
