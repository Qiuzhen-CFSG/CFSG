module

public import Theory.SpecificGroups.G2.ConwayRootFour.MarkedLift

/-!
# Resolving signs for the marked Mathieu involution

Let p be the literal coordinate permutation of `markedLift`. On the binary
Golay code, the image and kernel of 1 + p coincide. An explicit linear map R
satisfies (1 + p)R + R(1 + p) = 1; the proof checks this identity on the twelve
existing Golay basis vectors. Consequently two Golay words with opposite signs
on each p-pair differ by b + p(b) for a Golay word b.

The consumer `MonomialConjugacy` turns b into a sign isometry conjugating the
corresponding negative-square lifts. This calculation does not classify the
coordinate permutations.

Source context: Aschbacher, *Sporadic Groups* (1994), root-four conventions
p.269 and Lemma 49.5, pp.283–284. The concrete Golay encoder and basis are
existing attributed ATLAS ports; the resolving map and its verification here
are new calculations on those definitions.
-/

open Atlas.Codes Atlas.Lattices
public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion


private def signResolution (c : BinaryWord) : golay :=
  (c ((1,0),3) + c ((1,1),2) + c ((2,0),1) + c ((2,0),2) +
      c ((2,1),1) + c ((2,1),3)) • golayBasis 0 +
  (c ((1,0),3) + c ((1,1),2) + c ((2,0),3) + c ((2,1),0) +
      c ((2,1),1) + c ((2,1),3)) • golayBasis 1 +
  (c ((1,1),1) + c ((1,1),2) + c ((1,1),3) + c ((2,1),2) +
      c ((2,1),3)) • golayBasis 3 +
  (c ((0,1),3) + c ((1,1),3) + c ((2,0),1) + c ((2,0),2) +
      c ((2,1),2) + c ((2,1),3)) • golayBasis 4 +
  (c ((0,1),3) + c ((1,1),3) + c ((2,0),1) + c ((2,0),2) +
      c ((2,1),0)) • golayBasis 5 +
  (c ((2,1),2) + c ((2,1),3)) • golayBasis 11

private def signResolutionMap : golay →ₗ[Bit] golay where
  toFun c := signResolution c.val
  map_add' c d := by
    simp only [signResolution, Submodule.coe_add, Pi.add_apply, add_smul]
    abel
  map_smul' r c := by
    simp only [signResolution, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      ← mul_add, smul_add, smul_smul]
    rfl

private def swapDifference : golay →ₗ[Bit] golay :=
  LinearMap.id + (golayPermutationEquiv coordinateSwap).toLinearMap

private theorem swapDifference_val (c : golay) :
    (swapDifference c).val = c.val + coordinatePermutation coordinateSwap.val c.val := rfl

private theorem signResolutionMap_val (c : golay) :
    (signResolutionMap c).val =
  (c.val ((1,0),3) + c.val ((1,1),2) + c.val ((2,0),1) + c.val ((2,0),2) +
      c.val ((2,1),1) + c.val ((2,1),3)) • golayGenerators 0 +
  (c.val ((1,0),3) + c.val ((1,1),2) + c.val ((2,0),3) + c.val ((2,1),0) +
      c.val ((2,1),1) + c.val ((2,1),3)) • golayGenerators 1 +
  (c.val ((1,1),1) + c.val ((1,1),2) + c.val ((1,1),3) + c.val ((2,1),2) +
      c.val ((2,1),3)) • golayGenerators 3 +
  (c.val ((0,1),3) + c.val ((1,1),3) + c.val ((2,0),1) + c.val ((2,0),2) +
      c.val ((2,1),2) + c.val ((2,1),3)) • golayGenerators 4 +
  (c.val ((0,1),3) + c.val ((1,1),3) + c.val ((2,0),1) + c.val ((2,0),2) +
      c.val ((2,1),0)) • golayGenerators 5 +
  (c.val ((2,1),2) + c.val ((2,1),3)) • golayGenerators 11 := by
  simp only [signResolutionMap, LinearMap.coe_mk, AddHom.coe_mk, signResolution,
    Submodule.coe_add, Submodule.coe_smul, golayBasis_coe]

private theorem swap_contracting_identity :
    swapDifference.comp signResolutionMap + signResolutionMap.comp swapDifference =
      LinearMap.id := by
  apply golayBasis.ext
  intro i
  apply Subtype.ext
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    Submodule.coe_add, swapDifference_val, signResolutionMap_val, golayBasis_coe]
  revert i
  decide +kernel


/-- A fixed Golay word is a coboundary for the marked coordinate involution. -/
theorem fixed_sign_eq_coboundary (c : golay)
    (hc : ∀ i, c.val (coordinateSwap.val.symm i) = c.val i) :
    ∃ b : golay, ∀ i, b.val i + b.val (coordinateSwap.val.symm i) = c.val i := by
  have hz : swapDifference c = 0 := by
    apply Subtype.ext
    funext i
    change c.val i + c.val (coordinateSwap.val.symm i) = 0
    rw [hc]
    exact CharTwo.add_self_eq_zero _
  refine ⟨signResolutionMap c, ?_⟩
  have he := DFunLike.congr_fun swap_contracting_identity c
  change swapDifference (signResolutionMap c) + signResolutionMap (swapDifference c) = c at he
  rw [hz, map_zero, add_zero] at he
  intro i
  exact congrArg (fun d : golay => d.val i) he

/-- All opposite-sign words for the marked permutation are sign conjugate. -/
theorem opposite_signs_eq_marked_coboundary (c : golay)
    (hc : ∀ i, c.val (coordinateSwap.val.symm i) = c.val i + 1) :
    ∃ b : golay, ∀ i,
      b.val i + c.val i = signWord.val i + b.val (coordinateSwap.val.symm i) := by
  obtain ⟨b, hb⟩ := fixed_sign_eq_coboundary (c + signWord) (by
    intro i
    change c.val (coordinateSwap.val.symm i) + signWord.val (coordinateSwap.val.symm i) =
      c.val i + signWord.val i
    rw [hc, signs_opposite]
    ring_nf
    simp)
  refine ⟨b, fun i => ?_⟩
  have h := hb i
  change b.val i + b.val (coordinateSwap.val.symm i) = c.val i + signWord.val i at h
  rcases bit_cases (b.val i) with h₁ | h₁ <;>
    rcases bit_cases (b.val (coordinateSwap.val.symm i)) with h₂ | h₂ <;>
    rcases bit_cases (c.val i) with h₃ | h₃ <;>
    rcases bit_cases (signWord.val i) with h₄ | h₄ <;> simp_all

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion
