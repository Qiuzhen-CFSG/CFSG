module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ActionClassification.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ActionClassification.Faithfulness
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ActionClassification.S3Normalization.Cubic
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ActionClassification.S3Normalization.Inverting
/-!
# Normalization on the labelled S₃ subgroup

A faithful binary S₄-action with full fixed space of order two has a
nontrivial cubic operator and a nonidentity fixed vector. First choose a
basis in which `(0 1 2)` permutes the first three coordinates. The relation
inverting this cycle then puts `(0 1)` into either its ordinary permutation
form or its parity-twisted form, by a second basis change commuting with
the cubic operator. Composing the two actual multiplicative equivalences
preserves both generator labels.

This proves the independent S₃ normalization step used toward
Huppert–Blackburn, *Finite Groups III*, XII.1.18(b), p.314. Faithfulness is an
explicit premise, discharged by the parent from its Sylow fixed-space
hypothesis. No representation classification or unconstructed basis is
assumed; the remaining S₄ classification stays with its assembly owner.
-/

open Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.S3Normalization
namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification

private theorem changeBasis_trans (α : SymmetricFour →* MulAut BinaryFour)
    (e f : MulAut BinaryFour) :
    changeBasis α (e.trans f) = changeBasis (changeBasis α e) f := by
  apply MonoidHom.ext
  intro s
  apply MulEquiv.ext
  intro v
  rfl

/-- Normalize the two fixed S₃ generators by an actual binary basis change. -/
public theorem exists_s3_normalization (α : SymmetricFour →* MulAut BinaryFour)
    (hinj : Function.Injective α)
    (hfixed : Nat.card {v : BinaryFour // ∀ s : SymmetricFour, α s v = v} = 2) :
    ∃ e : MulAut BinaryFour,
      changeBasis α e threeCycle = permutationAction threeCycle ∧
      (changeBasis α e transposition = permutationAction transposition ∨
        changeBasis α e transposition = twistedAction transposition) := by
  have hcube : α threeCycle ^ 3 = 1 := by
    rw [← map_pow, threeCycle_cube, map_one]
  have hne : α threeCycle ≠ 1 := by
    intro h
    exact threeCycle_ne_one (hinj (h.trans α.map_one.symm))
  obtain ⟨v, hv, hvfixed⟩ := exists_nonidentity_fixed α hfixed
  obtain ⟨f, hf⟩ := normalize_cubic (α threeCycle) hcube hne ⟨v, hv, hvfixed threeCycle⟩
  let β := changeBasis α f.symm
  have hb : β threeCycle = permutationAction threeCycle := by
    apply MulEquiv.ext
    intro w
    change f.symm (α threeCycle (f w)) = _
    rw [hf, f.symm_apply_apply]
  have hsquare : β transposition * β transposition = 1 := by
    have h := congrArg β transposition_square
    simpa only [pow_two, map_mul, map_one] using h
  have hinverts : β transposition * permutationAction threeCycle =
      (permutationAction threeCycle * permutationAction threeCycle) * β transposition := by
    have h : transposition * threeCycle = (threeCycle * threeCycle) * transposition := by
      decide +kernel
    have he := congrArg β h
    simpa only [map_mul, hb] using he
  obtain ⟨g, hg, ht⟩ := normalize_inverting (β transposition) hsquare hinverts
  refine ⟨f.symm.trans g.symm, ?_, ?_⟩
  · rw [changeBasis_trans]
    apply MulEquiv.ext
    intro w
    change g.symm (β threeCycle (g w)) = _
    rw [hb, hg, g.symm_apply_apply]
  · rw [changeBasis_trans]
    rcases ht with ht | ht
    · left
      apply MulEquiv.ext
      intro w
      change g.symm (β transposition (g w)) = _
      rw [ht, g.symm_apply_apply]
    · right
      apply MulEquiv.ext
      intro w
      change g.symm (β transposition (g w)) = _
      rw [ht, g.symm_apply_apply]
end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification
