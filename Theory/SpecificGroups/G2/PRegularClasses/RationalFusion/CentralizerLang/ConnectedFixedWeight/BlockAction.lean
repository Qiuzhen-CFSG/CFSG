module

public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedFixedWeight.Coordinates
public import Theory.AtlasPort.LinearGroups.G2.WeylMaps

/-!
# Realizing fixed-weight blocks as octonion automorphisms

Every invertible two-dimensional block is realized by an actual automorphism
of the split octonions over any field of characteristic two. Root C supplies
upper transvections, the Weyl word `(weylR * weylS)^3 * weylR` swaps the two
coordinates, and conjugating by this word supplies lower transvections.
The torus supplies diagonal blocks. Gaussian elimination constructs the
required automorphism when the upper-left entry is nonzero; swapping rows
handles the remaining invertible matrices. The calculation checks the action
on all eight octonion coordinates.

Together with `block_coordinates` and `mem_centralizer_of_blockApply`, this
realizes precisely the blocks of the fixed-weight torus centralizer used in
the semisimple-centralizer argument of Steinberg, 8.1/8.5 and 12.5,
`refs/KGroup/GLS3/Chapter2St2.tex`.

The root, torus and Weyl automorphisms use the licensed ATLAS port and its
Wilson split-octonion coordinates. See `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`; the imported ATLAS modules retain their source
attribution and revision.
-/

public section

open Atlas.SplitOctonion
open scoped CharTwo

namespace Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.FixedWeight

variable {K : Type*} [Field K] [CharP K 2]

private def swap : Model K := (weylR * weylS)^3 * weylR

private theorem swap_apply (x : Carrier K) :
    (swap : Model K).val x = ![x 7, x 5, x 6, x 4, x 3, x 1, x 2, x 0] := by
  ext i
  fin_cases i <;>
    simp [swap, pow_succ, weylR, weylREquiv, weylRLinear, weylRApply,
      weylS, weylSEquiv, weylSLinear, weylSApply, CharTwo.neg_eq]

private theorem upper_apply (u : K) (x : Carrier K) :
    (rootC u).val x = blockApply 1 u 0 1 1 x := by
  ext i
  fin_cases i <;>
    simp [rootC, Explicit.rootCEquiv, Explicit.rootCLinear, Explicit.rootCApply,
      blockApply, CharTwo.sub_eq_add]
  all_goals ring

private def lower (u : K) : Model K := swap * rootC u * swap

private theorem lower_apply (u : K) (x : Carrier K) :
    (lower u).val x = blockApply 1 0 u 1 1 x := by
  change (swap : Model K).val ((rootC u).val ((swap : Model K).val x)) = _
  rw [swap_apply, upper_apply, swap_apply]
  ext i
  fin_cases i <;> simp [blockApply] <;> ring

private theorem diagonal_apply (a d : Kˣ) (x : Carrier K) :
    (torus (a / d) a).val x =
      blockApply (a : K) 0 0 (d : K) ((a : K) * (d : K))⁻¹ x := by
  change (fun i => (torusWeights (a / d) a i : K) * x i) = _
  ext i
  fin_cases i <;> simp [torusWeights, blockApply]
  all_goals field_simp

private theorem gauss_apply (a b c d : K) (ha : a ≠ 0) (hd : a * d + b * c ≠ 0)
    (x : Carrier K) :
    blockApply 1 0 (c / a) 1 1
      (blockApply a 0 0 ((a * d + b * c) / a) (a * ((a * d + b * c) / a))⁻¹
        (blockApply 1 (b / a) 0 1 1 x)) =
      blockApply a b c d (a * d + b * c)⁻¹ x := by
  ext i
  fin_cases i <;> simp [blockApply]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp

private theorem exists_block_of_pivot (a b c d : K)
    (ha : a ≠ 0) (hd : a * d + b * c ≠ 0) :
    ∃ g : Model K, ∀ x : Carrier K,
      g.val x = blockApply a b c d (a * d + b * c)⁻¹ x := by
  let u : Kˣ := Units.mk0 a ha
  let v : Kˣ := Units.mk0 ((a * d + b * c) / a) (div_ne_zero hd ha)
  refine ⟨lower (c / a) * torus (u / v) u * rootC (b / a), ?_⟩
  intro x
  change (lower (c / a)).val ((torus (u / v) u).val ((rootC (b / a)).val x)) = _
  rw [lower_apply, diagonal_apply, upper_apply]
  exact gauss_apply a b c d ha hd x

private theorem swap_blockApply (a b c d t : K) (x : Carrier K) :
    (swap : Model K).val (blockApply a b c d t x) = blockApply c d a b t x := by
  rw [swap_apply]
  ext i
  fin_cases i <;> simp [blockApply]
  all_goals ring_nf
  all_goals simp

private theorem exists_block (a b c d : K) (hd : a * d + b * c ≠ 0) :
    ∃ g : Model K, ∀ x : Carrier K,
      g.val x = blockApply a b c d (a * d + b * c)⁻¹ x := by
  by_cases ha : a = 0
  · have hc : c ≠ 0 := by
      intro hc
      simp [ha, hc] at hd
    have he : c * b + d * a = a * d + b * c := by ring
    obtain ⟨g, hg⟩ := exists_block_of_pivot c d a b hc (by rwa [he])
    refine ⟨swap * g, ?_⟩
    intro x
    change (swap : Model K).val (g.val x) = _
    rw [hg, swap_blockApply, he]
  · exact exists_block_of_pivot a b c d ha hd

/-- Every invertible two-dimensional block is realized by an actual octonion
automorphism, over any field of characteristic two. -/
theorem exists_block_automorphism (A : Matrix (Fin 2) (Fin 2) K) (hA : A.det ≠ 0) :
    ∃ g : Model K, ∀ x : Carrier K,
      g.val x = blockApply (A 0 0) (A 0 1) (A 1 0) (A 1 1) A.det⁻¹ x := by
  have hd : A.det = A 0 0 * A 1 1 + A 0 1 * A 1 0 := by
    rw [Matrix.det_fin_two, CharTwo.sub_eq_add]
  rw [hd] at hA ⊢
  exact exists_block (A 0 0) (A 0 1) (A 1 0) (A 1 1) hA

end Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.FixedWeight
