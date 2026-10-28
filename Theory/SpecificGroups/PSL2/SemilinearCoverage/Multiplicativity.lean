module
public import Theory.SpecificGroups.PSL2.SemilinearCoverage.RootParameters

/-!
# Recovery of multiplication from the root action

A normalized automorphism fixes the parameter one by the braid relation.
The diagonal torus acts on the upper root group by square scalars. Applying the
automorphism to this action first forces each image of a diagonal element into
the Borel, and then forces the root-coordinate map to respect multiplication by
squares. Every element of a finite field of characteristic two is a square.
Thus the normalized automorphism is the concrete entrywise field action.

This supplies field recovery in the elementary proof of GLS, Volume 4,
Chapter 4, Lemma 3.1(a), used in Lemma 3.4(c).

Adapted from the corresponding module under
`BenderSuzuki/ZD/Recognition/MinimalReduction/LocalEmbedding/BenderAutomorphisms/Linear/`.
The Theory consumer is GLS2, Chapter G, the automorphism paragraph before
Theorem 26.24, Step 5 (`refs/KGroup/GLS2/ChapterG.tex`).
-/

namespace Theory.PSL2.SemilinearCoverage
variable {K : Type*} [Field K] [CharP K 2]

private theorem rootParameter_mul_unit_sq (a : MulAut (SL2 K))
    (hU : (Unip K).map a.toMonoidHom = Unip K) (hw : a (weyl K) = weyl K)
    (r : Kˣ) (t : K) :
    rootParameter a ((r : K) ^ 2 * t) = rootParameter a ((r : K) ^ 2) * rootParameter a t := by
  have htor : tor r ∈ Borel K := by rw [mem_Borel_iff]; simp
  have hrel (s : K) : tor r * uni s * (tor r)⁻¹ = uni ((r : K) ^ 2 * s) := by
    simpa using Borel_conj_uni htor s
  have hmap (s : K) :
      a (tor r) * uni (rootParameter a s) * (a (tor r))⁻¹ =
        uni (rootParameter a ((r : K) ^ 2 * s)) := by
    have h := congrArg a (hrel s)
    simpa only [map_mul, map_inv, map_uni_of_preserves_root a hU] using h
  have h1 := hmap 1
  rw [rootParameter_one a hU hw, mul_one] at h1
  have heq := (mul_inv_eq_iff_eq_mul).mp h1
  have hB : a (tor r) ∈ Borel K := by
    rw [mem_Borel_iff]
    have he := congrArg (fun g : SL2 K => g.val 1 1) heq
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using he
  have hs (s : K) : rootParameter a ((r : K) ^ 2 * s) =
      (a (tor r)).val 0 0 ^ 2 * rootParameter a s :=
    uni_injective ((hmap s).symm.trans (Borel_conj_uni hB _))
  have hsq : rootParameter a ((r : K) ^ 2) = (a (tor r)).val 0 0 ^ 2 := by
    simpa only [mul_one, rootParameter_one a hU hw] using hs 1
  rw [hs, hsq]

/-- Normalized root coordinates over a finite field preserve multiplication. -/
public theorem rootParameter_mul [Finite K] (a : MulAut (SL2 K))
    (hU : (Unip K).map a.toMonoidHom = Unip K) (hw : a (weyl K) = weyl K)
    (s t : K) : rootParameter a (s * t) = rootParameter a s * rootParameter a t := by
  obtain ⟨r, rfl⟩ := (Finite.surjective_of_injective (CharTwo.sq_injective (R := K))) s
  by_cases hr : r = 0
  · subst r
    have hz : rootParameter a 0 = 0 := (rootParameterEquiv a hU).map_zero
    simp [hz]
  · exact rootParameter_mul_unit_sq a hU hw (Units.mk0 r hr) t

/-- Every automorphism preserving the upper root group and fixing the Weyl
matrix is an actual entrywise field automorphism. -/
public theorem eq_sl2FieldAut_of_preserves_root_weyl [Finite K] (a : MulAut (SL2 K))
    (hU : (Unip K).map a.toMonoidHom = Unip K) (hw : a (weyl K) = weyl K) :
    ∃ σ : K ≃+* K, a = sl2FieldAut σ :=
  eq_sl2FieldAut_of_rootParameter_mul a hU hw (rootParameter_mul a hU hw)

end Theory.PSL2.SemilinearCoverage
