module

public import Theory.Representation.G2NaturalSemilinear

/-!
# Faithfulness of the natural G₂ quotient

An automorphism acting trivially on the trace-zero quotient fixes each of the
six nonscalar basis vectors modulo the identity line. Preservation of the
quadratic norm forces the scalar error to vanish. Products of two of those
vectors recover both remaining basis vectors, so the automorphism is identity.
The argument works over every field of characteristic two and also proves
faithfulness after restriction to the binary prime field.

This supplies the faithful natural action used in Aschbacher--Smith, B.4.6
and K.4.5. The split-octonion conventions and ATLAS attribution are retained
in the imported model. No simplicity or order theorem is needed.
-/

@[expose] public section

namespace Atlas.G2.Natural
open Atlas.SplitOctonion
variable (F : Type*) [Field F] [CharP F 2]

/-- The trace-zero quotient detects every octonion automorphism in characteristic two. -/
theorem action_injective : Function.Injective (action F) := by
  apply (action F).ker_eq_bot_iff.mp
  apply le_antisymm ?_ bot_le
  intro g hg
  change g = 1
  change action F g = 1 at hg
  have hfix (i : Fin 8) (hi : i ≠ 3) (hi' : i ≠ 4) :
      g.val (basisVector i) = basisVector i := by
    have hx : trace (basisVector i : Atlas.SplitOctonion.Carrier F) = 0 := by
      simp [trace, basisVector, Ne.symm hi, Ne.symm hi']
    have hq := LinearMap.congr_fun hg (mk F ⟨basisVector i, hx⟩)
    change mk F (traceZeroAction F g ⟨basisVector i, hx⟩) = mk F ⟨basisVector i, hx⟩ at hq
    obtain ⟨r, hr⟩ := (mk_eq_mk_iff F _ _).mp hq
    change r • unit = g.val (basisVector i) - basisVector i at hr
    have hv : g.val (basisVector i) = r • unit + basisVector i :=
      (eq_sub_iff_add_eq.mp hr).symm
    have hn := automorphism_norm g (basisVector i)
    rw [hv] at hn
    have hr0 : r = 0 := by
      clear hv hr hq hx
      fin_cases i <;> simp_all [Atlas.SplitOctonion.norm, unit, basisVector]
    simpa [hr0] using hv
  have h03 : mul (basisVector 0) (basisVector 7) = (basisVector 3 : Atlas.SplitOctonion.Carrier F) := by
    ext i
    fin_cases i <;> simp [mul, basisVector, CharTwo.neg_eq]
  have h74 : mul (basisVector 7) (basisVector 0) = (basisVector 4 : Atlas.SplitOctonion.Carrier F) := by
    ext i
    fin_cases i <;> simp [mul, basisVector, CharTwo.neg_eq]
  have hfixall (i : Fin 8) : g.val (basisVector i) = basisVector i := by
    by_cases h3 : i = 3
    · subst i
      rw [← h03, automorphism_mul, hfix 0 (by decide) (by decide),
        hfix 7 (by decide) (by decide)]
    by_cases h4 : i = 4
    · subst i
      rw [← h74, automorphism_mul, hfix 7 (by decide) (by decide),
        hfix 0 (by decide) (by decide)]
    exact hfix i h3 h4
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun F (Fin 8)).ext
  intro i
  simpa [Pi.basisFun_apply, basisVector] using hfixall i

variable [Algebra (ZMod 2) F]
/-- Restricting scalars to the prime field preserves faithfulness. -/
theorem binary_action_injective :
    Function.Injective (BinarySemilinear.innerRepresentation F) := by
  intro g h hgh
  apply action_injective F
  apply LinearMap.ext
  intro v
  have hv := LinearMap.congr_fun hgh v
  change BinarySemilinear.representation F (SemidirectProduct.inl g) v =
    BinarySemilinear.representation F (SemidirectProduct.inl h) v at hv
  simpa only [BinarySemilinear.representation_inner] using hv
end Atlas.G2.Natural
