module
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.TensorRank
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.Source
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.Established
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Nontrivial

/-!
# The source involution estimate for faithful exceptional tensors

The original faithful action supplies a nontrivial algebraic factor, the
proved basic minimum gives dimension at least 26, and the genuine binary Ree
odd-element calculation supplies displacement at least ten in every large
factor. The periodic tensor calculation therefore gives the source estimate.
The actual intertwining map identifies the original cyclic fixed quotient.

Only tensor realization and its dimension period remain inputs here. Their
finite Steinberg classification producer must discharge both in the final
binary model theorem. Source: Guralnick–Malle II, Lemma 8.8, internal pp.57–58.
-/

public section
open Module Representation Theory.AlgebraicGroup
open ReeF4.BinaryDegree.ExceptionalTensor
namespace ReeF4.FixedSpaceEstimate
universe u v
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

/-- The source ten-dimensional estimate on every factor feeds the literal
periodic exceptional tensor. Nontriviality follows from the original faithful
representation and the actual intertwining equivalence. -/
theorem exceptionalTensor_bound_of_faithful {m : ℕ} (hm : 1 ≤ m)
    {W : Type v} [AddCommGroup W] [Module F W]
    (σ : Representation F (Model m) W) (hσ : Function.Injective σ)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (hB : ∀ i, (B i).IsExceptionalBasic)
    (e : Representation.Equiv σ
      (exceptionalTensor (Classification.splitEmbedding (Classification.coefficientHom F m)) B).ρ)
    {s : ℕ} (hs : 0 < s) (hsn : s ∣ 2 * m + 1)
    (hshift : ∀ i, finrank F (B (i + 2 * (s : ZMod (2 * m + 1)))).Space =
      finrank F (B i).Space)
    (t : Model m) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    10 * (2 * m + 1) ≤ s * finrank F
      (W ⧸ invariants (σ.comp (Subgroup.zpowers t).subtype)) := by
  let τ := (exceptionalTensor
    (Classification.splitEmbedding (Classification.coefficientHom F m)) B).ρ
  have hmap : (invariants (σ.comp (Subgroup.zpowers t).subtype)).map
      e.toLinearEquiv.toLinearMap = invariants (τ.comp (Subgroup.zpowers t).subtype) := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩ g
      have hi := Representation.IntertwiningMap.isIntertwining σ τ e.toIntertwiningMap g.val v
      change e (σ g.val v) = τ g.val (e v) at hi
      change τ g.val (e v) = e v
      have hv' : σ g.val v = v := hv g
      rw [← hi, hv']
    · intro hw
      refine ⟨e.toLinearEquiv.symm w, ?_, e.toLinearEquiv.apply_symm_apply w⟩
      intro g
      apply e.toLinearEquiv.injective
      have hi := Representation.IntertwiningMap.isIntertwining σ τ e.toIntertwiningMap g.val
        (e.toLinearEquiv.symm w)
      change e (σ g.val (e.toLinearEquiv.symm w)) = τ g.val (e (e.toLinearEquiv.symm w)) at hi
      change e (σ g.val (e.toLinearEquiv.symm w)) = e (e.toLinearEquiv.symm w)
      rw [hi]
      have hew : e (e.toLinearEquiv.symm w) = w := e.toLinearEquiv.apply_symm_apply w
      rw [hew]
      exact hw g
  have he := (Submodule.Quotient.equiv _ _ e.toLinearEquiv hmap).finrank_eq
  rw [he]
  obtain ⟨i, hi⟩ := Classification.exists_nontrivial_factor_of_faithful σ hσ _ B e
  exact exceptionalTensor_periodic_fixedCodim_bound _ B t ht2 hs hsn
    ⟨i, basicFactorMinimum_charTwo (B i) (hB i) hi⟩ hshift
    (fun i hi => BasicInvolutions.exceptionalFactor_involution_bound hm B hB i hi t ht ht2)

end ReeF4.FixedSpaceEstimate
