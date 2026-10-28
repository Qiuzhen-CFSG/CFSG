module

public import Theory.Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement.Rigidity

/-!
# Transporting tensor conjugation to the actual representation

Suppose a literal involution and a transpose-conjugate tensor operator send
each group representative to the same target action. A genuine representation
equivalence then transports the tensor coordinates to the original module.
Both conjugations equal that target action because both operators square to
one. This argument works with central kernels and does not assert any
outer-automorphism classification or remove a scalar by assumption.

The actual Schur-linear SU₃ actor is the consumer in
`GraphStable.Displacement.Conjugation`.
Source: Guralnick--Malle, Classification of 2F-modules II, Proposition 4.11,
internal pp.31--32.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Representation.SL3.BinaryDefiningFactors
namespace Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement.OuterConjugation
variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

/-- Common target representatives identify conjugation on the actual module. -/
theorem conjugation_eq_of_word_intertwiner
    (ρ : Representation K G V) (w : List Factor)
    (τ : Representation K G (WordSpace K w))
    (E : ρ.Equiv τ) (T : Module.End K V) (hT : T * T = 1)
    (S c : WordSpace K w ≃ₗ[K] WordSpace K w)
    (hc : ∀ x, c (S x) = wordTranspose w (c x))
    (ht : ∀ g, ∃ h, T * ρ g = ρ h * T ∧
      S.toLinearMap * τ g = τ h * S.toLinearMap) :
    ∃ e : V ≃ₗ[K] WordSpace K w,
      ∀ g, T * ρ g * T =
        wordTransposeInCoordinates e * ρ g * wordTransposeInCoordinates e := by
  let e := E.toLinearEquiv.trans c
  let B := wordTransposeInCoordinates e
  have hE (g : G) (v : V) : E (ρ g v) = τ g (E v) :=
    LinearMap.congr_fun (E.isIntertwining' g) v
  have hB (v : V) : E (B v) = S (E v) := by
    apply c.injective
    change c (E.toLinearEquiv (E.toLinearEquiv.symm (c.symm (wordTranspose w (c (E v)))))) = _
    rw [E.toLinearEquiv.apply_symm_apply, c.apply_symm_apply, hc]
  have hB2 : B * B = 1 := wordTransposeInCoordinates_sq e
  refine ⟨e, ?_⟩
  intro g
  obtain ⟨h, hTg, hSg⟩ := ht g
  have hBg : B * ρ g = ρ h * B := by
    apply LinearMap.ext
    intro v
    apply E.toLinearEquiv.injective
    change E (B (ρ g v)) = E (ρ h (B v))
    rw [hB, hE, hE, hB]
    exact LinearMap.congr_fun hSg (E v)
  change T * ρ g * T = B * ρ g * B
  rw [hTg, hBg, mul_assoc, mul_assoc, hT, hB2]

end Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement.OuterConjugation
