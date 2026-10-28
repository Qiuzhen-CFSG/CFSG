module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus.UnitaryModel
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus.UnitaryEmbedding.Action
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus.UnitaryEmbedding.SplitComparison

/-!
# A faithful embedding of the full quadratic-field SU₃ in G₂

The full identity-form SU₃ acts faithfully on the quadratic octonion algebra.
Conjugating that action by a multiplication-preserving F-linear comparison
with the literal split-octonion table produces the desired faithful map.
The compatibility theorem specifies the actual action on transported vectors.
The comparison is constructed explicitly in `SplitComparison` from a
quadratic norm minus one element and a nonzero trace-zero element.
`exists_unitary_model_embedding` supplies the precise second homomorphism of
`exists_twisted_cubic_torus_of_unitary_embeddings`, with no extra premises.

Source application: Aschbacher–Smith I.1.2–I.1.4, printed pp.407–408,
and GLS III §6.1, for the twisted cubic torus. No projective quotient is taken.
-/

@[expose] public section

open Matrix Atlas.SplitOctonion
namespace Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus.UnitaryEmbedding
noncomputable section
variable (F : Type*) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

/-- Conjugation by a proved algebra comparison transports the actual action. -/
def comparisonHom (e : Octonion F p ≃ₗ[F] Carrier F)
    (he : ∀ x y, e (octonionMul F p x y) = mul (e x) (e y)) :
    Atlas.Algebra.multiplicativeLinearAut (R := F) (octonionMul F p) →* Model F where
  toFun g := ⟨e.symm.trans (g.val.trans e), by
    intro x y
    change e (g.val (e.symm (mul x y))) =
      mul (e (g.val (e.symm x))) (e (g.val (e.symm y)))
    have hxy : e.symm (mul x y) = octonionMul F p (e.symm x) (e.symm y) := by
      apply e.injective
      rw [e.apply_symm_apply, he, e.apply_symm_apply, e.apply_symm_apply]
    rw [hxy, g.property, he]⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact e.apply_symm_apply x
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change e (g.val (h.val (e.symm x))) =
      e (g.val (e.symm (e (h.val (e.symm x)))))
    rw [e.symm_apply_apply]

theorem comparisonHom_injective (e : Octonion F p ≃ₗ[F] Carrier F)
    (he : ∀ x y, e (octonionMul F p x y) = mul (e x) (e y)) :
    Function.Injective (comparisonHom F p e he) := by
  intro g h hgh
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply e.injective
  have hx := congrArg (fun k : Model F => k.val (e x)) hgh
  change e (g.val (e.symm (e x))) = e (h.val (e.symm (e x))) at hx
  simpa only [e.symm_apply_apply] using hx

/-- The full SU₃, with its center retained, acts faithfully on split octonions
once the displayed multiplication-preserving comparison has been constructed. -/
def embeddingOfComparison (e : Octonion F p ≃ₗ[F] Carrier F)
    (he : ∀ x y, e (octonionMul F p x y) = mul (e x) (e y)) :
    (standardForm F p).specialSubgroup →* Model F :=
  (comparisonHom F p e he).comp (actionHom F p)

theorem embeddingOfComparison_injective (e : Octonion F p ≃ₗ[F] Carrier F)
    (he : ∀ x y, e (octonionMul F p x y) = mul (e x) (e y)) :
    Function.Injective (embeddingOfComparison F p e he) :=
  (comparisonHom_injective F p e he).comp (actionHom_injective F p)

theorem embeddingOfComparison_action (e : Octonion F p ≃ₗ[F] Carrier F)
    (he : ∀ x y, e (octonionMul F p x y) = mul (e x) (e y))
    (A : (standardForm F p).specialSubgroup) (x : Octonion F p) :
    (embeddingOfComparison F p e he A).val (e x) = e (x.1, A.val.val *ᵥ x.2) := by
  change e (actionEquiv F p A (e.symm (e x))) = _
  rw [e.symm_apply_apply]
  rfl


end
end Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus.UnitaryEmbedding

namespace Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus
open UnitaryEmbedding
noncomputable section
variable (F : Type*) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

/-- The full identity-form special unitary group acts on the literal split
 octonions. The cardinality hypothesis identifies conjugation with x ↦ x^p. -/
def unitaryEmbedding (_hF : Nat.card F = p) (hp : 3 < p) :
    (standardForm F p).specialSubgroup →* Model F :=
  embeddingOfComparison F p (splitComparison F p hp) (splitComparison_mul F p hp)

theorem unitaryEmbedding_injective (hF : Nat.card F = p) (hp : 3 < p) :
    Function.Injective (unitaryEmbedding F p hF hp) :=
  embeddingOfComparison_injective F p (splitComparison F p hp) (splitComparison_mul F p hp)

/-- The map acts through the proved comparison by the actual matrix action. -/
theorem unitaryEmbedding_action (hF : Nat.card F = p) (hp : 3 < p)
    (A : (standardForm F p).specialSubgroup) (x : Octonion F p) :
    (unitaryEmbedding F p hF hp A).val (splitComparison F p hp x) =
      splitComparison F p hp (x.1, A.val.val *ᵥ x.2) :=
  embeddingOfComparison_action F p (splitComparison F p hp) (splitComparison_mul F p hp) A x

/-- The second geometric input of the twisted cubic torus construction,
with every algebra comparison and descent premise discharged. -/
theorem exists_unitary_model_embedding (hF : Nat.card F = p) (hp : 3 < p) :
    ∃ ι : (standardForm F p).specialSubgroup →* Model F, Function.Injective ι :=
  ⟨unitaryEmbedding F p hF hp, unitaryEmbedding_injective F p hF hp⟩

end
end Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus
