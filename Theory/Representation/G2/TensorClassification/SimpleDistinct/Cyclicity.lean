module

public import Theory.Representation.G2.TensorClassification.SimpleDistinct.Cyclicity.TensorForms

/-!
# Cyclicity of the concrete G₂ tensor highest vector

Assuming precisely that the actual unipotent fixed space is the specified
highest line, its full-group orbit spans the tensor carrier. The proof uses the
concrete unipotent-invariant form pairing highest and opposite highest vectors,
and the finite two-group fixed-vector theorem on the orthogonal complement of
a hypothetical proper orbit span. It covers all-trivial words and boundary
weights without separate cases.

This is the conditional cyclicity input to GLS3, 2.8.6(a), 2.8.9 and 2.8.10(g),
used in Aschbacher--Smith G.9.3(10), printed pp.354,356--357. Highest-line
uniqueness remains an explicit premise, to be supplied by the assembly owner.
-/

public section
namespace Atlas.G2.TensorClassification
open Restricted
variable {F : Type*} [Field F] [CharP F 2] [Finite F]
  {K : Type*} [Field K] [Algebra F K] [CharP K 2]
  {n : ℕ}

/-- Highest-line uniqueness implies cyclicity of the specified highest vector
in every actual Frobenius tensor word. This includes the all-trivial word and
all boundary weights, and requires neither algebraic closure nor `n ≥ 2`. -/
theorem tensorHighestVector_orbit_span_of_fixedLine
    (hF : Nat.card F = 2 ^ n) (w : Fin n → Factor)
    (hfixed : ∀ v : TensorSpace F K w,
      (∀ g ∈ (unipotent : Subgroup (Model F)), tensorRep F K w g v = v) →
        ∃ c : K, v = c • tensorHighestVector F K w) :
    Submodule.span K (Set.range fun g : Model F =>
      tensorRep F K w g (tensorHighestVector F K w)) = ⊤ := by
  have hp : IsPGroup (ringChar K) (unipotent (K := F)) := by
    rw [ringChar.eq K 2]
    apply IsPGroup.of_card (n := n * 6)
    rw [card_unipotent, hF, pow_mul]
  apply Cyclicity.orbit_span_eq_top_of_fixedLine_pairing (tensorRep F K w)
    unipotent (by rw [ringChar.eq K 2]; decide) hp (tensorHighestVector F K w)
    hfixed (Cyclicity.tensorForm F K w) (Cyclicity.tensorForm_invariant F K w)
    (Steinberg.longestWeyl F)
  rw [Cyclicity.tensorForm_opposite_highestVector]
  exact one_ne_zero

end Atlas.G2.TensorClassification

end
