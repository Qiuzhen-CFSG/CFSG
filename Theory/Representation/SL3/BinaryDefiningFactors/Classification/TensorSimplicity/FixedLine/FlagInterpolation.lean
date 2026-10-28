module

public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.FixedLine.PolynomialModel
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.FixedLine.FlagInterpolation.GridSurjectivity

/-!
# Finite-grid injectivity for SL₃ flag polynomials

At weights `(q-1,q-1)`, straightening with `xy=(xy+z)-z` bounds the dimension
by `q^3`. Evaluation onto the `q^3` grid functions is surjective, using the
nonzero norm of `z^(q-1)(xy+z)^(q-1)` and the finite p-group orbit criterion.
Consequently evaluation is injective. Monotonicity of the two filtrations
gives the assertion for all weights `a,b<q`, including zero weights and `q=2`.
The proof does not require algebraic closure or tensor-map injectivity.

Source context: GLS III, 2.8.6(a), 2.8.9 and 2.8.10(c), in
`refs/KGroup/GLS3/chapter2.tex`. This is the polynomial interpolation input
to the upper-fixed-line argument, proved independently of word simplicity.
-/

public section
noncomputable section
open Matrix.PSL3Even.UnipotentGeometry
namespace Representation.SL3.BinaryDefiningFactors.TensorSimplicity.FixedLine
variable {F K : Type*} [Field F] [Field K] [Finite F] [CharP K 2]

/-- Flag polynomials with both fundamental weights below the field cardinality
are determined by their values on the entire embedded finite-field grid. -/
theorem eq_zero_of_flagSpace_eval_eq_zero (ι : F →+* K) (n a b : ℕ)
    (hcard : Nat.card F = 2^n) (ha : a < 2^n) (hb : b < 2^n)
    (p : Polynomial K) (hp : p ∈ flagSpace K a b)
    (heval : ∀ u : U F, MvPolynomial.eval (point ι u) p = 0) : p = 0 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (U F) := Fintype.ofFinite (U F)
  let m := Fintype.card F - 1
  have hm : m + 1 = Fintype.card F := Nat.sub_add_cancel Fintype.card_pos
  have hq : Fintype.card F = 2^n := by simpa [Nat.card_eq_fintype_card] using hcard
  have hsurj := gridEvaluation_surjective ι n hcard
  have hdimU : Module.finrank K (U F → K) = (Fintype.card F)^3 := by
    rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card,
      card_U, Nat.card_eq_fintype_card]
  have hdim : Module.finrank K (flagSpace K m m) = Module.finrank K (U F → K) := by
    apply le_antisymm
    · rw [hdimU, ← hm]
      exact finrank_flagSpace_le_cube m
    · exact LinearMap.finrank_le_finrank_of_surjective hsurj
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  have hpm : p ∈ flagSpace K m m :=
    flagSpace_mono (by omega) (by omega) hp
  have he : gridEvaluation ι m m ⟨p,hpm⟩ = gridEvaluation ι m m 0 := by
    ext u
    simpa [gridEvaluation] using heval u
  exact congrArg Subtype.val (hinj he)
end Representation.SL3.BinaryDefiningFactors.TensorSimplicity.FixedLine
