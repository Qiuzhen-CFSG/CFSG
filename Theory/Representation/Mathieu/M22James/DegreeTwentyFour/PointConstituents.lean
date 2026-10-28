module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.SmallConstituents

/-!
# Schur degrees in the enlarged point-stabilizer window

For an irreducible binary SL₃(4) module with the central quadratic relation,
Schur-field extension gives a length-two defining-characteristic tensor word.
Its exact Frobenius period determines the Schur degree. In binary dimension
at most twenty-four, even dimension rules out period one; the remaining
word dimensions are three, eight and nine. Thus the Schur degree is two and
the binary degree belongs to the preliminary list 6, 16, 18.

This necessary list suffices to constrain the actual Mathieu restriction;
it is not asserted to be a complete central-character catalogue. In particular,
the sixteen-dimensional numerical possibility is retained here. The Mathieu
consumer also has divisibility by six and excludes that possibility.

Source: GLS III, 2.8.6, Remark 2.8.8 and 2.8.10(c), using the checked tensor
classification and descent from M22James/Uniqueness/PointRestriction/
LocalCatalogue/SmallConstituents. These are preparations for Guralnick–Malle I,
Proposition 5.1, pp.15–16.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.PointConstituents
open Representation Representation.SL3.BinaryDefiningFactors
open Representation.SL3FourLocalCatalogue
open scoped TensorProduct MonoidAlgebra

private lemma word_window (w : List Factor) (hlen : w.length = 2)
    (s d r : ℕ) (hd : d = s * wordDegree w) (heven : 2 * r = d)
    (hle : d ≤ 24) (hperiod : ∀ j, w.rotate j = w ↔ s ∣ j) :
    s = 2 ∧ (d = 6 ∨ d = 16 ∨ d = 18) := by
  have hs : s = 1 ∨ s = 2 := (Nat.dvd_prime Nat.prime_two).mp
    ((hperiod 2).mp (hlen ▸ List.rotate_length w))
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  rcases hs with rfl | rfl
  · have hr := (hperiod 1).mpr (one_dvd 1)
    have hab : a = b := (by simpa using hr : b = a ∧ a = b).2
    subst b
    cases a <;> simp [wordDegree, Factor.dimension] at hd <;> omega
  · have hr := (hperiod 1).not.mpr (by decide : ¬ 2 ∣ 1)
    cases a <;> cases b <;> simp_all [wordDegree, Factor.dimension]

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]
  (σ : Representation (ZMod 2) SL U) [IsIrreducible σ]
private abbrev SchurField := Module.End (ZMod 2)[SL] σ.asModule
private abbrev SplittingField := AlgebraicClosure (SchurField σ)
private instance schurField_charTwo : CharP (SchurField σ) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (SchurField σ)).injective 2

/-- The actual Schur degree and a necessary list of binary degrees in the
 enlarged point-stabilizer window. No Schur field is prescribed as input. -/
theorem schurDegree_eq_two_and_finrank_cases (hq : CentralQuadratic σ)
    (hd : Module.finrank (ZMod 2) U ≤ 24) :
    Representation.schurDegree 2 σ = 2 ∧
      (Module.finrank (ZMod 2) U = 6 ∨ Module.finrank (ZMod 2) U = 16 ∨
        Module.finrank (ZMod 2) U = 18) := by
  let : Algebra (ZMod 2) (SplittingField σ) := ZMod.algebra (SplittingField σ) 2
  let : IsAbsolutelyIrreducible σ.endFieldRep := endFieldRep_isAbsolutelyIrreducible σ
  let : IsIrreducible (extendScalars (SplittingField σ) σ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension σ.endFieldRep (SplittingField σ)
  let ι : F →+* SplittingField σ :=
    (IsAlgClosed.lift (R := ZMod 2) (S := F) (M := SplittingField σ)).toRingHom
  have hcard : Nat.card F = 2 ^ 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  obtain ⟨w, hw, ⟨e⟩⟩ := exists_word_equiv ι 2 hcard
    (extendScalars (SplittingField σ) σ.endFieldRep)
  have hp := word_rotate_iff_schurDegree_dvd σ ι w (hw ▸ hcard)
    (fun v hv => wordRep_isIrreducible ι 2 hcard v (hv.trans hw))
    (fun u v hu hv h => (wordRep_equiv_iff ι 2 hcard u v (hu.trans hw) (hv.trans hw)).mp h)
    ⟨e⟩
  have hdim : Module.finrank (ZMod 2) U = Representation.schurDegree 2 σ * wordDegree w := by
    rw [Representation.finrank_eq_schurDegree_mul 2 σ (SplittingField σ),
      e.toLinearEquiv.finrank_eq, finrank_wordSpace]
  let := fieldModule σ hq
  exact word_window w hw _ _ _ hdim (field_finrank σ hq) hd hp

omit [IsIrreducible σ] in
private theorem finrank_zero_or_six (hq : CentralQuadratic σ)
    (hd : Module.finrank (ZMod 2) U ≤ 6) :
    Module.finrank (ZMod 2) U = 0 ∨ Module.finrank (ZMod 2) U = 6 := by
  by_cases hz : Module.finrank (ZMod 2) U = 0
  · exact Or.inl hz
  let : Nontrivial U := Module.nontrivial_of_finrank_pos (by omega :
    0 < Module.finrank (ZMod 2) U)
  obtain ⟨N, hN⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional σ
  let := hN
  have hn := finrank_eq_six_of_irreducible N.toRepresentation
    (centralQuadratic_subrepresentation σ hq N)
    ((Submodule.finrank_le N.toSubmodule).trans (by omega))
  have hle := Submodule.finrank_le N.toSubmodule
  exact Or.inr (by omega)

omit [IsIrreducible σ] in
/-- Every small module with this central character has degree divisible by six;
 no simplicity or semisimplicity of the module is assumed. -/
theorem six_dvd_finrank_of_le_twelve (hq : CentralQuadratic σ)
    (hd : Module.finrank (ZMod 2) U ≤ 12) : 6 ∣ Module.finrank (ZMod 2) U := by
  by_cases hz : Module.finrank (ZMod 2) U = 0
  · exact hz ▸ dvd_zero 6
  let : Nontrivial U := Module.nontrivial_of_finrank_pos (by omega :
    0 < Module.finrank (ZMod 2) U)
  obtain ⟨N, hN⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional σ
  let := hN
  have hn := finrank_eq_six_of_irreducible N.toRepresentation
    (centralQuadratic_subrepresentation σ hq N)
    ((Submodule.finrank_le N.toSubmodule).trans hd)
  have hsum := Submodule.finrank_quotient_add_finrank N.toSubmodule
  have hq' := finrank_zero_or_six N.quotientRepresentation
    (centralQuadratic_quotient σ hq N) (by omega)
  rcases hq' with hq' | hq' <;> omega

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.PointConstituents
