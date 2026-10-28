module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.DualFiltration.FieldFlag.PackedData

/-!
# Finite certificates for the dual adapted basis

The decoded bit planes equal the published field matrices. Packed column
products certify B C = 1 and B Dₐ = Aₐ B. `Arithmetic` proves soundness
over F₄; every finite identity here is checked in Lean’s kernel.
Source: the explicit induction supporting Guralnick–Malle I, Proposition
5.1, pp.15–16. Data provenance: `../source/README.md`.
-/

@[expose] public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.DualFiltration.FieldFlag.Packed
private instance basisRow (j : Fin 66) :
    Decidable (∀ i : Fin 66, decode (basis j) i = basisMatrix i j) := Fintype.decidableForallFintype
set_option Elab.async false in
lemma basis_decode : ∀ (j i : Fin 66), decode (basis j) i = basisMatrix i j := by decide +kernel

private instance inverseRow (j : Fin 66) :
    Decidable (∀ i : Fin 66, decode (inverse j) i = basisInverse i j) := Fintype.decidableForallFintype
set_option Elab.async false in
lemma inverse_decode : ∀ (j i : Fin 66), decode (inverse j) i = basisInverse i j := by decide +kernel

private instance ambientRow (a : Fin 2) (j : Fin 66) :
    Decidable (∀ i : Fin 66, decode (ambient a j) i = ambientMatrix a i j) := Fintype.decidableForallFintype
set_option Elab.async false in
lemma ambient_decode : ∀ (a : Fin 2) (j i : Fin 66), decode (ambient a j) i = ambientMatrix a i j := by decide +kernel

private instance adaptedRow (a : Fin 2) (j : Fin 66) :
    Decidable (∀ i : Fin 66, decode (adapted a j) i = adaptedMatrix a i j) := Fintype.decidableForallFintype
set_option Elab.async false in
lemma adapted_decode : ∀ (a : Fin 2) (j i : Fin 66), decode (adapted a j) i = adaptedMatrix a i j := by decide +kernel

set_option Elab.async false in
lemma packed_inverse : ∀ j : Fin 66, combine basis (inverse j) = (2^j.val, 0) := by decide +kernel
set_option Elab.async false in
lemma packed_action : ∀ (a : Fin 2) (j : Fin 66),
    combine basis (adapted a j) = combine (ambient a) (basis j) := by decide +kernel
end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.DualFiltration.FieldFlag.Packed
