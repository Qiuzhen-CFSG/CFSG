module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularInput
public import Theory.Representation.FrobeniusFixedDescent

/-!
# Prime-field realization of the seven-dimensional module

An irreducible seven-dimensional representation over the actual algebraic
closure of GF(11), fixed up to equivalence by coefficient Frobenius, has an
irreducible model on `Fin 7 → ZMod 11`. Its coefficient extension along the
literal algebra map is equivalent to the given representation.

The general Frobenius descent theorem constructs the fixed basis and the
prime-field matrices. No descended module, invariant basis, or matrix
cocycle solution is assumed. This discharges step 3 of Gorenstein,
*Finite Groups*, §16.6, p.482; see `Source.md`. The modular-character
existence and uniqueness input is independent and remains with its owner.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation

/-- The Frobenius-invariant closed seven-dimensional irreducible is realizable
on the literal GF(11) coordinate module. -/
public theorem exists_prime_field_seven_of_frobenius_equiv
    {G : Type*} [Group G] [Finite G]
    (ρ : ClosedSeven G) (hρ : Representation.IsIrreducible ρ)
    (hfrob : Nonempty (ρ.Equiv (Representation.frobeniusConjugate 11 1 ρ))) :
    ∃ σ : Representation (ZMod 11) G (Fin 7 → ZMod 11),
      Representation.IsIrreducible σ ∧
        Nonempty ((Representation.mapCoefficients
          (algebraMap (ZMod 11) ElevenClosure) σ).Equiv ρ) :=
  Representation.exists_irreducible_primeField_model_of_frobenius_equiv 11
    ρ (Pi.basisFun ElevenClosure (Fin 7)) hρ hfrob

end CFSG.Quasithin.Janko1SevenRepresentation
