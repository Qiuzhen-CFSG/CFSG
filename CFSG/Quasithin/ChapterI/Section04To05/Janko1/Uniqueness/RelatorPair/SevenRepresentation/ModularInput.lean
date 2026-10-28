module

public import Theory.Representation.EndFieldFrobenius
public import Theory.Representation.CoefficientReduction

/-!
# The modular-character input to the J₁ representation construction

Gorenstein, *Finite Groups*, §16.6, p.482, describes Janko's construction as
first proving existence and uniqueness of the absolutely irreducible module
of degree seven in characteristic eleven, then realizing it over GF(11).
Here the former conclusion is stated over the actual algebraic closure of
GF(11), with uniqueness expressed by an intertwining equivalence.

Uniqueness implies invariance under coefficient Frobenius because that twist
preserves irreducibility and dimension. This module proves that implication;
it does not establish the modular-character input from the local hypotheses,
nor does it descend the module to GF(11).
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation

public instance eleven_prime : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- The actual coefficient field used for the modular-character calculation. -/
public abbrev ElevenClosure := AlgebraicClosure (ZMod 11)

/-- Seven-dimensional representations over the algebraic closure of GF(11). -/
public abbrev ClosedSeven (G : Type*) [Group G] :=
  Representation ElevenClosure G (Fin 7 → ElevenClosure)

/-- The missing modular-character conclusion, without faithfulness or field
descent built into its statement. -/
@[expose] public def UniqueClosedSeven (G : Type*) [Group G] : Prop :=
  ∃ ρ : ClosedSeven G, Representation.IsIrreducible ρ ∧
    ∀ σ : ClosedSeven G, Representation.IsIrreducible σ → Nonempty (ρ.Equiv σ)

/-- The unique degree-seven irreducible is fixed, up to an actual intertwiner,
by coefficient Frobenius. This is the input for finite-field descent. -/
public theorem exists_frobenius_fixed_of_unique {G : Type*} [Group G]
    (hmod : UniqueClosedSeven G) :
    ∃ ρ : ClosedSeven G, Representation.IsIrreducible ρ ∧
      Nonempty (ρ.Equiv (Representation.frobeniusConjugate 11 1 ρ)) := by
  obtain ⟨ρ, hρ, huniq⟩ := hmod
  let := hρ
  exact ⟨ρ, hρ, huniq _ (Representation.frobeniusConjugate_isIrreducible 11 1 ρ)⟩

end CFSG.Quasithin.Janko1SevenRepresentation
