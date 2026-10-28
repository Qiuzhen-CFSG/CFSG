module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularInput
public import Theory.Representation.IrreducibleSimpleFaithful
public import Theory.SpecificGroups.Janko1.Model.Basic

/-!
# Faithfulness and coordinates for the source group's seven-dimensional module

An irreducible seven-dimensional GF(11) representation of a simple group is
faithful. The standard basis then gives an injective homomorphism to the
literal matrix group `Janko1.Ambient = GL₇(GF(11))` used by the relator-pair
consumer. This uses no recognition or comparison with the concrete J₁ model.

The conditional assembly below combines the unique algebraically closed
module with Frobenius descent. The two premises still require proofs:
the characteristic-eleven modular-character calculation from the source
centralizer data, and descent of a Frobenius-fixed irreducible. Thus this is
not yet the representation-existence theorem under the source hypotheses.
Source: Gorenstein, *Finite Groups*, §16.6, pp.482–483, reporting Janko,
J. Algebra 3 (1966), 147–186, DOI 10.1016/0021-8693(66)90010-X.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation

variable {G : Type*} [Group G] [IsSimpleGroup G]

/-- The modular-character construction need only produce an irreducible
degree-seven module over GF(11); simplicity supplies faithfulness. -/
public theorem exists_faithful_of_irreducible_seven
    (σ : Representation (ZMod 11) G (Fin 7 → ZMod 11))
    [Representation.IsIrreducible σ] :
    ∃ ρ : G →* Janko1.Ambient, Function.Injective ρ := by
  have hσ : Function.Injective σ :=
    σ.injective_of_simple_of_irreducible_of_one_lt_finrank (by simp)
  have hu : Function.Injective σ.asGroupHom := by
    intro x y hxy
    exact hσ (congrArg Units.val hxy)
  exact ⟨Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp σ.asGroupHom,
    Matrix.GeneralLinearGroup.toLin.symm.injective.comp hu⟩

/-- Conditional assembly of the modular-character and field-descent steps.
The source-theorem owner must establish both premises before asserting the
unconditional representation of the source group. -/
public theorem exists_faithful_of_unique_closed_seven
    (hmod : UniqueClosedSeven G)
    (hdescent : ∀ ρ : ClosedSeven G, Representation.IsIrreducible ρ →
      Nonempty (ρ.Equiv (Representation.frobeniusConjugate 11 1 ρ)) →
      ∃ σ : Representation (ZMod 11) G (Fin 7 → ZMod 11),
        Representation.IsIrreducible σ ∧
          Nonempty ((Representation.mapCoefficients
            (algebraMap (ZMod 11) ElevenClosure) σ).Equiv ρ)) :
    ∃ ρ : G →* Janko1.Ambient, Function.Injective ρ := by
  obtain ⟨ρ, hρ, hfrob⟩ := exists_frobenius_fixed_of_unique hmod
  obtain ⟨σ, hσ, _⟩ := hdescent ρ hρ hfrob
  let := hσ
  exact exists_faithful_of_irreducible_seven σ

end CFSG.Quasithin.Janko1SevenRepresentation
