module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.GeneralizedRows.TwoRestriction
public import Theory.Character.NilpotentRestriction
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Generalized ordinary rows from compatible local restrictions

Brauer's restriction criterion reduces genuine generalized-character realization
to nilpotent subgroups. The exponent-two branch is proved in `TwoRestriction`.
This module chooses primitive complex roots and combines that branch with the
cyclic restrictions and a classification of the nilpotent subgroups.

The local inputs remain explicit at this shared interface: actual compatible
power labels, the cyclic restriction calculation, and the cyclic-or-exponent-two
nilpotent subgroup reduction. `GeneralizedRows.Source` constructs all three from
`Janko1CentralizerData`, the order 175560, involution fusion and the supplied
`OrdinaryClassData`. It proves the source-group generalized-row existence theorem.
The class enumeration itself remains an independent input.

Source: Janko, J. Algebra 3 (1966), 147–186, ordinary-character calculation;
Gorenstein, *Finite Groups*, §16.6, printed p.482; Brauer induction as in Serre,
*Linear Representations of Finite Groups*, Chapter 10.
-/

noncomputable section
attribute [local instance] Fintype.ofFinite

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters

/-- Construct the exact generalized-row contract from its remaining local
inputs. The two-primary restrictions and the integral Brauer assembly are
discharged here; the cyclic restrictions concern actual subgroup representations. -/
public theorem ordinaryGeneralizedRows_of_local_restrictions
    {G : Type*} [Group G] [Finite G] {c : OrdinaryClassData G}
    (p : OrdinaryPowerLabels c)
    (htypes : ∀ H : Subgroup G, Group.IsNilpotent H →
      IsCyclic H ∨ ((∀ x : H, x ^ 2 = 1) ∧ Nat.card H ∣ 8))
    (hcyclic : ∀ (ζ₅ ζ₁₉ : ℂ), IsPrimitiveRoot ζ₅ 5 → IsPrimitiveRoot ζ₁₉ 19 →
      ∀ (i : Fin 15) (H : Subgroup G), IsCyclic H →
        IsGeneralizedCharacter (fun x : H => p.row ζ₅ ζ₁₉ i (x : G))) :
    Nonempty (OrdinaryGeneralizedRows c) := by
  let ζ₅ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)
  let ζ₁₉ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 19)
  have h₅ : IsPrimitiveRoot ζ₅ 5 := Complex.isPrimitiveRoot_exp 5 (by decide)
  have h₁₉ : IsPrimitiveRoot ζ₁₉ 19 := Complex.isPrimitiveRoot_exp 19 (by decide)
  refine ⟨{
    labels := p.labels
    labels_zero := p.labels_zero
    labels_orders := p.labels_orders
    labels_centralizers := p.labels_centralizers
    rootFive := ζ₅
    rootFive_primitive := h₅
    rootNineteen := ζ₁₉
    rootNineteen_primitive := h₁₉
    generalized := ?_ }⟩
  intro i
  apply isGeneralizedCharacter_of_nilpotent_restrictions (p.row_isClassFunction ζ₅ ζ₁₉ i)
  intro H hH
  rcases htypes H hH with hcyc | ⟨hsquare, hcard⟩
  · exact hcyclic ζ₅ ζ₁₉ h₅ h₁₉ i H hcyc
  · exact p.row_two_restriction ζ₅ ζ₁₉ i H hsquare hcard

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
