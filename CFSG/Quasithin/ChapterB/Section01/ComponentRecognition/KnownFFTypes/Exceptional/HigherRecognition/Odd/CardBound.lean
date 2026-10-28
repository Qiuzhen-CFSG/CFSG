module

public import Theory.Representation.BinaryOffender.QuasisimpleCardBound
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.Odd.Reduction

/-!
# Discharging the FF cardinality premise of the odd exceptional reduction

For the native faithful irreducible binary action with F*(H) = N quasisimple
and irreducible restriction to N, the general maximization and Schur-field
argument proves |V| ≤ |Aut(N/Z(N))|² for every actual offender.

Applying `not_ff_of_absolute_component_estimates` therefore leaves only its
independent absolute degree estimate. The estimate must still be proved for
the actual odd exceptional carriers by the higher-recognition assembly owner;
this module does not claim the unconditional exceptional exclusion.

Source: Guralnick--Malle, *Classification of 2F-modules, I*, Section 2 and
Proposition 4.6; see `../Source.md` and `Reduction.lean`.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MonoidAlgebra

universe u v
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.Odd
variable {H : Type u} {V : Type v} [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) H V) [IsIrreducible ρ]
  (N : Subgroup H) [N.Normal] [IsQuasisimple N]
  [IsIrreducible (ρ.comp N.subtype)]

/-- The upper estimate in the literal source component situation. The general
theorem shows that the displayed generalized-Fitting equality is not needed. -/
theorem offender_card_le_quotient_aut_sq (hρ : Function.Injective ρ)
    (_hfit : generalizedFitting H = N) {A : Subgroup H} (hA : IsOffender ρ A) :
    Nat.card V ≤ Nat.card (MulAut (N ⧸ center N)) ^ 2 :=
  QuasisimpleCardBound.card_le_aut_central_quotient_sq ρ N hρ hA

/-- The native source application now requires only the independent degree
estimate over finite fields of characteristic two. -/
theorem not_ff_of_absolute_component_degree (hρ : Function.Injective ρ)
    (hfit : generalizedFitting H = N)
    (hdegree : ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      [Module K V] [FiniteDimensional K V] (σ : Representation K N V),
      Function.Injective σ → IsAbsolutelyIrreducible σ →
        Nat.card (MulAut (N ⧸ center N)) ^ 2 < 2 ^ Module.finrank K V) :
    ¬ IsFFModule ρ :=
  not_ff_of_absolute_component_estimates ρ N hρ
    (fun _ hA => offender_card_le_quotient_aut_sq ρ N hρ hfit hA) hdegree

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.Odd
