module

public import Theory.Representation.BinaryOffender.QuasisimpleCardBound.Maximizer
public import Theory.Representation.BinaryOffender.QuasisimpleCardBound.ScalarBound
public import Theory.GroupTheory.Covering

/-!
# A quasisimple FF-module cardinality bound

Let a finite group H act faithfully and irreducibly on a finite binary module
V, with irreducible restriction to a normal quasisimple subgroup N. Every
actual offender forces |V| ≤ |Aut(N/Z(N))|².

Exponent-one maximization gives |V| ≤ |H|. For the component's actual Schur
field E, the centralizer and conjugation estimates give
|H| ≤ |E| |Aut(N/Z(N))|, while the faithful perfect action gives |E|² ≤ |V|.
Cancellation first bounds |E| by |Aut(N/Z(N))| and then bounds |V| by its
square. In fact only nontriviality and perfectness of N are needed, and no
generalized-Fitting hypothesis is required.

Source: the exponent-one version of Guralnick--Malle,
*Classification of 2F-modules, I*, Section 2, Lemma 2.1, and the cardinality
comparison in Proposition 4.6. This proves the FF estimate independently;
it assumes neither a degree estimate nor an FF classification.
-/

public section
open Representation Representation.BinaryOffender Subgroup Theory.GroupTheory
open scoped MonoidAlgebra

namespace Representation.BinaryOffender.QuasisimpleCardBound
variable {H V : Type*} [Group H] [Finite H] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) H V)
  [IsIrreducible ρ] (N : Subgroup H) [N.Normal]
  [IsIrreducible (ρ.comp N.subtype)]

/-- A normal nontrivial perfect irreducible actor suffices for the square bound. -/
theorem card_le_aut_central_quotient_sq_of_perfect [Group.IsPerfect N] [Nontrivial N]
    (hρ : Function.Injective ρ) {A : Subgroup H} (hA : IsOffender ρ A) :
    Nat.card V ≤ Nat.card (MulAut (N ⧸ center N)) ^ 2 := by
  let E := Module.End (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype))
  have hV := card_le_group_of_offender ρ hρ hA
  have hH := group_card_le_endField_mul_aut ρ N hρ
  have hE := endField_sq_le_card ρ N hρ
  have hq : Nat.card E ≤ Nat.card (MulAut (N ⧸ center N)) := by
    apply Nat.le_of_mul_le_mul_left (c := Nat.card E) _ Nat.card_pos
    simpa only [← pow_two] using hE.trans (hV.trans hH)
  calc
    Nat.card V ≤ Nat.card E * Nat.card (MulAut (N ⧸ center N)) := hV.trans hH
    _ ≤ Nat.card (MulAut (N ⧸ center N)) * Nat.card (MulAut (N ⧸ center N)) :=
      Nat.mul_le_mul_right _ hq
    _ = Nat.card (MulAut (N ⧸ center N)) ^ 2 := (pow_two _).symm

/-- Every offender in the native quasisimple-component situation satisfies the
automorphism-square estimate, without needing F*(H) = N. -/
theorem card_le_aut_central_quotient_sq [IsQuasisimple N]
    (hρ : Function.Injective ρ) {A : Subgroup H} (hA : IsOffender ρ A) :
    Nat.card V ≤ Nat.card (MulAut (N ⧸ center N)) ^ 2 := by
  let : IsSimpleGroup (N ⧸ center N) := (inferInstance : IsQuasisimple N).simple
  let : Nontrivial N := (QuotientGroup.mk'_surjective (center N)).nontrivial
  exact card_le_aut_central_quotient_sq_of_perfect ρ N hρ hA

end Representation.BinaryOffender.QuasisimpleCardBound
