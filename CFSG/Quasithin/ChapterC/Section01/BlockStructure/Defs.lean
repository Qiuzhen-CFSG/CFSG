module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes
public import Theory.Representation.CentralizerField
public import Theory.GroupTheory.PResidual.PrimeSet
public import Theory.GroupTheory.PResidual.Empty

/-!
# Source data for the structural block lemmas

C.1.9 uses the upper core O₂,₃ and the actual alternating-three block
predicate. C.1.10 uses the intertwining endomorphism ring of the literal
binary conjugation representation on U/C_U(X); Schur and Wedderburn make
it a finite field with an odd unit group. C.1.11 uses a finite set product
of subnormal short groups. None of their conclusions is part of these
definitions.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
C.1.9--11, printed pp.123--124.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
variable {L : Type*} [Group L]
/-- End_X(Ũ(X)), formed from the actual binary conjugation representation. -/
noncomputable abbrev BlockEndRing (h : IsShort L) :=
  letI : IsElementaryAbelian 2 (blockU L) := h.elementary
  letI : IsElementaryAbelian 2 (BlockModule L) := h.module_elementary
  Representation.IntertwiningMap (ExceptionalRestrictions.moduleRepresentation h)
    (ExceptionalRestrictions.moduleRepresentation h)

/-- The primes dividing the unit group of the source endomorphism field. -/
@[expose] def blockEndPrimes (h : IsShort L) : Set Nat.Primes :=
  {p | p.val ∣ Nat.card (BlockEndRing h)ˣ}

theorem blockEndRing_isField (h : IsShort L) : IsField (BlockEndRing h) := by
  let := h.finite
  let := h.elementary
  let := h.module_elementary
  let := ExceptionalRestrictions.moduleRepresentation_irreducible h
  exact Representation.CentralizerField.end_isField (ExceptionalRestrictions.moduleRepresentation h)

theorem blockEndRing_finite (h : IsShort L) : Finite (BlockEndRing h) := by
  let := h.finite
  let := h.elementary
  let := h.module_elementary
  exact Representation.CentralizerField.end_finite (ExceptionalRestrictions.moduleRepresentation h)

theorem blockEndRing_units_odd (h : IsShort L) : Odd (Nat.card (BlockEndRing h)ˣ) := by
  let := h.finite
  let := h.elementary
  let := h.module_elementary
  let := ExceptionalRestrictions.moduleRepresentation_irreducible h
  exact Representation.CentralizerField.units_odd_card (ExceptionalRestrictions.moduleRepresentation h)

variable (G : Type*) [Group G]
/-- O₂,₃(G) is the upper two-then-three core, not the {2,3}-core. -/
@[expose] def upperTwoThreeCore : Subgroup G :=
  (pCore 3 (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G))

/-- The conditional A₃-block hypothesis in C.1.9. -/
@[expose] def BlockCommutationHypothesis : Prop :=
  (∃ B : Subgroup G, IsBlock B ∧ IsAlternatingBlock B 3) →
    generalizedFitting (upperTwoThreeCore G) = pCore 2 (upperTwoThreeCore G)

open scoped Pointwise
variable {G}
/-- A finite product of blocks, as equality of the actual set product with
K. This includes the empty product and does not assume commutation. -/
@[expose] def IsProductOfBlocks (K : Subgroup G) : Prop :=
  ∃ blocks : List (Subgroup G), (∀ X ∈ blocks, IsBlock X) ∧
    (blocks.map (fun X => (X : Set G))).prod = (K : Set G)
end CFSG.Quasithin.ChapterC

namespace CFSG.Quasithin.ChapterC

/-- The residual condition in C.1.10 imposes no restriction when π is empty. -/
theorem block_residual_condition_of_empty_primes {L Y : Type*}
    [Group L] [Group Y] [Finite Y] (h : IsShort L)
    (hπ : blockEndPrimes h = ∅) :
    piResidual (blockEndPrimes h) Y ⊔ commutator Y = ⊤ := by
  rw [hπ, piResidual_empty_eq_top, top_sup_eq]

end CFSG.Quasithin.ChapterC
