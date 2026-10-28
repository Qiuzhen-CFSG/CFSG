module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.HighestWeightConstruction
public import Theory.Representation.PRegularSimpleCount

/-!
# The counting argument for D4 finite exhaustivity

Choose a rational irreducible for each restricted highest weight. Restricted
irreducibility and separation give `(2^n)^4` inequivalent finite irreducibles.
If another irreducible were omitted, adjoining it would produce one more than
this number. Modular trace independence bounds this enlarged family by the
number of odd-order conjugacy classes of the actual elementary subgroup,
contradicting the class bound.

The conclusion supplies an actual rational factor and a linear intertwining
equivalence on the given finite representation. All positive exponents,
including one, are covered. The four fundamental rational constructions and
the elementary class bound remain explicit obligations; the conditional results
below do not yet prove GLS3 Theorem 2.8.2 from geometry alone.

Sources: GLS3, Theorem 2.8.2; `refs/KGroup/GLS3/Chapter2St2.tex`, Section
13.3(b), the following semisimple-class count, and Section 14.
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Adjoining an omitted irreducible to the restricted family would exceed
the modular bound by odd-order conjugacy classes. Both the rational existence
and the class-count premises must be proved to finish the source theorem. -/
theorem restrictedExhaustivity_of_existence_of_classBound (S : Geometry K)
    (n : ℕ) (hn : 0 < n)
    (hirr : RestrictedIrreducibility S n) (hsep : RestrictedSeparation S n)
    (hexists : RestrictedRationalExistence S n) (hclasses : ElementaryClassBound S n) :
    RestrictedExhaustivity S n := by
  classical
  let : Finite (graphFieldElementarySubgroup
    S.diagram.toMulEquiv S.frobenius.onPoints n) := S.elementary_finite n hn
  let : Fintype (RestrictedWeight n) := Fintype.ofEquiv _ (restrictedWeightEquiv n).symm
  intro V hV
  by_contra! hnone
  choose A hA using fun a : RestrictedWeight n => hexists a.val a.property
  let W : Option (RestrictedWeight n) → FDRep k
      (graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n) := fun i =>
    match i with
    | none => V
    | some a => (A a).restrict (S.inclusion n)
  let M : Option (RestrictedWeight n) → Type u := fun i => W i
  let rep : ∀ i, Representation k
      (graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n) (M i) :=
    fun i => (W i).ρ
  have irr : ∀ i, Representation.IsIrreducible (rep i) := by
    intro i
    cases i with
    | none => exact hV
    | some a => exact hirr (A a) a.val a.property (hA a)
  have hpair : Pairwise fun i j => IsEmpty (Representation.Equiv (rep i) (rep j)) := by
    intro i j hij
    constructor
    intro φ
    cases i with
    | none =>
      cases j with
      | none => exact hij rfl
      | some a => exact (hnone (A a) a.val a.property (hA a)).false φ
    | some a =>
      cases j with
      | none => exact (hnone (A a) a.val a.property (hA a)).false φ.symm
      | some b =>
        apply hij
        congr 1
        exact Subtype.ext (hsep (A a) (A b) a.val b.val a.property b.property (hA a) (hA b) ⟨φ⟩)
  have hb := (Representation.irreducible_family_card_le_pRegularConjClasses M rep 2 hpair).trans
    hclasses
  have hcard := card_restrictedWeight n
  simp only [Nat.card_eq_fintype_card, Fintype.card_option] at hb hcard
  omega

/-- The remaining geometric inputs to exhaustivity are precisely the four
fundamental constructions and the class bound for the elementary subgroup. -/
theorem restrictedExhaustivity_of_fundamentals_of_classBound (S : Geometry K)
    (n : ℕ) (hn : 0 < n)
    (hirr : RestrictedIrreducibility S n) (hsep : RestrictedSeparation S n)
    (hfund : FundamentalRationalExistence S) (hclasses : ElementaryClassBound S n) :
    RestrictedExhaustivity S n :=
  restrictedExhaustivity_of_existence_of_classBound S n hn hirr hsep
    (restrictedRationalExistence_of_fundamentals S hfund n) hclasses

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
