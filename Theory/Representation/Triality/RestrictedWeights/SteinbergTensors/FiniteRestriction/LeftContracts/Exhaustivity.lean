module
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.HighestWeightConstruction
public import Theory.Representation.PRegularSimpleCount
/-!
# Finite exhaustion in the source left highest-weight convention

The actual restricted highest weights index q^4 inequivalent irreducibles.
Adjoining an omitted original module contradicts the odd-class count via
modular trace independence. This returns an actual rational lift and linear
intertwiner on the original finite group, retaining the exact earlier inputs.
The concrete triality source discharges these with its finite highest lines,
root-chart recovery and torus-class count.
Source: Steinberg 13.3(b) and GLS3 2.8.2.
-/
public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
/-- Adjoining an omitted irreducible to the restricted family would exceed
the modular bound by odd-order conjugacy classes. Both the rational existence
and the class-count premises must be proved to finish the source theorem. -/
theorem leftRestrictedExhaustivity_of_existence_of_classBound (S : Geometry K)
    (n : ℕ) (hn : 0 < n)
    (hirr : LeftRestrictedIrreducibility S n) (hsep : LeftRestrictedSeparation S n)
    (hexists : LeftRestrictedRationalExistence S n) (hclasses : ElementaryClassBound S n) :
    LeftRestrictedExhaustivity S n := by
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


end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
