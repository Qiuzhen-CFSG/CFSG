module

public import Theory.Representation.AlternatingSevenConjugatePair.Model.Extension
public import Theory.Representation.AlternatingSevenConjugatePair.Model.FixedSpaces
public import Theory.Representation.AlternatingSevenConjugatePair.Model.Structure
public import Theory.Representation.AlternatingSevenConjugatePair.Model.InnerElements
public import Theory.Representation.BinaryAlternatingSevenFixedPoints
public import Theory.LinearAlgebra.BinaryFourCubicNormalForm

/-!
# Construction and element calculations for the binary A₇ conjugate pair

The natural action is restricted through the actual A₇ → A₈ ≃ SL₄(2)
comparison. Its eight-dimensional S₇ extension, complementary coordinate
summands, faithfulness, and intertwining equivalences are constructed in
`Model.Extension`. The irreducibility and inequivalence proved in
`Model.Structure` instantiate this construction as the concrete `Model.pair`.
The equivalences `Model.pairFirstEquiv` and `Model.pairSecondEquiv` identify
its summands with the restricted natural four-space and its outer conjugate.

For every finite-dimensional `Pair`, `Pair.involution_fixedCodim` proves
codimension four for every involution, and `Pair.odd_prime_fixedCodim` gives
the lower bound four for every odd-prime-order element. Even involutions
move a plane in each faithful four-dimensional summand, while odd ones
interchange the two summands. The binary cubic normal-form theorem discharges
the three-cycle fixed-point premise in `Model.InnerElements`, proving that
the double-three-cycle fixes a plane in each summand of every pair. These
calculations use the given pair, without a module-classification assumption.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.8, printed p.389/PDF p.400, with standing hypotheses on printed p.377.
-/

public section

namespace Representation.AlternatingSevenConjugatePair

open BinaryOffender

noncomputable section

namespace Model

/-- The genuine binary conjugate pair on the eight-dimensional space `Four × Four`.
All representation-theoretic premises of the extension are discharged. -/
@[expose] def pair : Pair Eight :=
  pairOfIrreducibleInequivalent natural_isIrreducible outerNatural_isIrreducible
    natural_not_equiv_outerNatural

/-- The first summand is the natural four-space restricted along A₇ → A₈ ≃ SL₄(2). -/
@[expose] def pairFirstEquiv : pair.first.toRepresentation.Equiv natural := firstEquiv

/-- The second summand is the outer conjugate of that restricted natural four-space. -/
@[expose] def pairSecondEquiv : pair.second.toRepresentation.Equiv outerNatural := secondEquiv

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- Three-cycles have no nonzero fixed vectors in any faithful binary A₇ four-space.
The required cubic normal form is proved for every operator on this space. -/
theorem threeCycle_fixedPointFree
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) W)
    (hρ : Function.Injective ρ) (hdim : Module.finrank (ZMod 2) W = 4) :
    ∀ a : alternatingGroup (Fin 7), a.val.IsThreeCycle →
      ∀ v : W, ρ a v = v → v = 0 :=
  binaryAlternatingSeven_threeCycle_fixedPointFree_of_normalForm ρ hρ
    (BinaryFourCubic.exists_basis_fixedPlaneMatrix hdim)

/-- The product `(0 1 2)(3 4 5)` fixes a plane in every faithful binary A₇ four-space. -/
theorem doubleThreeCycle_fixed_finrank_of_faithful
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) W)
    (hρ : Function.Injective ρ) (hdim : Module.finrank (ZMod 2) W = 4) :
    Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers doubleThreeCycle)) = 2 :=
  doubleThreeCycle_fixed_finrank ρ hdim (threeCycle_fixedPointFree ρ hρ hdim)

end Model

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Every involution of S₇ has fixed codimension four in every conjugate pair. -/
theorem Pair.involution_fixedCodim (D : Pair V) (t : Equiv.Perm (Fin 7))
    (ht : orderOf t = 2) : fixedCodim D.representation (Subgroup.zpowers t) = 4 := by
  by_cases heven : t ∈ alternatingGroup (Fin 7)
  · let a : alternatingGroup (Fin 7) := ⟨t, heven⟩
    have ha : orderOf a = 2 := (Subgroup.orderOf_mk t heven).trans ht
    have hfirst := Model.involution_fixedCodim D.first.toRepresentation
      D.first_faithful D.first_dim a ha
    have hsecond := Model.involution_fixedCodim D.second.toRepresentation
      D.second_faithful D.second_dim a ha
    exact (D.inner_fixedCodim a).trans (by rw [hfirst, hsecond])
  · exact D.odd_involution_fixedCodim t ht heven

/-- The same explicit double-three-cycle fixes a plane in each summand of every pair. -/
theorem Pair.doubleThreeCycle_fixed_planes (D : Pair V) :
    Module.finrank (ZMod 2)
      (D.firstFixedSpace (Subgroup.zpowers Model.doubleThreeCycle.val)) = 2 ∧
    Module.finrank (ZMod 2)
      (D.secondFixedSpace (Subgroup.zpowers Model.doubleThreeCycle.val)) = 2 := by
  constructor
  · exact (cyclicSummandFixedEquiv D.representation D.first
      Model.doubleThreeCycle).finrank_eq.symm.trans
        (Model.doubleThreeCycle_fixed_finrank_of_faithful D.first.toRepresentation
          D.first_faithful D.first_dim)
  · exact (cyclicSummandFixedEquiv D.representation D.second
      Model.doubleThreeCycle).finrank_eq.symm.trans
        (Model.doubleThreeCycle_fixed_finrank_of_faithful D.second.toRepresentation
          D.second_faithful D.second_dim)

/-- The order-three witness in A₇ required by H.8, for the given pair. -/
theorem Pair.exists_order_three_fixed_planes (D : Pair V) :
    ∃ x : Equiv.Perm (Fin 7), x ∈ alternatingGroup (Fin 7) ∧ orderOf x = 3 ∧
      Module.finrank (ZMod 2) (D.firstFixedSpace (Subgroup.zpowers x)) = 2 ∧
      Module.finrank (ZMod 2) (D.secondFixedSpace (Subgroup.zpowers x)) = 2 :=
  ⟨Model.doubleThreeCycle.val, Model.doubleThreeCycle.property,
    (Subgroup.orderOf_coe Model.doubleThreeCycle).trans Model.doubleThreeCycle_order,
    D.doubleThreeCycle_fixed_planes⟩

end
end Representation.AlternatingSevenConjugatePair
