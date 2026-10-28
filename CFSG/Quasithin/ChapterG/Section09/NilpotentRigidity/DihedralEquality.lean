module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.Induction
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.SpaceTransport
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.Centralizers
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep

/-!
# Equality in the degree bounds for dihedral products

This module classifies faithful binary actions of embedded odd-prime
dihedral products at the cubic and five-factor degree bounds. It proves
the classified-module centralizer premise from splitting, closes the
positive-rank step by strong induction, and transports the resulting
internal decomposition to the actual embedded range.

All summands are actual displacement spaces. The group and space
equivalences preserve their canonical inclusions, the smaller
classification's factor count is retained when appending a block, and
the exceptional D₁₀ factor stays first. In the exceptional half-space
estimate the bound is `2(n + 1)` for `n = |J|`, correcting the printed
`m` in (J2).

Only the splitting, degree, and orthogonal-pair theorems from
`NilpotentRigidity.Contracts` remain explicit inputs. The parent G.9.2
assembly supplies those inputs and the group-theoretic extraction.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
G.9.2, printed pp.351--353, PDF pp.362--364.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity

universe u v

/-- Equality classification at every rank, with the commuting-involution
premise discharged and only the three permitted upstream inputs remaining. -/
theorem DihedralEquality.equalityAt_of_inputs
    (split : DihedralSplittingTheorem.{v}) (bounds : DihedralDegreeTheorem.{v})
    (pair : OrthogonalPairTheorem.{v}) :
    ∀ r, DihedralEquality.EqualityAt.{v} r :=
  DihedralEquality.equalityAt_of_positiveStep
    (DihedralEquality.positiveEqualityStep_of_inputs split bounds pair
      (DihedralEquality.classifiedInvolutionCentralizer_of_inputs split))

/-- The two equality cases for every embedded dihedral product in a faithful
binary representation. The output gives actual internal group and space
decompositions, including the natural orthogonal actions and the exceptional
degree-four D₁₀ factor at index zero. -/
theorem dihedralEqualityCases_of_inputs
    (split : DihedralSplittingTheorem.{v}) (bounds : DihedralDegreeTheorem.{v})
    (pair : OrthogonalPairTheorem.{v})
    {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hfaith : Function.Injective ρ) :
    HasDihedralEqualityCases ρ :=
  dihedralEqualityCases_of_uniform
    (DihedralEquality.equalityAt_of_inputs split bounds pair) ρ hfaith

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity
