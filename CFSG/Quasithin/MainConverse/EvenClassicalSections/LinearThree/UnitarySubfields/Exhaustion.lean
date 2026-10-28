module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.UnitarySubfields.Reduction
public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.UnitarySubfields.BorelCases
public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.UnitarySubfields.Exhaustion.Geometry
public import Mathlib.Order.Atoms.Finite

/-!
# Reduction of unitary exhaustion to maximal primitive subgroups

Every proper subgroup is contained in a maximal proper subgroup. The
geometric arguments in `Geometry` handle reducible lifts and lifts
permuting three independent lines. Solvable maximal subgroups also have
an envelope. The remaining maximal primitive subgroups divide according
to whether they have a nontrivial abelian normal subgroup, normal inside
the maximal subgroup itself.

The two primitive inputs below remain unproved. The first is the intrinsic
normal-subgroup argument leading to the solvable Singer and Hessian cases;
the second is the classification of primitive subgroups without abelian
normal subgroups, with actual model maps and proper unitary subfields.
This file is a conditional reduction, not the unconditional exhaustion
required by `psu3_even_isKGroup_of_exhaustion`.

Source: Hartley–Mitchell, GLS3, Theorem 6.5.3(a–i),
`refs/KGroup/GLS3/chapter6.tex`. Its shortened K-group proof does not
discharge either remaining primitive input here.
-/

namespace CFSG.Quasithin.MainConverse.UnitaryThreeSections.Exhaustion

open BenderSuzuki.MatrixGroups

/-- The geometric cases reduce intrinsic exhaustion to two precise maximal
primitive cases. Both premises must be discharged before source assembly. -/
public theorem envelope_of_maximal_primitive_cases
    {F : Type} [Field F] [Finite F] {n : ℕ} (J : HermitianForm 3 F)
    (habelian : ∀ M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      IsCoatom M → IsPrimitiveLift J M →
      (∃ A : Subgroup M, A.Normal ∧ IsMulCommutative A ∧ A ≠ ⊥) →
      Group.IsSolvable M)
    (hsemisimple : ∀ M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      IsCoatom M → IsPrimitiveLift J M → ¬ Group.IsSolvable M →
      (∀ A : Subgroup M, A.Normal → IsMulCommutative A → A = ⊥) →
      Envelope n M)
    (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hU : U ≠ ⊤) :
    Envelope n U := by
  classical
  obtain ⟨M, hM, hUM⟩ := (eq_top_or_exists_le_coatom U).resolve_left hU
  apply Envelope.subgroup (Subgroup.inclusion hUM) (Subgroup.inclusion_injective hUM)
  by_cases hred : IsReducible J M
  · exact envelope_of_reducible J M hred
  by_cases hlines : PreservesThreeLines J M
  · exact envelope_of_preservesThreeLines J M hlines
  have hprimitive : IsPrimitiveLift J M := ⟨hred, hlines⟩
  by_cases hsolv : Group.IsSolvable M
  · exact .solvable M hsolv
  by_cases hab : ∃ A : Subgroup M, A.Normal ∧ IsMulCommutative A ∧ A ≠ ⊥
  · exact .solvable M (habelian M hM hprimitive hab)
  apply hsemisimple M hM hprimitive hsolv
  intro A hnormal hcomm
  by_contra hne
  exact hab ⟨A, hnormal, hcomm, hne⟩

end CFSG.Quasithin.MainConverse.UnitaryThreeSections.Exhaustion
