module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.UnitarySubfields.Exhaustion.Geometry
public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.UnitarySubfields.Exhaustion.PrimitiveAbelian.Basic
public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.UnitarySubfields.Exhaustion.PrimitiveAbelian.Clifford
public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.UnitarySubfields.Exhaustion.PrimitiveAbelian.Normalizers
public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.UnitarySubfields.Exhaustion.PrimitiveAbelian.ThreeSylow
public import Theory.Representation.NormalAbelianKernelOrder
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# The abelian-normal branch for primitive unitary subgroups

Let `A` be abelian and normal inside a projective subgroup `M`. Its full
inverse image in SU has central derived subgroup of exponent dividing three.
If that inverse image is nonabelian, it has a characteristic nonabelian
three-subgroup. The latter's degree-three matrix normalizer is solvable,
and hence so is `M`. This branch is unconditional in characteristic two;
it needs neither primitivity nor maximality.

If the inverse image is abelian and acts irreducibly, Schur's lemma and
finite division rings give a cyclic matrix centralizer. The character-weight
action gives a solvable automizer, so again `M` is solvable.

Clifford restriction supplies the required irreducibility: otherwise the
normal lift either acts by scalars, contradicting its nontrivial projective
image, or determines a decomposition into three lines preserved by the full
lift, contradicting primitivity. Combining the two normalizer arguments
proves solvability whenever a primitive projective subgroup has a nontrivial
abelian normal subgroup. The final theorem has exactly the existential
abelian-normal premise used by `envelope_of_maximal_primitive_cases`.

Source: the first part of the proof of Hartley–Mitchell, GLS3, Theorem 6.5.3,
`refs/KGroup/GLS3/chapter6.tex`, before the enumeration of simple groups.
-/

open Matrix BenderSuzuki.MatrixGroups

namespace CFSG.Quasithin.MainConverse.UnitaryThreeSections.Exhaustion.PrimitiveAbelian

variable {F : Type} [Field F] (J : HermitianForm 3 F)
  (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))

/-- A solvable matrix normalizer containing the lift gives solvability in PSU. -/
public theorem solvable_of_normalized_matrix_group (Q : Subgroup (GL (Fin 3) F))
    (hQ : (liftToGL J M).range ≤ Subgroup.normalizer (Q : Set (GL (Fin 3) F)))
    (hsolv : Group.IsSolvable (Subgroup.normalizer (Q : Set (GL (Fin 3) F)))) :
    Group.IsSolvable M := by
  let := hsolv
  let f := (liftToGL J M).codRestrict (Subgroup.normalizer (Q : Set (GL (Fin 3) F)))
    (fun g => hQ ⟨g, rfl⟩)
  let : Group.IsSolvable (specialLift J M) :=
    Group.isSolvable_of_isSolvable_injective (f := f) (by
      intro x y h
      apply liftToGL_injective J M
      exact congrArg (fun z : Subgroup.normalizer (Q : Set (GL (Fin 3) F)) =>
        (z : GL (Fin 3) F)) h)
  exact solvable_of_lift J M

/-- The central nonabelian lift case is intrinsically solvable. The full SU
inverse image of an abelian normal subgroup has a characteristic nonabelian
three-subgroup, whose faithful matrix normalizer is solvable. -/
public theorem solvable_of_nonabelian_normalLift [Finite F] [CharP F 2]
    (A : Subgroup M) [A.Normal] [IsMulCommutative A]
    (hnonab : ¬ IsMulCommutative (normalLift J M A)) : Group.IsSolvable M := by
  obtain ⟨Q, hchar, hthree, hn⟩ := exists_characteristic_nonabelian_three_subgroup
    (normalLift_commutator_le_center J M A) (normalLift_commutator_cube J M A) hnonab
  let : Q.Characteristic := hchar
  let B : Subgroup (specialLift J M) := Q.map (normalLift J M A).subtype
  let : B.Normal := ConjAct.normal_of_characteristic_of_normal
  let C := B.map (liftToGL J M)
  have hCthree : IsPGroup 3 C := (hthree.map (normalLift J M A).subtype).map (liftToGL J M)
  have hCnonab : ¬ IsMulCommutative C := by
    intro hc
    let : IsMulCommutative C := hc
    let e := (Q.equivMapOfInjective (normalLift J M A).subtype
      (normalLift J M A).subtype_injective).trans
      (B.equivMapOfInjective (liftToGL J M) (liftToGL_injective J M))
    apply hn
    apply IsMulCommutative.of_comm
    intro x y
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm' _ _
  have hnorm : (liftToGL J M).range ≤ Subgroup.normalizer (C : Set (GL (Fin 3) F)) := by
    simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map] using
      B.le_normalizer_map (liftToGL J M)
  exact solvable_of_normalized_matrix_group J M C hnorm
    (threeGroup_normalizer_isSolvable C hCthree hCnonab)

/-- Once Clifford restriction gives irreducibility of the abelian lift, its
centralizer is cyclic and its normalizer is solvable. -/
public theorem solvable_of_abelian_normalLift_irreducible [Finite F]
    (A : Subgroup M) [A.Normal] [IsMulCommutative (normalLift J M A)]
    (hM : ¬ IsReducible J M)
    (hirr : Representation.IsIrreducible
      ((Representation.generalLinearNatural 3).comp (normalLiftMatrix J M A).subtype)) :
    Group.IsSolvable M := by
  let : Representation.IsIrreducible (liftRepresentation J M) :=
    liftRepresentation_irreducible J M hM
  have horder := Representation.card_normal_abelian_ne_zero_of_faithful_irreducible
    (liftRepresentation J M) (normalLift J M A) (liftRepresentation_injective J M)
  have horder' : (Nat.card (normalLiftMatrix J M A) : F) ≠ 0 := by
    simpa only [normalLiftMatrix, Subgroup.card_map_of_injective (liftToGL_injective J M)]
      using horder
  let : Representation.IsIrreducible
      ((Representation.generalLinearNatural 3).comp (normalLiftMatrix J M A).subtype) := hirr
  let : IsMulCommutative (normalLiftMatrix J M A) :=
    Subgroup.map_isMulCommutative _ _
  exact solvable_of_normalized_matrix_group J M (normalLiftMatrix J M A)
    (normalLiftMatrix_normalized J M A)
    (abelian_normalizer_isSolvable_of_irreducible (normalLiftMatrix J M A) horder')

end CFSG.Quasithin.MainConverse.UnitaryThreeSections.Exhaustion.PrimitiveAbelian

namespace CFSG.Quasithin.MainConverse.UnitaryThreeSections.Exhaustion

/-- The two normalizer arguments, given irreducibility of the abelian lift.
The following theorem discharges this restriction premise by Clifford theory. -/
public theorem solvable_of_primitive_abelian_normal_of_restriction
    {F : Type} [Field F] [Finite F] [CharP F 2] (J : HermitianForm 3 F)
    (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hM : IsPrimitiveLift J M)
    (A : Subgroup M) [A.Normal] [IsMulCommutative A]
    (hrestriction : IsMulCommutative (PrimitiveAbelian.normalLift J M A) →
      Representation.IsIrreducible ((Representation.generalLinearNatural 3).comp
        (PrimitiveAbelian.normalLiftMatrix J M A).subtype)) :
    Group.IsSolvable M := by
  by_cases hab : IsMulCommutative (PrimitiveAbelian.normalLift J M A)
  · let := hab
    exact PrimitiveAbelian.solvable_of_abelian_normalLift_irreducible J M A hM.1
      (hrestriction hab)
  · exact PrimitiveAbelian.solvable_of_nonabelian_normalLift J M A hab

/-- A primitive projective unitary subgroup with a nontrivial abelian normal
subgroup is solvable in characteristic two. Normality is inside `M`.
Clifford theory supplies the irreducibility needed in the abelian lift case;
the nonabelian lift case has a solvable three-subgroup normalizer. -/
public theorem solvable_of_primitive_abelian_normal
    {F : Type} [Field F] [Finite F] [CharP F 2] (J : HermitianForm 3 F)
    (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hM : IsPrimitiveLift J M)
    (A : Subgroup M) [A.Normal] [IsMulCommutative A] (hA : A ≠ ⊥) :
    Group.IsSolvable M := by
  apply solvable_of_primitive_abelian_normal_of_restriction J M hM A
  intro hab
  let := hab
  exact PrimitiveAbelian.abelian_normalLift_irreducible J M hM A hA

/-- The abelian-normal input of `envelope_of_maximal_primitive_cases`, with the
source's even-unitary field parameters. The intrinsic argument above works
for every primitive subgroup and every nondegenerate Hermitian form. -/
public theorem solvable_of_maximal_primitive_abelian_normal
    {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (_hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (_hform : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (_hmax : IsCoatom M) (hM : IsPrimitiveLift J M)
    (habelian : ∃ A : Subgroup M, A.Normal ∧ IsMulCommutative A ∧ A ≠ ⊥) :
    Group.IsSolvable M := by
  let : CharP F 2 := ChapterF.Source.Unitary.charP_two n (by omega) hcard
  obtain ⟨A, hnormal, hcomm, hA⟩ := habelian
  let := hnormal
  let := hcomm
  exact solvable_of_primitive_abelian_normal J M hM A hA

end CFSG.Quasithin.MainConverse.UnitaryThreeSections.Exhaustion
