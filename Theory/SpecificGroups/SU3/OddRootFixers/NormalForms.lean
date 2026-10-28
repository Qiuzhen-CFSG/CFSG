module

public import Theory.SpecificGroups.SU3.BorelTorus.Basic
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.UnitaryConjugation
public import Mathlib.GroupTheory.Sylow

/-!
# Matrix normal forms for marked unitary root fixers

These predicates describe intermediate matrix conclusions, not hypotheses
of the odd-order root-fixer theorem. The root is the actual upper Hermitian
unipotent image. The conjugating automorphism must carry the specified Sylow
subgroup onto that image. The actor formula is retained on SU₃ itself, or
on its literal image in PGL₃, respectively.

An upper triangular unitary representative with equal outer diagonal entries
is the output of removing the field parameter. Conjugacy inside the root
group should then make it diagonal. `OddRootFixers` proves that the latter
matrix conclusion supplies the marked PSL₂ subgroup; existence of these
normal forms from odd order remains a separate proof obligation.

Source: GLS4, Chapter 4, Lemma 3.6(c,d), used in Chapter 2, Lemma 13.2.
-/

public section
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddRootFixers
open BorelTorus
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- The triangular root-centralizing matrix shape. -/
@[expose] def IsRootTriangular (d : J.unitarySubgroup) : Prop :=
  d.val.val 1 0 = 0 ∧ d.val.val 2 0 = 0 ∧ d.val.val 2 1 = 0 ∧
    d.val.val 0 0 = d.val.val 2 2

/-- A diagonal unitary matrix with equal entries on the two outer coordinates. -/
@[expose] def IsRootDiagonal (d : J.unitarySubgroup) : Prop :=
  (∀ i j, i ≠ j → d.val.val i j = 0) ∧ d.val.val 0 0 = d.val.val 2 2

variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

/-- A marked matrix formula in the actual special-unitary group. -/
@[expose] def HasSpecialRootForm (shape : J.unitarySubgroup → Prop)
    (P : Sylow 2 J.specialSubgroup) (a : MulAut J.specialSubgroup) : Prop :=
  ∃ (e : MulAut J.specialSubgroup) (d : J.unitarySubgroup),
    shape d ∧ (P : Subgroup J.specialSubgroup).map e.toMonoidHom = specialRoot J hJ ∧
    ∀ x : J.specialSubgroup,
      (MulAut.congr e a x).val = d.val * x.val * d.val⁻¹

/-- A marked matrix formula in the actual projective image. -/
@[expose] def HasProjectiveRootForm (shape : J.unitarySubgroup → Prop)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) : Prop :=
  ∃ (e : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (d : J.unitarySubgroup),
    shape d ∧ (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map e.toMonoidHom =
      projectiveRoot J hJ ∧ MulAut.congr e a = J.unitaryConj d

end BenderSuzuki.MatrixGroups.HermitianForm.OddRootFixers
