module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.Roots

/-!
# The proper middle-line stabilizer in the unitary matrix model

The diagonal torus, Weyl element, and zero-first-coordinate roots preserve
`E(0,1,0)`. A root with first coordinate one moves this line. The stabilizer
is defined using the actual projective image of the matrix action; membership
is invariant under scalar representatives.

This is the proper-overgroup calculation for the unitary branch of GLS4,
Chapter 4, Lemma 3.2(h). Matrix conventions are those of Huppert II.10.12.
-/

noncomputable section
open Matrix BenderSuzuki.External
open scoped LinearAlgebra.Projectivization
namespace BenderSuzuki.MatrixGroups.HermitianForm.UnitaryPair
open OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E]

private noncomputable instance : MulAction (GL (Fin 3) E) (ℙ E (Fin 3 → E)) :=
  MulAction.compHom _ GeneralLinearGroup.toLin.toMonoidHom

private def middlePoint : ℙ E (Fin 3 → E) :=
  Projectivization.mk E (![0, 1, 0] : Fin 3 → E) (by simp)

private def middleGL : Subgroup (GL (Fin 3) E) :=
  MulAction.stabilizer _ (middlePoint (E := E))

/-- The stabilizer of the middle projective line in the actual PSU image. -/
public def middleSubgroup (J : HermitianForm 3 E) :
    Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  ((middleGL (E := E)).map ProjGenLinGroup.mk).comap
    (ProjectiveSpecialUnitaryMatrixGroup J).subtype

private theorem middleGL_iff (A : GL (Fin 3) E) :
    A ∈ middleGL ↔ A.val 0 1 = 0 ∧ A.val 2 1 = 0 := by
  change A • middlePoint = middlePoint ↔ _
  change GeneralLinearGroup.toLin A • Projectivization.mk E (![0, 1, 0] : Fin 3 → E) _ =
    Projectivization.mk E (![0, 1, 0] : Fin 3 → E) _ ↔ _
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨c, hc⟩
    change (c : E) • (![0, 1, 0] : Fin 3 → E) = A.val.mulVec ![0, 1, 0] at hc
    have h0 := congrFun hc 0
    have h2 := congrFun hc 2
    simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail] at h0 h2
    exact ⟨h0.symm, h2.symm⟩
  · rintro ⟨h0, h2⟩
    have h1 : A.val 1 1 ≠ 0 := by
      intro hz
      have hzero : A.val.mulVec ![0, 1, 0] = 0 := by
        ext i
        fin_cases i <;> simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail, h0, h2, hz]
      have hh := Matrix.mulVec_injective_of_isUnit (Units.isUnit A)
        (show A.val.mulVec ![0, 1, 0] = A.val.mulVec 0 by simpa using hzero)
      have hh1 := congrFun hh 1
      simp at hh1
    refine ⟨Units.mk0 (A.val 1 1) h1, ?_⟩
    change (A.val 1 1) • (![0, 1, 0] : Fin 3 → E) = A.val.mulVec ![0, 1, 0]
    funext i
    fin_cases i <;> simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail, h0, h2]

private theorem mem_middleSubgroup_iff (J : HermitianForm 3 E)
    (g : ProjectiveSpecialUnitaryMatrixGroup J) (A : GL (Fin 3) E)
    (hA : ProjGenLinGroup.mk A = g.val) :
    g ∈ middleSubgroup J ↔ A.val 0 1 = 0 ∧ A.val 2 1 = 0 := by
  change g.val ∈ (middleGL (E := E)).map ProjGenLinGroup.mk ↔ _
  rw [← hA]
  constructor
  · rintro ⟨C, hC, he⟩
    obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he
    have h0 := congrArg (fun M : GL (Fin 3) E => M.val 0 1) hc
    have h2 := congrArg (fun M : GL (Fin 3) E => M.val 2 1) hc
    have hC' := middleGL_iff C |>.mp hC
    simp [GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
      Fin.sum_univ_three, hC'.1, hC'.2] at h0 h2
    exact ⟨h0.symm, h2.symm⟩
  · intro h
    exact ⟨A, (middleGL_iff A).mpr h, rfl⟩

/-- Every diagonal torus element preserves the middle line. -/
public theorem torus_mem_middleSubgroup (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (k : Eˣ) :
    hermitianTorusPSU J hJ k ∈ middleSubgroup J := by
  apply (mem_middleSubgroup_iff J _ (hermitianTorusGL J k) rfl).mpr
  simp [hermitianTorusGL, hermitianTorusMatrix]

/-- The standard Weyl element preserves the middle line. -/
public theorem weyl_mem_middleSubgroup (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) :
    weyl J hJ ∈ middleSubgroup J := by
  apply (mem_middleSubgroup_iff J _ hermitianWeylGL rfl).mpr
  simp [hermitianWeylGL, hermitianWeylMatrix]

/-- The central root coordinate layer preserves the middle line. -/
public theorem root_mem_middleSubgroup (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0) :
    root J hJ z ∈ middleSubgroup J := by
  apply (mem_middleSubgroup_iff J _ (hermitianUnipotentGL J z) rfl).mpr
  simp [hermitianUnipotentGL, hermitianUnipotentMatrix, hz]

/-- A root with first coordinate one witnesses properness. -/
public theorem middleSubgroup_ne_top (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hfirst : ∃ z : hermitianUnipotentCoord J, z.val.1 = 1) :
    middleSubgroup J ≠ ⊤ := by
  obtain ⟨z, hz⟩ := hfirst
  intro htop
  have hm : root J hJ z ∈ middleSubgroup J := htop ▸ Subgroup.mem_top _
  have hh := ((mem_middleSubgroup_iff J _ (hermitianUnipotentGL J z) rfl).mp hm).1
  simp [hermitianUnipotentGL, hermitianUnipotentMatrix, hz] at hh

end BenderSuzuki.MatrixGroups.HermitianForm.UnitaryPair
