module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore
public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental
public import Theory.SpecificGroups.SL2.ThreeResidualCore
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.GeneralizedFitting.Defs
import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Native PSU₄(3) factor source

The standard projective involution in the concrete field-nine unitary model has
two literal determinant-one plane factors. Each is transported to SL₂(3),
the factors commute, and their projective images lie in the actual
involution centralizer. This is the native factor source used before the
remaining full centralizer residual and fused-intersection calculations.

Source: Aschbacher (1994), §45.1, and the concrete unitary model files.
-/

@[expose] public section

open Matrix BenderSuzuki.MatrixGroups
open Subgroup
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.SourceType
open RepresentativeCore
open Theory.GroupTheory
abbrev Plane := (form 2).specialSubgroup

noncomputable def planeEquivSL : Plane ≃* SpecialLinearGroup (Fin 2) (ZMod 3) := by
  have hp:IsPrimePow 3:=(isPrimePow_nat_iff _).mpr ⟨3,1,by decide,by decide,by decide⟩
  have hc:Nat.card FiniteField.Nine=3^2:=by norm_num
  have hj:∀x:FiniteField.Nine,conjugation x=x^3:=FiniteField.Nine.star_eq_cube
  let e := Classical.choice (OddFundamental.nonempty_specialTwoEquiv_odd conjugation star_involutive hp (by decide) hc hj)
  have hk:Nat.card (FixedBy.subfield FiniteField.Nine conjugation)=3:=
    (OddFundamental.form conjugation star_involutive 2).fixed_card_prime_power hp hc hj
  letI := Fintype.ofFinite (FixedBy.subfield FiniteField.Nine conjugation)
  let f:=ZMod.ringEquivOfPrime (FixedBy.subfield FiniteField.Nine conjugation) Nat.prime_three
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  exact e.trans (Atlas.fieldEquivSL 2 f.symm)

theorem plane_card : Nat.card Plane=24 :=
  (Nat.card_congr planeEquivSL.toEquiv).trans GLS3.Chapter5.SchurPresentation.sl23_card_eq

theorem plane_twoPerfect : IsPPerfect 2 Plane :=
  GLS3.Chapter5.SchurPresentation.sl23_twoPerfect.of_surjective planeEquivSL.symm.toMonoidHom
    planeEquivSL.symm.surjective

noncomputable def leftHom : Plane→*Carrier 4 :=
  OddFundamental.projectLeft conjugation star_involutive (m:=2) (n:=2)
noncomputable def rightHom : Plane→*Carrier 4 :=
  OddFundamental.projectRight conjugation star_involutive (m:=2) (n:=2)

theorem leftHom_injective : Function.Injective leftHom :=
  OddFundamental.projectLeft_injective conjugation star_involutive
theorem rightHom_injective : Function.Injective rightHom :=
  OddFundamental.projectRight_injective conjugation star_involutive

noncomputable def leftFactor : Subgroup (Carrier 4):=leftHom.range
noncomputable def rightFactor : Subgroup (Carrier 4):=rightHom.range
noncomputable def factorJoin : Subgroup (Carrier 4):=leftFactor⊔rightFactor

noncomputable def leftFactorEquiv : leftFactor≃*SpecialLinearGroup (Fin 2) (ZMod 3):=
  (MonoidHom.ofInjective leftHom_injective).symm.trans planeEquivSL
noncomputable def rightFactorEquiv : rightFactor≃*SpecialLinearGroup (Fin 2) (ZMod 3):=
  (MonoidHom.ofInjective rightHom_injective).symm.trans planeEquivSL

theorem factors_commute (a:Plane) (b:Plane) : Commute (leftHom a) (rightHom b) :=
  OddFundamental.factors_commute conjugation star_involutive a b

theorem block_eq (A B:Mat₂) : OddFundamental.blockMatrix A B=block A B := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem leftHom_mem (a:Plane) : leftHom a∈standardCentralizer := by
  apply (project_mem_standardCentralizer_iff (OddFundamental.left conjugation star_involutive (m:=2) (n:=2) a)).mpr
  left
  change OddFundamental.blockMatrix a.val.val (1:Mat₂) * standardInvolutionMatrix =
    standardInvolutionMatrix * OddFundamental.blockMatrix a.val.val (1:Mat₂)
  rw [block_eq]
  exact block_commutes_standard _ _

theorem rightHom_mem (a:Plane) : rightHom a∈standardCentralizer := by
  apply (project_mem_standardCentralizer_iff (OddFundamental.right conjugation star_involutive (m:=2) (n:=2) a)).mpr
  left
  change OddFundamental.blockMatrix (1:Mat₂) a.val.val * standardInvolutionMatrix =
    standardInvolutionMatrix * OddFundamental.blockMatrix (1:Mat₂) a.val.val
  rw [block_eq]
  exact block_commutes_standard _ _

theorem factorJoin_le : factorJoin≤standardCentralizer := by
  apply sup_le
  · rintro x ⟨a,rfl⟩;exact leftHom_mem a
  · rintro x ⟨a,rfl⟩;exact rightHom_mem a

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.SourceType
