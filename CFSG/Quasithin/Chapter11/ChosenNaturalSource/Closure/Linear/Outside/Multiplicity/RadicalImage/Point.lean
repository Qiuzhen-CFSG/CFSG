module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Seed
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.ParabolicResiduals
public import Theory.GroupTheory.PCoreInRestriction

/-! The literal SL₃ point residual, transported through the original quotient.
Source: Aschbacher--Smith 11.5.7, printed pp.781--782. -/

@[expose] public noncomputable section
open Subgroup Representation Matrix
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.RadicalImage
open LocalGeometry Matrix.PSL3.PointRadicalGeneration
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)
  (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))

def componentMap : L →* SL(3, E.input.field.Carrier) :=
  (Coordinates.sl3 m).quotientMap

def componentImage (A : Subgroup G) : Subgroup SL(3, E.input.field.Carrier) :=
  (A.subgroupOf L).map (componentMap E m)

theorem componentMap_ker : (componentMap E m).ker = pCore 2 L := by
  ext l
  change m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = 1 ↔ l ∈ pCore 2 L
  rw [← m.groupEquiv.map_one, m.groupEquiv.injective.eq_iff]
  exact QuotientGroup.eq_one_iff l

theorem componentImage_core (A : Subgroup G) (hA : A ≤ L) :
    componentImage E m (A.pCoreIn 2) = (componentImage E m A).pCoreIn 2 := by
  have hk : IsPGroup 2 (componentMap E m).ker := by
    rw [componentMap_ker]; exact pCore_isPGroup
  change ((A.pCoreIn 2).subgroupOf L).map _ = _
  rw [← pCoreIn_subgroupOf 2 A L hA]
  exact map_pCoreIn_of_ker_isPGroup _ hk _

private theorem residual_image (P : Submodule E.input.field.Carrier
    (Fin 3 → E.input.field.Carrier)) :
    componentImage E m (localResidual L ((Coordinates.sl3 m).preimage P)) =
      residualIn ((Coordinates.sl3 m).modelStabilizer P) := by
  let c := Coordinates.sl3 m
  ext x
  constructor
  · rintro ⟨l,hl,rfl⟩
    let y : localResidual L (c.preimage P) := ⟨l,hl⟩
    refine ⟨(c.residualProjection P y).val,(c.residualProjection P y).property,?_⟩
    exact c.residualProjection_coe P y
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨y,hy⟩ := (c.residualProjection_surjective P) ⟨x,hx⟩
    refine ⟨⟨y,(localResidual_le _ y.property).1⟩,y.property,?_⟩
    exact (c.residualProjection_coe P y).symm.trans (congrArg (fun z => z.val.val) hy)

private theorem modelStabilizer_eq (P : Submodule E.input.field.Carrier
    (Fin 3 → E.input.field.Carrier)) :
    (Coordinates.sl3 m).modelStabilizer P = parabolic P := by
  ext a
  change (∀ x, a.val *ᵥ x ∈ P ↔ x ∈ P) ↔ a ∈ parabolic P
  exact (@MulAction.mem_stabilizer_set SL(3,E.input.field.Carrier)
    (Fin 3 → E.input.field.Carrier) _ _ a (P : Set _)).symm

/-- The chosen solvable residual maps onto the genuine point-parabolic residual. -/
theorem componentImage_residual
    (P : Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace P) :
    componentImage E m E.L₁ = residualIn (parabolic P) := by
  have hp : E.V₁ = (Coordinates.sl3 m).preimage P :=
    congrArg D.centralQuotientPreimage hpoint
  change componentImage E m (localResidual L E.V₁) = _
  rw [hp, residual_image, modelStabilizer_eq]
  rfl

/-- A genuine coordinate change identifies the original residual with the
standard vector stabilizer. This retains the solvable residual convention. -/
theorem componentImage_residual_conjugate
    (P : Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace P)
    (a : SL(3, E.input.field.Carrier))
    (ha : conjugatePoint standardPoint a = P) :
    componentImage E m E.L₁ =
      (Matrix.PSL3.LinearThree.pointLocalSL E.input.field.Carrier).map
        (MulAut.conj a⁻¹).toMonoidHom := by
  rw [componentImage_residual E m P hpoint, ← ha, ← parabolic_conjugate]
  calc
    _ = (residualIn (parabolic standardPoint)).map (MulAut.conj a⁻¹).toMonoidHom :=
      (residualIn_map (parabolic standardPoint) (MulAut.conj a⁻¹)).symm
    _ = _ := ?_
  rw [parabolic_standardPoint]
  apply congrArg (Subgroup.map (MulAut.conj a⁻¹).toMonoidHom)
  apply Matrix.PSL3.LinearThree.ParabolicResiduals.pointParabolicSL_residual
  rw [E.input.field.card_eq]
  change 2 ^ 2 ≤ 2 ^ E.input.field.degree
  exact Nat.pow_le_pow_right (by decide : 0 < 2) E.input.nonbinary

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.RadicalImage
