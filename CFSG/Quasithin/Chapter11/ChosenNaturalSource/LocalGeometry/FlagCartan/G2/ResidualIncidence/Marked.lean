module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ResidualIncidence.Model

/-!
# The actual marked G₂ stabilizers and residual quotients

A single inner conjugating element aligns all three spaces of the constructed
flag. The original quotient map L → L/O₂(L), followed by the supplied marking,
then identifies each relative normalizer and maps its solvable residual onto
the corresponding concrete local group. Its two-group kernel gives the
literal quotients Lᵢ/O₂(Lᵢ) ≃ PSL₂. The representative formula is retained for
the subsequent natural plane action; no central part of V is discarded.

Source: Aschbacher--Smith 11.0.2 and opening §11.1, printed pp.759--761.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation

open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2.ResidualIncidence
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover
open Atlas.G2.Natural.OrthogonalCover.SylowFlag
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

/-- One actual derived-group element aligns the complete chosen flag. -/
def alignment : SylowFlag.D S.field.Carrier :=
  (exists_marking S.field.Carrier (modelSylow S m)).choose

theorem alignment_sylow : (modelSylow S m : Subgroup (SylowFlag.D S.field.Carrier)) =
    movedSylow S.field.Carrier (alignment S m) :=
  (exists_marking S.field.Carrier (modelSylow S m)).choose_spec

/-- All three spaces use the same original marking and conjugating element. -/
theorem flag_space_eq (i : Fin 3) :
    (flag S m).space i = (movedIntrinsicFlag S.field.Carrier (alignment S m)).space i := by
  apply (movedIntrinsicFlag S.field.Carrier (alignment S m)).unique i _
    ((flag S m).dimension i)
  intro q
  exact (modelFlag S m).invariant i
    ⟨q.val, (alignment_sylow S m).symm ▸ q.property⟩

/-- The two marked model stabilizers, in the source point/plane order. -/
theorem modelStabilizer_flag (i : Fin 2) :
    (coordinates S m).modelStabilizer ((flag S m).space i.castSucc) =
      (standardParabolic S.field.Carrier i).map
        (MulAut.conj (alignment S m).val).toMonoidHom := by
  rw [flag_space_eq]
  fin_cases i
  · change stabilizer S.field.Carrier
      ((N1 S.field.Carrier).map (Natural.action S.field.Carrier (alignment S m).val)) = _
    rw [stabilizer_map, point_stabilizer]
    rfl
  · change stabilizer S.field.Carrier
      ((naturalPlane S.field.Carrier).map (Natural.action S.field.Carrier (alignment S m).val)) = _
    rw [stabilizer_map, plane_stabilizer]
    rfl

/-- The actual relative normalizer is the full inverse image of that parabolic. -/
theorem flag_normalizer (i : Fin 2) :
    L ⊓ normalizer ((flag S m).Vi i.castSucc : Set G) =
      (((standardParabolic S.field.Carrier i).map
        (MulAut.conj (alignment S m).val).toMonoidHom).comap
          (coordinates S m).quotientMap).map L.subtype := by
  rw [← modelStabilizer_flag]
  exact ((coordinates S m).normalizer_preimage _).symm

/-- The stabilizer isomorphism uses the inverse of the same inner conjugation. -/
def stabilizerEquiv (i : Fin 2) :
    (coordinates S m).modelStabilizer ((flag S m).space i.castSucc) ≃*
      standardParabolic S.field.Carrier i :=
  (MulEquiv.subgroupCongr (modelStabilizer_flag S m i)).trans
    ((MulAut.conj (alignment S m).val).subgroupMap _).symm

/-- The model residual is precisely the standard local group after alignment. -/
def modelResidualEquiv (i : Fin 2) :
    solvableResidual ((coordinates S m).modelStabilizer ((flag S m).space i.castSucc)) ≃*
      standardLocal S.field.Carrier i :=
  (stabilizerEquiv S m i).solvableResidualEquiv.trans
    (((solvableResidual (standardParabolic S.field.Carrier i)).equivMapOfInjective
      (standardParabolic S.field.Carrier i).subtype
      (standardParabolic S.field.Carrier i).subtype_injective).trans
        (MulEquiv.subgroupCongr (standard_residual S.field.Carrier (field_card_gt_two S) i)))

/-- The original residual maps to its concrete model using the original quotient. -/
def localProjection (i : Fin 2) : (flag S m).Li i →* standardLocal S.field.Carrier i :=
  (modelResidualEquiv S m i).toMonoidHom.comp
    ((coordinates S m).residualProjection ((flag S m).space i.castSucc))

theorem localProjection_surjective (i : Fin 2) : Function.Surjective (localProjection S m i) :=
  (modelResidualEquiv S m i).surjective.comp
    ((coordinates S m).residualProjection_surjective _)

/-- Representative formula: no independent abstract local-group isomorphism is chosen. -/
theorem localProjection_coe (i : Fin 2) (x : (flag S m).Li i) :
    (localProjection S m i x).val =
      (alignment S m).val⁻¹ * (show Model S.field.Carrier from
        (coordinates S m).quotientMap ⟨x.val, (localResidual_le _ x.property).1⟩) *
          (alignment S m).val := by
  change (MulAut.conj (alignment S m).val).symm
    (((coordinates S m).residualProjection ((flag S m).space i.castSucc) x).val.val) = _
  rw [(coordinates S m).residualProjection_coe]
  rfl

/-- Literal source quotients L_i/O₂(L_i), with the exact defining field. -/
def flag_Li_quotientEquiv (i : Fin 2) :
    ((flag S m).Li i ⧸ pCore 2 ((flag S m).Li i)) ≃* PSL(2,S.field.Carrier) :=
  ((coordinates S m).residualCoreQuotientEquiv _).trans
    ((QuotientGroup.congr _ _ (modelResidualEquiv S m i)
      (pCore_map_iso 2 (modelResidualEquiv S m i))).trans
        (standardCoreQuotientEquiv S.field.Carrier i))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2.ResidualIncidence
