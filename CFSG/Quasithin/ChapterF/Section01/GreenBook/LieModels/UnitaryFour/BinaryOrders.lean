module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.SylowGeometry
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.Geometry
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPlaneRadical.Structure
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.UnitaryOrder
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointIndex
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# Binary unitary parabolic orders

The actual SU₄(2) and PSU₄(2) models have order 25920. The isotropic-point
index gives the full point-parabolic order 576. The plane local factor has
order 960 from its Hermitian radical and SL₂(F₄) quotient. Its Borel
determinant lies in F₂ˣ, so maximality of the Borel in the full plane
parabolic identifies the local factor with that entire parabolic.

These are concrete inputs to the faithful-completion counting argument in
Aschbacher–Smith F.4.6 and F.4.24, printed pp.276–277 and 287–288.
No uniqueness or recognition statement is assumed here.
-/

@[expose] public section

open Theory.SpecificGroups.ClassicalUnitary
open Theory.SpecificGroups.HigherClassicalCovers
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.BinaryCompletion
noncomputable section
local notation "h1" => (Nat.le_refl 1)
local notation "F" => MatrixField 1
local notation "J" => standardForm 1 h1

theorem matrix_card : Nat.card (MatrixGroup 1 h1) = 25920 := by
  have hF : Nat.card F = 4 := by simpa using matrixField_card 1 h1
  have hc : ∀ x : F, (J).conj x = x ^ 2 := by
    intro x
    exact fieldConj_apply 1 x
  exact (Nat.card_congr (UnitaryTwo.specialEquivStandard J hF hc).toEquiv).trans
    UnitaryTwo.UnitaryOrder.card_standardSU

theorem projective_card : Nat.card (ProjectiveGroup 1 h1) = 25920 := by
  have hF : Nat.card F = 4 := by simpa using matrixField_card 1 h1
  have hc : ∀ x : F, (J).conj x = x ^ 2 := by
    intro x
    exact fieldConj_apply 1 x
  rw [← Nat.card_congr (UnitaryTwo.specialProjectiveEquiv J hF hc).toEquiv]
  exact matrix_card

theorem point_matrix_index : (pointParabolicMatrix 1 h1).index = 45 := by
  have h := UnitaryFourPointIndex.pointParabolic_index_eq_card F (fieldConj 1)
    (fieldConj_involutive 1 h1) 1 (by decide) (matrixField_card 1 h1) (fieldConj_apply 1)
  rw [UnitaryFourPointIndex.isotropicLine_card, matrixField_card 1 h1,
    PointLocal.fixedField_card 1 h1] at h
  exact h

theorem point_matrix_card : Nat.card (pointParabolicMatrix 1 h1) = 576 := by
  have h := (pointParabolicMatrix 1 h1).card_mul_index
  rw [point_matrix_index, matrix_card] at h
  omega

theorem point_card : Nat.card (pointParabolic 1 h1) = 576 := by
  change Nat.card ((pointParabolicMatrix 1 h1).map (projection 1 h1)) = 576
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective (pointParabolicMatrix 1 h1)
    (projection 1 h1) (projection_injective 1 h1)).toEquiv]
  exact point_matrix_card

theorem middle_card : Nat.card (overlap 1 h1) = 192 := overlap_card 1 h1

theorem local_plane_card : Nat.card (L2 1 h1) = 960 := by
  have h := (pCore 2 (L2 1 h1)).card_mul_index
  rw [L2TwoCore_card, Subgroup.index_eq_card,
    Nat.card_congr (L2QuotientEquivSL2 1 h1).toEquiv, Atlas.card_sl_two,
    show Nat.card (Representation.OrthogonalFourMinus.FiniteModel.Field 1) = 4 from
      GaloisField.card 2 2 (by decide)] at h
  norm_num at h ⊢
  omega

theorem middle_le_local_plane : overlap 1 h1 ≤ L2 1 h1 := by
  apply Subgroup.map_mono
  intro x hx
  apply (UnitaryFourPlaneLocal.mem_localFactor F J x).mpr
  refine ⟨hx.2, ?_⟩
  let a : UnitaryFourFlag.borelSU F J := ⟨x, hx⟩
  let t := (UnitaryFourSylow.torusCharacter F (fieldConj 1)
    (fieldConj_involutive 1 h1) a).2
  have hcard : Nat.card (PointLocal.FixedField 1)ˣ = 1 := by
    rw [Nat.card_units, PointLocal.fixedField_card 1 h1]
    norm_num
  let : Subsingleton (PointLocal.FixedField 1)ˣ :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  have ht : t = 1 := Subsingleton.elim _ _
  have hd := UnitaryFourSylow.torusCharacter_snd_val F (fieldConj 1)
    (fieldConj_involutive 1 h1) a
  change ((t : PointLocal.FixedField 1) : F) = _ at hd
  rw [ht] at hd
  have h10 := ((UnitaryFourFlag.mem_pointParabolicSU F J x).mp hx.1).1
  simpa [UnitaryFourPlaneLocal.restrictionMatrix, Matrix.det_fin_two, h10] using hd.symm

/-- At q=2 the full plane parabolic is its SL₂(F₄) local factor. -/
theorem plane_eq_local : planeParabolic 1 h1 = L2 1 h1 := by
  let P := planeParabolic 1 h1
  have hl : (overlap 1 h1).subgroupOf P < (L2 1 h1).subgroupOf P := by
    apply lt_of_le_of_ne (Subgroup.subgroupOf_mono P middle_le_local_plane)
    intro he
    have hmap := congrArg (fun Q : Subgroup P => Q.map P.subtype) he
    rw [Subgroup.map_subgroupOf_eq_of_le (show overlap 1 h1 ≤ P from
      by rw [← exact_overlap]; exact inf_le_right),
      Subgroup.map_subgroupOf_eq_of_le (L2_le_planeParabolic 1 h1)] at hmap
    have h := congrArg (fun Q : Subgroup (ProjectiveGroup 1 h1) => Nat.card Q) hmap
    rw [middle_card, local_plane_card] at h
    omega
  have he := (overlap_isCoatom_in_plane 1 h1).lt_iff.mp hl
  have hm := congrArg (fun Q : Subgroup P => Q.map P.subtype) he
  rw [Subgroup.map_subgroupOf_eq_of_le (L2_le_planeParabolic 1 h1),
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hm
  exact hm.symm

theorem plane_card : Nat.card (planeParabolic 1 h1) = 960 := by
  rw [plane_eq_local, local_plane_card]
theorem plane_matrix_card : Nat.card (planeParabolicMatrix 1 h1) = 960 := by
  have he : Nat.card (planeParabolic 1 h1) = Nat.card (planeParabolicMatrix 1 h1) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective (planeParabolicMatrix 1 h1)
      (projection 1 h1) (projection_injective 1 h1)).toEquiv).symm
  rw [plane_card] at he
  exact he.symm

theorem overlap_matrix_card : Nat.card (overlapMatrix 1 h1) = 192 := by
  have he : Nat.card (overlap 1 h1) = Nat.card (overlapMatrix 1 h1) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective (overlapMatrix 1 h1)
      (projection 1 h1) (projection_injective 1 h1)).toEquiv).symm
  rw [middle_card] at he
  exact he.symm

end
end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.BinaryCompletion
