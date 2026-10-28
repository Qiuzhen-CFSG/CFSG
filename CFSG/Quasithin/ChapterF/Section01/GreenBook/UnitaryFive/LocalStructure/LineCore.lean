module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.LineCore.Parameters
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.LineCore.Levi
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.LineCore.Parabolic
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Matrices
public import Theory.GroupTheory.PCoreSurjective
public import Theory.Frattini.OmegaProducts

/-!
# The unitary-five line residual and its canonical two-core

At parameter four the actual solvable residual is the radical–SU₃ subgroup
and the kernel of the cubic character, so it has index three in the line
parabolic. Its surjective Levi map has the full unipotent coordinate group
as kernel. Since the actual SU₃ group has trivial two-core, this kernel is
the canonical two-core of the residual. The first isomorphism theorem gives
the actual quotient equivalence to SU₃(4), with its value on quotient
representatives equal to the matrix Levi projection.

The core has center equal to its commutator and Frattini subgroups, order
`4^7`, and center order four. Its image under the residual inclusion is
exactly the full matrix unipotent subgroup. The whole flag overlap is the
preimage of the SU₃ isotropic-line stabilizer and hence has index 65 in the
line parabolic. All these conclusions have only the model as input; the
earlier conditional assembly interfaces are preserved below.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.11--12(7), printed pp.262--264.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
variable (M : Model 4)

/-- A genuine Levi map with the computed coordinate kernel identifies the canonical core. -/
theorem leftLeviKernel_eq_pCore
    (f : M.leftLocal →* M.LocalUnitaryGroup) (hf : Function.Surjective f)
    (e : f.ker ≃* M.LineRadicalCoordinates) (hL : pCore 2 M.LocalUnitaryGroup = ⊥) :
    f.ker = pCore 2 M.leftLocal := by
  have hk : IsPGroup 2 f.ker := M.lineRadicalCoordinates_isPGroup.of_equiv e.symm
  have h := f.comap_pCore_of_ker_isPGroup hf hk
  rwa [hL, MonoidHom.comap_bot] at h

/-- The conditional quotient identification uses the canonical two-core. -/
noncomputable def leftLocalQuotientEquiv_of_leviMap
    (f : M.leftLocal →* M.LocalUnitaryGroup) (hf : Function.Surjective f)
    (e : f.ker ≃* M.LineRadicalCoordinates) (hL : pCore 2 M.LocalUnitaryGroup = ⊥) :
    (M.leftLocal ⧸ pCore 2 M.leftLocal) ≃* M.LocalUnitaryGroup :=
  (QuotientGroup.quotientMulEquivOfEq (M.leftLeviKernel_eq_pCore f hf e hL).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- The computed kernel coordinates transfer to the canonical two-core. -/
noncomputable def leftCoreEquivCoordinates_of_leviMap
    (f : M.leftLocal →* M.LocalUnitaryGroup) (hf : Function.Surjective f)
    (e : f.ker ≃* M.LineRadicalCoordinates) (hL : pCore 2 M.LocalUnitaryGroup = ⊥) :
    pCore 2 M.leftLocal ≃* M.LineRadicalCoordinates :=
  (MulEquiv.subgroupCongr (M.leftLeviKernel_eq_pCore f hf e hL).symm).trans e

theorem card_leftCore_of_leviMap
    (f : M.leftLocal →* M.LocalUnitaryGroup) (hf : Function.Surjective f)
    (e : f.ker ≃* M.LineRadicalCoordinates) (hL : pCore 2 M.LocalUnitaryGroup = ⊥) :
    Nat.card (pCore 2 M.leftLocal) = 4 ^ 7 :=
  (Nat.card_congr (M.leftCoreEquivCoordinates_of_leviMap f hf e hL).toEquiv).trans
    M.card_lineRadicalCoordinates

theorem card_center_leftCore_of_leviMap
    (f : M.leftLocal →* M.LocalUnitaryGroup) (hf : Function.Surjective f)
    (e : f.ker ≃* M.LineRadicalCoordinates) (hL : pCore 2 M.LocalUnitaryGroup = ⊥) :
    Nat.card (Subgroup.center (pCore 2 M.leftLocal)) = 4 :=
  (Nat.card_congr (Subgroup.centerCongr
    (M.leftCoreEquivCoordinates_of_leviMap f hf e hL)).toEquiv).trans
      M.card_center_lineRadicalCoordinates

/-- The overlap index follows from its exact preimage under a surjective Levi map. -/
theorem overlap_index_of_leviMap
    (π : M.leftParabolic →* M.LocalUnitaryGroup) (hπ : Function.Surjective π)
    (hpre : M.localUnitaryLineStabilizer.comap π = M.overlap.subgroupOf M.leftParabolic)
    (hind : M.localUnitaryLineStabilizer.index = 65) :
    (M.overlap.subgroupOf M.leftParabolic).index = 65 := by
  rw [← hpre, M.localUnitaryLineStabilizer.index_comap_of_surjective hπ, hind]

/-- The full radical–SU₃ matrix subgroup is the actual solvable residual. -/
theorem leftLocal_eq_lineRadicalLeviSubgroup :
    M.leftLocal = M.lineRadicalLeviSubgroup :=
  M.leftLocal_eq_radicalLevi M.localUnitaryGroup_isPerfect

/-- The cubic character cuts out the actual solvable residual. -/
theorem leftLocal_eq_lineParabolicCharacter_ker :
    M.leftLocal = M.lineParabolicCharacter.ker :=
  M.leftLocal_eq_ker_lineParabolicCharacter M.localUnitaryGroup_isPerfect

/-- The full unipotent kernel is the canonical two-core of the residual. -/
theorem leftLocalLevi_ker_eq_pCore : M.leftLocalLevi.ker = pCore 2 M.leftLocal :=
  M.leftLeviKernel_eq_pCore M.leftLocalLevi
    (M.leftLocalLevi_surjective M.localUnitaryGroup_isPerfect)
    (M.leftLocalLeviKernelEquiv M.localUnitaryGroup_isPerfect)
    M.pCore_localUnitaryGroup

/-- The source quotient is the actual identity-form SU₃ matrix group over `M.F`. -/
noncomputable def leftLocalQuotientEquiv :
    (M.leftLocal ⧸ pCore 2 M.leftLocal) ≃* M.LocalUnitaryGroup :=
  M.leftLocalQuotientEquiv_of_leviMap M.leftLocalLevi
    (M.leftLocalLevi_surjective M.localUnitaryGroup_isPerfect)
    (M.leftLocalLeviKernelEquiv M.localUnitaryGroup_isPerfect)
    M.pCore_localUnitaryGroup

/-- The quotient identification is induced by the same matrix Levi projection. -/
@[simp] theorem leftLocalQuotientEquiv_mk (g : M.leftLocal) :
    M.leftLocalQuotientEquiv (QuotientGroup.mk g) = M.leftLocalLevi g := rfl

/-- Coordinates on the canonical core, using the faithful full unipotent matrices. -/
noncomputable def leftCoreEquivCoordinates :
    pCore 2 M.leftLocal ≃* M.LineRadicalCoordinates :=
  M.leftCoreEquivCoordinates_of_leviMap M.leftLocalLevi
    (M.leftLocalLevi_surjective M.localUnitaryGroup_isPerfect)
    (M.leftLocalLeviKernelEquiv M.localUnitaryGroup_isPerfect)
    M.pCore_localUnitaryGroup

/-- The core is the literal matrix unipotent subgroup restricted to the residual. -/
theorem pCore_leftLocal_eq_lineUnipotent :
    pCore 2 M.leftLocal = M.lineUnipotent.subgroupOf M.leftLocal :=
  M.leftLocalLevi_ker_eq_pCore.symm.trans
    (M.leftLocalLevi_ker M.localUnitaryGroup_isPerfect)

theorem lineUnipotent_le_leftLocal : M.lineUnipotent ≤ M.leftLocal := by
  rw [M.leftLocal_eq_lineRadicalLeviSubgroup]
  exact Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic.projectiveUnipotent_le_radicalLeviSubgroup
    M.form M.matrix

/-- Inclusion into the parabolic recovers the entire concrete unipotent subgroup. -/
theorem map_leftCore_subtype :
    (pCore 2 M.leftLocal).map M.leftLocal.subtype = M.lineUnipotent := by
  rw [M.pCore_leftLocal_eq_lineUnipotent, Subgroup.map_subgroupOf_eq_of_le
    M.lineUnipotent_le_leftLocal]

/-- The order in the source notation `4^(1+6)` is derived from the full coordinates. -/
theorem card_leftCore : Nat.card (pCore 2 M.leftLocal) = 4 ^ 7 :=
  (Nat.card_congr M.leftCoreEquivCoordinates.toEquiv).trans M.card_lineRadicalCoordinates

theorem card_center_leftCore : Nat.card (Subgroup.center (pCore 2 M.leftLocal)) = 4 :=
  (Nat.card_congr (Subgroup.centerCongr M.leftCoreEquivCoordinates).toEquiv).trans
    M.card_center_lineRadicalCoordinates

/-- The commutator subgroup of the canonical core is exactly its center. -/
theorem commutator_leftCore :
    commutator (pCore 2 M.leftLocal) = Subgroup.center (pCore 2 M.leftLocal) := by
  let e := M.leftCoreEquivCoordinates
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective,
    ← commutator_def, Subgroup.center_map_equiv e]
  exact M.commutator_lineRadicalCoordinates

/-- The Frattini subgroup of the canonical core is exactly its center. -/
theorem frattini_leftCore :
    frattini (pCore 2 M.leftLocal) = Subgroup.center (pCore 2 M.leftLocal) := by
  let e := M.leftCoreEquivCoordinates
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.frattini_map_equiv e, Subgroup.center_map_equiv e]
  exact M.frattini_lineRadicalCoordinates

/-- The actual solvable residual has index three in the full line parabolic. -/
theorem leftLocal_index_eq_three : M.leftLocal.index = 3 :=
  M.leftLocal_index M.localUnitaryGroup_isPerfect

/-- The original whole flag overlap has index 65 in the full line parabolic. -/
theorem overlap_index_eq_sixtyFive :
    (M.overlap.subgroupOf M.leftParabolic).index = 65 :=
  M.overlap_index_of_leviMap M.lineParabolicProjection
    M.lineParabolicProjection_surjective M.lineParabolicProjection_flag_preimage
    M.localUnitaryLineStabilizer_index

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
