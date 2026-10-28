module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Suzuki.Fixed

/-!
# Marked coordinates in the fixed Suzuki component branch

When the chosen Sylow normalizes a relative Suzuki component, its orbit is the
component itself.  A quotient marking whose Sylow image is the standard root
subgroup therefore gives the literal `OrbitCoordinates` required by the
coefficient-quotient argument.  The quotient map is the original
`I → I/O₂(I)` map followed by that marking; no replacement quotient or ambient
normality is introduced.

Source: Aschbacher--Smith 11.5.6(3), printed pp.780--781.
-/

@[expose] public noncomputable section
open Subgroup
open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.Suzuki

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
variable {L V : Subgroup G} {D : ChosenModule T L V} {E : Geometry D}

/-- The marked quotient map in a fixed component gives the orbit coordinates.
The `hroot` premise is the exact Sylow marking used by the standard Suzuki
Borel; it is discharged by the component-model producer. -/
def orbitCoordinates_of_fixed
    {I : Subgroup G} (hTI : (T : Subgroup G) ≤ normalizer (I : Set G))
    {m : ℕ} (_hm : 0 < m)
    (e : (I ⧸ pCore 2 I) ≃* SuzukiMatrixGroup m)
    (hroot : ((T : Subgroup G).subgroupOf I).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))) =
      SuzukiRootSubgroup m) :
    OrbitCoordinates T I m := by
  have horbit : orbit T I = I := le_antisymm
    (conjugateSpanBy_le le_rfl hTI) (le_conjugateSpanBy I (T : Subgroup G))
  let j : orbit T I →* I := inclusion horbit.le
  let q : orbit T I →* SuzukiMatrixGroup m :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 I)).comp j)
  refine ⟨e, q, ?_, ?_⟩
  · intro i
    change e ((QuotientGroup.mk' (pCore 2 I)) (j (inclusion _ i))) = _
    rfl
  · have hj : ((T : Subgroup G).subgroupOf (orbit T I)).map j =
        (T : Subgroup G).subgroupOf I := by
      ext i
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ha
      · intro hi
        exact ⟨⟨i, horbit.symm ▸ i.property⟩, hi, rfl⟩
    change _ = _
    simpa only [q, MonoidHom.comp_assoc, ← map_map, hj] using hroot

/-- Any quotient marking can be adjusted by an inner automorphism to mark the
standard Suzuki root subgroup.  This is the usual Sylow conjugacy transport,
with the original quotient left unchanged. -/
theorem exists_orbitCoordinates_of_fixed
    {I : Subgroup G} (hTI : (T : Subgroup G) ≤ normalizer (I : Set G))
    {m : ℕ} (hm : 0 < m)
    (e : (I ⧸ pCore 2 I) ≃* SuzukiMatrixGroup m) :
    ∃ e' : (I ⧸ pCore 2 I) ≃* SuzukiMatrixGroup m,
      ∃ c : OrbitCoordinates T I m, c.component = e' := by
  obtain ⟨P, hP⟩ := NormalSylowQuotientAction.intersection_sylow T I hTI
  obtain ⟨U, hU⟩ := suzukiRootSubgroup_isSylow m hm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  let Q := P.mapSurjective (f := q)
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
    (SuzukiMatrixGroup m) Q U
  let e' := e.trans (MulAut.conj g)
  have he : (P : Subgroup I).map (e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))) =
      SuzukiRootSubgroup m := by
    have hh := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul, hU] at hh
    change ((P : Subgroup I).map q).map
      (MulAut.conj g).toMonoidHom =
      (SuzukiRootSubgroup m : Subgroup (SuzukiMatrixGroup m)) at hh
    have he' : e'.toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by
      ext x
      rfl
    rw [he', MonoidHom.comp_assoc, ← map_map]
    simpa only [hP] using hh
  refine ⟨e', orbitCoordinates_of_fixed hTI hm e' ?_, rfl⟩
  simpa only [hP] using he

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.Suzuki
