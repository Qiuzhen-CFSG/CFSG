module
public import Theory.SpecificGroups.LieType.F4LongParabolic.Characteristic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.MSInputs

/-!
# The original F4 parabolic satisfies the MS3 input clause

Transport the proved characteristic-subgroup theorem through the literal
inclusion of the positive subgroup into its long-A2 parabolic. This gives
exactly `MSCharacteristicCondition` used in `BinaryMS.Input`.

This checks one hypothesis of the original-action candidate investigated by
qt-rank-two-ms93. The quotient, generalized-Fitting, SQTK, odd-index radical,
and component clauses still require proofs. No full MS input, counterexample
to C.1.34, or original fixed-factor centrality is asserted here. The existing
fixed-factor producer and final linearThree assembly remain separate.

Source: Aschbacher--Smith C.1.31 (MS3), printed p.135; the F4 examples in
Meierfrankenfeld--Stellmacher (1993), printed p.831.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.F4OriginalCandidate
open Subgroup ReeF4 ReeF4.LargeLocalSeeds
open Theory.SpecificGroups.LieType.F4LongParabolic

private theorem characteristic_map_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (C : Subgroup G) [C.Characteristic] :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  rintro a x ⟨y, hy, rfl⟩
  refine ⟨(MulAut.congr e.symm a) y,
    characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy, ?_⟩
  exact e.apply_symm_apply _

/-- The literal MS3 field for the original positive subgroup in its long-A2 parabolic. -/
theorem positiveInParabolic_msCharacteristic (m : ℕ) :
    CFSG.Quasithin.ChapterC.MSCharacteristicCondition (positiveInParabolic m) := by
  intro C hc hne hn
  let := hc
  let S := splitUnipotent m
  let P := longParabolic m
  let R := positiveInParabolic m
  let e : R ≃* S := subgroupOfEquivOfLe (show S ≤ P from le_sup_left)
  let D := C.map e.toMonoidHom
  let : D.Characteristic := characteristic_map_equiv e C
  have hle : D.map S.subtype ≤ P := (map_subtype_le D).trans le_sup_left
  have he : (D.map S.subtype).subgroupOf P = C.map R.subtype := by
    apply map_injective P.subtype_injective
    rw [map_subgroupOf_eq_of_le hle]
    change (C.map e.toMonoidHom).map S.subtype = (C.map R.subtype).map P.subtype
    rw [map_map, map_map]
    rfl
  have hD : D = ⊥ := characteristic_normal_eq_bot m D (he.symm ▸ hn)
  exact hne ((map_eq_bot_iff_of_injective C e.injective).mp hD)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.F4OriginalCandidate
