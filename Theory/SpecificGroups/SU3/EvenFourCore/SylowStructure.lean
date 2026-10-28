module

public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.RootGeneration
public import Theory.ElementaryAbelian.Basic

/-!
# The central quotient of the PSU₃(4) root group

Huppert's matrix coordinates identify his root subgroup with the literal range
of `hermitianUnipotentPSU`. Thus this range has order 64, and its derived
subgroup is its center of order four. In characteristic two, root squares
have zero first coordinate and hence are central. The central quotient is
therefore elementary abelian of order sixteen.

Source: Huppert II.10.12, with the square formula in `EvenInnerCentralizers`.
This is the intrinsic Sylow calculation used in the PSU₃(4) exclusion in
Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.40, printed p.1138.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open scoped Matrix

namespace SU3.EvenFourCore
variable {F : Type*} [Field F] [Finite F]

private theorem root_profile (J : HermitianForm 3 F) (q : ℕ)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    let R := (hermitianUnipotentPSU J hJ).range
    Nat.card R = q ^ 3 ∧ _root_.commutator R = center R ∧ Nat.card (center R) = q := by
  obtain ⟨_, _, _, _, _, _,
    ⟨R, _, _, _, _, _, _, _, hRcard, hcomm, hcenter, _, _, ⟨e, he⟩, _⟩, _⟩ :=
    huppert_II_10_12 J q hcard hfixed hJ
  have heq (z : hermitianUnipotentCoord J) :
      (e z : ProjectiveSpecialUnitaryMatrixGroup J) = hermitianUnipotentPSU J hJ z := by
    obtain ⟨M, hM, hp⟩ := he z
    apply Subtype.ext
    rw [hp, hermitianUnipotentPSU_val]
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact congrFun (congrFun hM i) j
  have hR : R = (hermitianUnipotentPSU J hJ).range := by
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz⟩ := e.surjective ⟨x, hx⟩
      exact ⟨z, (heq z).symm.trans (congrArg Subtype.val hz)⟩
    · rintro ⟨z, rfl⟩
      rw [← heq]
      exact (e z).property
  rw [← hR]
  exact ⟨hRcard, hcomm, hcomm ▸ hcenter⟩

omit [Finite F] in
private theorem coord_square_central [CharP F 2] (J : HermitianForm 3 F)
    (z : hermitianUnipotentCoord J) : z ^ 2 ∈ center (hermitianUnipotentCoord J) := by
  have hz : (z ^ 2).val.1 = 0 := congrArg Prod.fst (HermitianForm.EvenInner.square_coordinates J z)
  apply mem_center_iff.mpr
  intro w
  apply Subtype.ext
  apply Prod.ext
  · change w.val.1 + (z ^ 2).val.1 = (z ^ 2).val.1 + w.val.1
    exact add_comm _ _
  · change w.val.2 + (z ^ 2).val.2 - w.val.1 * J.conj (z ^ 2).val.1 =
      (z ^ 2).val.2 + w.val.2 - (z ^ 2).val.1 * J.conj w.val.1
    simp [hz, add_comm]

/-- The actual PSU₃(4) root group has elementary central quotient of order sixteen
and derived subgroup equal to its center. -/
theorem four_root_structure [CharP F 2] (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card F = 16)
    (hfixed : Nat.card {x : F // J.conj x = x} = 4) :
    let R := (hermitianUnipotentPSU J hJ).range
    IsElementaryAbelian 2 (R ⧸ center R) ∧
      Nat.card (R ⧸ center R) = 16 ∧ _root_.commutator R = center R := by
  let R := (hermitianUnipotentPSU J hJ).range
  obtain ⟨hR, hcomm, hZ⟩ := root_profile J 4 hJ hcard hfixed
  have hsquare (x : R) : x ^ 2 ∈ center R := by
    let f := (hermitianUnipotentPSU J hJ).rangeRestrict
    obtain ⟨z, rfl⟩ := (hermitianUnipotentPSU J hJ).rangeRestrict_surjective x
    rw [← map_pow]
    apply mem_center_iff.mpr
    intro y
    obtain ⟨w, rfl⟩ := (hermitianUnipotentPSU J hJ).rangeRestrict_surjective y
    simpa only [map_mul] using congrArg f (mem_center_iff.mp (coord_square_central J z) w)
  refine ⟨?_, ?_, hcomm⟩
  · refine {
      toIsMulCommutative :=
        Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm.le
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center R) x
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hsquare y)
  · have h := (center R).card_mul_index
    rw [Subgroup.index_eq_card, hZ, hR] at h
    change 4 * Nat.card (R ⧸ center R) = 64 at h
    change Nat.card (R ⧸ center R) = 16
    omega

end SU3.EvenFourCore
