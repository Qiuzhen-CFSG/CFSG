module
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.Models
public import Theory.GroupTheory.SimpleSectionOrder
public import Theory.SpecificGroups.ClassicalUnitary.FivePerfectLocals

/-!
# No Suzuki residual in the actual PSU₅(4) parabolics

The literal residual representation normalizes a nonidentity two-subgroup.
Isotropic geometry puts its image in a conjugate full line or plane
parabolic. A solvable representation kernel preserves the nonsolvable
simple quotient as a section. The exact parabolic orders bound the Suzuki
parameter by two, and both remaining orders fail divisibility.
Source: Aschbacher--Smith 4.4.12, pp.621--622, and F.1.12(7), pp.263--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl

theorem suzuki_card_not_dvd_unitary_five_parabolic {m : ℕ} (hm : 1 ≤ m)
    (plane : Bool) : ¬ Nat.card (SuzukiMatrixGroup m) ∣
      2 ^ 20 * (if plane then 3 ^ 2 * 5 * 17 else 3 ^ 2 * 5 ^ 2 * 13) := by
  rw [suzukiMatrixGroup_card m (by omega)]
  intro hd
  have hle := Nat.le_of_dvd (by cases plane <;> norm_num :
    0 < 2 ^ 20 * (if plane then 3 ^ 2 * 5 * 17 else 3 ^ 2 * 5 ^ 2 * 13)) hd
  have hm2 : m ≤ 2 := by
    by_contra hn
    have hq : 128 ≤ 2 ^ (2 * m + 1) :=
      Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 7 ≤ 2 * m + 1)
    have hb := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.add_le_add_right (Nat.pow_le_pow_left hq 2) 1)
        (Nat.pow_le_pow_left hq 2)) (Nat.sub_le_sub_right hq 1)
    cases plane <;> norm_num at hb hle <;> omega
  interval_cases m <;> cases plane <;> norm_num at hd

theorem no_suzuki_unitary_five_local
    {A S : Type*} [Group A] [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S) (π : A →* S) (hπ : Function.Surjective π)
    {m : ℕ} (hm : 1 ≤ m) (e : S ≃* SuzukiMatrixGroup m)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (J : HermitianForm 5 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (r : A →* ProjectiveSpecialUnitaryMatrixGroup J) [Group.IsSolvable r.ker]
    (hr : r.range ≤ normalizer (P : Set _)) : False := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Theory.SpecificGroups.UnitaryFive.finite_projective J
  obtain ⟨W,hn,hi,_,hNW⟩ :=
    Theory.SpecificGroups.UnitaryFive.IsotropicGeometry.projective_twoLocal_stabilizes_isotropic
      J hJ (normalizer (P : Set _)) ⟨P,hne,hp,rfl⟩
  obtain ⟨b,g,hg⟩ := Theory.SpecificGroups.UnitaryFive.IsotropicTransitivity.transitive
    J hcard hconj hJ W hn hi
  have he : Theory.SpecificGroups.UnitaryFive.parabolic J W =
      (if b then Theory.SpecificGroups.UnitaryFive.planeParabolic J
        else Theory.SpecificGroups.UnitaryFive.lineParabolic J).map
          (MulAut.conj (Theory.SpecificGroups.UnitaryFive.project J g)).toMonoidHom := by
    rw [hg, Theory.SpecificGroups.UnitaryFive.IsotropicGeometry.parabolic_map_action]
    cases b <;> rfl
  rw [he] at hNW
  let j := (MulAut.conj (Theory.SpecificGroups.UnitaryFive.project J g)⁻¹).toMonoidHom.comp r
  have hj : j.range ≤ (if b then Theory.SpecificGroups.UnitaryFive.planeParabolic J
      else Theory.SpecificGroups.UnitaryFive.lineParabolic J) := by
    rintro _ ⟨x,rfl⟩
    obtain ⟨y,hy,he⟩ := hNW (hr ⟨x,rfl⟩)
    change (Theory.SpecificGroups.UnitaryFive.project J g)⁻¹ * r x *
      ((Theory.SpecificGroups.UnitaryFive.project J g)⁻¹)⁻¹ ∈ _
    rw [← he]
    simpa [MulAut.conj_apply,mul_assoc] using hy
  let k := j.codRestrict _ (fun x => hj ⟨x,rfl⟩)
  let : Group.IsSolvable k.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show k.ker ≤ r.ker from fun x hx => by
      have he : j x = 1 := congrArg Subtype.val hx
      exact (MulAut.conj (Theory.SpecificGroups.UnitaryFive.project J g)⁻¹).injective
        (he.trans (map_one _).symm))) (inclusion_injective _)
  have hd := SimpleSection.card_dvd_of_solvable_representation hS π hπ k
  rw [Nat.card_congr e.toEquiv] at hd
  apply suzuki_card_not_dvd_unitary_five_parabolic hm b
  cases b
  · simpa only [Bool.false_eq_true, ↓reduceIte,
      Theory.SpecificGroups.UnitaryFive.card_lineParabolic_four J hcard hconj hJ] using hd
  · simpa only [↓reduceIte,
      Theory.SpecificGroups.UnitaryFive.card_planeParabolic_four J hcard hconj hJ] using hd

end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
