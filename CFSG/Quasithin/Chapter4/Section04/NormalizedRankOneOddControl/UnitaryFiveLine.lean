module
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.UnitaryFiveLocal
/-!
# The remaining unitary parabolic is the PSU₃(4) line row

Exact full-parabolic orders bound the exponent of the binary unitary
quotient by four. Checking the three remaining parameters leaves s = 2
and excludes the plane parabolic. The geometric application retains the
original representation followed by actual inner conjugation.
Source: Aschbacher--Smith 4.4.12 and F.1.12(7), pp.621--622,263--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl

theorem unitary_parameter_and_side_of_parabolic_order
    {S : Type*} [Group S] {s : ℕ} (hs : 2 ≤ s)
    (hu : ClassicalGroup.IsPSU S 3 (2 ^ s)) (plane : Bool)
    (hd : Nat.card S ∣ 2 ^ 20 *
      (if plane then 3 ^ 2 * 5 * 17 else 3 ^ 2 * 5 ^ 2 * 13)) :
    s = 2 ∧ plane = false := by
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hu
  rw [Nat.card_congr e.toEquiv,
    HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.card_projective
      J hcard hconj] at hd
  have hle := Nat.le_of_dvd (by cases plane <;> norm_num :
    0 < 2 ^ 20 * (if plane then 3 ^ 2 * 5 * 17 else 3 ^ 2 * 5 ^ 2 * 13)) hd
  have hs4 : s ≤ 4 := by
    by_contra hn
    have hq : 32 ≤ 2 ^ s := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 5 ≤ s)
    have hnum := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.add_le_add_right (Nat.pow_le_pow_left hq 3) 1)
        (Nat.pow_le_pow_left hq 3)) (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    have hden : Nat.gcd 3 (2 ^ s + 1) ≤ 3 := Nat.gcd_le_left _ (by decide)
    have hb := (Nat.div_le_div_right hnum (c := 3)).trans
      (Nat.div_le_div_left hden (Nat.gcd_pos_of_pos_left _ (by decide)))
    cases plane <;> norm_num at hb hle <;> omega
  interval_cases s <;> cases plane <;> norm_num at *

theorem unitary_five_line_representation
    {A S : Type*} [Group A] [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S) (π : A →* S) (hπ : Function.Surjective π)
    {s : ℕ} (hs : 2 ≤ s) (hu : ClassicalGroup.IsPSU S 3 (2 ^ s))
    {F : Type*} [Field F] [Finite F] [CharP F 2] (J : HermitianForm 5 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (r : A →* ProjectiveSpecialUnitaryMatrixGroup J) [Group.IsSolvable r.ker]
    (hr : r.range ≤ normalizer (P : Set _)) :
    s = 2 ∧ ∃ g : ProjectiveSpecialUnitaryMatrixGroup J,
      r.range.map (MulAut.conj g).toMonoidHom ≤ Theory.SpecificGroups.UnitaryFive.lineParabolic J := by
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
  have hc : s = 2 ∧ b = false := by
    apply unitary_parameter_and_side_of_parabolic_order hs hu b
    cases b
    · simpa only [Bool.false_eq_true, ↓reduceIte,
        Theory.SpecificGroups.UnitaryFive.card_lineParabolic_four J hcard hconj hJ] using hd
    · simpa only [↓reduceIte,
        Theory.SpecificGroups.UnitaryFive.card_planeParabolic_four J hcard hconj hJ] using hd
  refine ⟨hc.1,(Theory.SpecificGroups.UnitaryFive.project J g)⁻¹,?_⟩
  rw [hc.2] at hj
  simpa only [j,MonoidHom.range_comp,Bool.false_eq_true,↓reduceIte] using hj

end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
