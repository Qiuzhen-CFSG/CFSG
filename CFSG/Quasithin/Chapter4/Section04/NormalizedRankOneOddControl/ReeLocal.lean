module
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.ParabolicSections
public import Theory.GroupTheory.SimpleSectionOrder
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Coverage
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.CoreActionRigidity.Structure

/-!
# The actual Ree parabolic containing a rank-one residual

Normalizer coverage places the residual in a full parabolic. The linear
projection has solvable kernel even with its complementary field torus;
the nonidentity two-square in the simple quotient excludes that parabolic.
The remaining Suzuki parabolic has three-free order. Every binary PSU₃
has order divisible by three, so the unitary residual cannot occur there.
The Suzuki family retains its actual conjugated residual map into the
Suzuki parabolic for the subsequent centered-module argument.
Source: Aschbacher--Smith 4.4.12, pp.621--622, and F.1.12(5), pp.263--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl

theorem unitary_three_dvd_card {S : Type*} [Group S]
    {s : ℕ} (_hs : 2 ≤ s) (hu : ClassicalGroup.IsPSU S 3 (2 ^ s)) :
    3 ∣ Nat.card S := by
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hu
  rw [Nat.card_congr e.toEquiv,
    HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.card_projective
      J hcard hconj]
  let q := 2 ^ s
  have hq : 1 ≤ q := Nat.one_le_pow _ _ (by decide)
  have hnd : ¬ 3 ∣ q := fun h => (by decide : ¬ 3 ∣ 2)
    (Nat.prime_three.dvd_of_dvd_pow h)
  have hm : q % 3 = 1 ∨ q % 3 = 2 := by
    have := Nat.mod_lt q (by decide : 0 < 3)
    have := mt Nat.dvd_of_mod_eq_zero hnd
    omega
  have hd : 3 ∣ q ^ 2 - 1 := by
    have ht : q ^ 2 % 3 = 1 := by
      rcases hm with h | h <;> simp [Nat.pow_mod,h]
    have hpos : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    apply Nat.dvd_of_mod_eq_zero
    omega
  change 3 ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1)
  rcases hm with h | h
  · have hg : Nat.gcd 3 (q + 1) = 1 := by
      apply Nat.Coprime.gcd_eq_one
      apply Nat.prime_three.coprime_iff_not_dvd.mpr
      omega
    rw [hg,Nat.div_one]
    exact dvd_mul_of_dvd_right hd _
  · have ha : 3 ∣ q + 1 := by omega
    have hb : 3 ∣ q ^ 3 + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      simp [Nat.add_mod,Nat.pow_mod,h]
    rw [Nat.gcd_eq_left ha]
    apply (Nat.dvd_div_iff_mul_dvd (dvd_mul_of_dvd_right hd _)).mpr
    exact Nat.mul_dvd_mul (dvd_mul_of_dvd_left hb _) hd

theorem no_ree_linear_parabolic
    {A S : Type*} [Group A] [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : A →* S) (hπ : Function.Surjective π)
    {m : ℕ} (hm : 1 ≤ m)
    (r : A →* ReeF4.ConverseParabolics.parabolic m .linear)
    [Group.IsSolvable r.ker] : False := by
  let q := ReeF4.ConverseParabolics.linearProjection hm
  let := (ReeF4.ConverseParabolics.linearProjection_ker_isPGroup hm).isNilpotent
  let f := (MonoidHom.fst _ _).comp q
  let : Group.IsSolvable (MonoidHom.fst
      (SL(2,ReeF4.CoefficientField m)) (ReeF4.CoefficientField m)ˣ).ker :=
    Group.isSolvable_of_isSolvable_injective
      (f := (MonoidHom.snd _ _).comp (MonoidHom.fst
        (SL(2,ReeF4.CoefficientField m)) (ReeF4.CoefficientField m)ˣ).ker.subtype) (by
        intro x y h
        apply Subtype.ext
        exact Prod.ext (x.property.trans y.property.symm) h)
  let : Group.IsSolvable f.ker := by
    change Group.IsSolvable ((MonoidHom.fst _ _).comp q).ker
    rw [← MonoidHom.comap_ker]
    exact isSolvable_comap_of_solvable_ker q _
  let : Group.IsSolvable (f.comp r).ker := by
    rw [← MonoidHom.comap_ker]
    exact isSolvable_comap_of_solvable_ker r _
  exact no_rankOne_quotient_in_binary_linear_two hS hexp π hπ (f.comp r)

theorem ree_suzuki_parabolic_representation
    {A S : Type*} [Group A] [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : A →* S) (hπ : Function.Surjective π)
    {m : ℕ} (hm : 1 ≤ m) (P : Subgroup (ReeF4.Model m))
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (r : A →* ReeF4.Model m) [Group.IsSolvable r.ker]
    (hr : r.range ≤ normalizer (P : Set _)) :
    ∃ g : ReeF4.Model m,
      r.range.map (MulAut.conj g).toMonoidHom ≤ ReeF4.ConverseParabolics.parabolic m .suzuki := by
  obtain ⟨g,b,hg⟩ := ReeF4.ConverseParabolics.normalizer_cover hm P hne hp
  have hh := (map_mono hr).trans hg
  cases b with
  | suzuki => exact ⟨g,hh⟩
  | linear =>
    let j := (MulAut.conj g).toMonoidHom.comp r
    have hj : j.range ≤ ReeF4.ConverseParabolics.parabolic m .linear := by
      rwa [MonoidHom.range_comp]
    let k := j.codRestrict _ (fun x => hj ⟨x,rfl⟩)
    let : Group.IsSolvable k.ker := Group.isSolvable_of_isSolvable_injective
      (f := inclusion (show k.ker ≤ r.ker from fun x hx => by
        have he : j x = 1 := congrArg Subtype.val hx
        exact (MulAut.conj g).injective (he.trans (map_one _).symm)))
      (inclusion_injective _)
    exact (no_ree_linear_parabolic hS hexp π hπ hm k).elim

theorem no_ree_local_of_three_dvd
    {A S : Type*} [Group A] [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (hthree : 3 ∣ Nat.card S) (π : A →* S) (hπ : Function.Surjective π)
    {m : ℕ} (hm : 1 ≤ m) (P : Subgroup (ReeF4.Model m))
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (r : A →* ReeF4.Model m) [Group.IsSolvable r.ker]
    (hr : r.range ≤ normalizer (P : Set _)) : False := by
  obtain ⟨g,hg⟩ := ree_suzuki_parabolic_representation hS hexp π hπ hm P hp hne r hr
  let j := (MulAut.conj g).toMonoidHom.comp r
  have hj : j.range ≤ ReeF4.ConverseParabolics.parabolic m .suzuki := by
    rwa [MonoidHom.range_comp]
  let k := j.codRestrict _ (fun x => hj ⟨x,rfl⟩)
  let : Group.IsSolvable k.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show k.ker ≤ r.ker from fun x hx => by
      have he : j x = 1 := congrArg Subtype.val hx
      exact (MulAut.conj g).injective (he.trans (map_one _).symm)))
    (inclusion_injective _)
  exact ReeF4.ConverseParabolics.suzuki_parabolic_three_free hm
    (hthree.trans (SimpleSection.card_dvd_of_solvable_representation hS π hπ k))


end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
