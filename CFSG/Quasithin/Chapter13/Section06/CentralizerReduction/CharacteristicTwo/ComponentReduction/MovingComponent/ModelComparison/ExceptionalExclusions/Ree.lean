module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.ModelComparison.Inputs
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.SuzukiCoordinates
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.Actions
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.ThreeDivisibility.Exceptional
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.GroupTheory.DihedralUniqueInvolutionProduct
public import GorensteinWalter.PSL2DihedralSylow
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Excluding Ree F₄ from the nonnormal component list

The actual type V fixed-root block has order q² and contains an element
whose square is nonidentity. Binary PSL₂ has Sylow two-subgroups of exponent
two, so this excludes its carrier. The same block has order divisible by
sixteen for m ≥ 1, excluding J₁. Three-divisibility excludes Suzuki.
The type VI elementary root subgroup has order q ≥ 8, whereas elementary
subgroups of the dihedral Sylow two-subgroups of odd PSL₂ have order at most
four. This last argument adapts the intrinsic Chapter 15 `LieParameter.Ree`
proof without its unused p ≥ 5 restriction, so it also covers p = 3.

Every root coordinate theorem is instantiated with the actual supplied
`LocalBlockInput`; no Ree order formula or simplicity assertion is needed.
This supplies the Ree field of `ExceptionalExclusions`.

Sources: GLS3 §2.4 and Table 2.4, types V and VI; Aschbacher–Smith,
1.1.5(3a), pp.501–503, and 1.2.1(3), p.504, compared in 13.6.6, p.927.
-/

public section
open Matrix Subgroup
open scoped MatrixGroups
open ReeF4.LocalBlockInput.PairRigidity
open ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent.ModelComparison

private theorem square_of_twoGroup_embedding {A F : Type*} [Group A] [Field F]
    [Finite F] [CharP F 2] (hA : IsPGroup 2 A)
    (f : A →* SL(2, F)) (hf : Function.Injective f) (a : A) : a^2=1 := by
  obtain ⟨S, hS⟩ := (hA.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  let g : A →* S := f.codRestrict (S : Subgroup _) (fun a => hS ⟨a, rfl⟩)
  let e := Sylow.equiv S (SpecialLinearGroup.upperUnipotentSylow F 2)
  let u := MonoidHom.ofInjective (SpecialLinearGroup.upperUnipotentHom_injective F)
  let j : A →* Multiplicative F := u.symm.toMonoidHom.comp (e.toMonoidHom.comp g)
  have hj : Function.Injective j := by
    intro a b h
    exact hf (congrArg Subtype.val (e.injective (u.symm.injective h)))
  apply hj
  rw [map_pow, map_one]
  change 2 • (j a).toAdd = 0
  simp [nsmul_eq_mul, CharTwo.two_eq_zero]

private theorem suzuki_block_card {m : ℕ} (d : ReeF4.LocalBlockInput m) :
    Nat.card (simpleBlock d .suzuki true) = 2 ^ ((2*m+1)*2) := by
  rw [← Nat.card_congr ((suzukiCoordinates d).blockEquiv true), Nat.card_prod,
    ReeF4.field_card, ← pow_two, ← pow_mul]

private theorem ree_not_binary {Q : Type*} [Group Q] {n m : ℕ}
    (hpsl : ClassicalGroup.IsPSL Q 2 (2^n))
    (hree : Chapter1.Section02.LocalModels.IsReeF4At Q m) : False := by
  obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨d, ⟨e⟩⟩ := hree
  let C := suzukiCoordinates d
  let A := simpleBlock d .suzuki true
  have hA : IsPGroup 2 A := IsPGroup.of_card (suzuki_block_card d)
  let g : A →* SL(2,F) := (Theory.PSL2.sl2QuotientEquiv F).symm.toMonoidHom.comp
    ((e.symm.trans eF).toMonoidHom.comp A.subtype)
  have hg : Function.Injective g := (Theory.PSL2.sl2QuotientEquiv F).symm.injective.comp
    ((e.symm.trans eF).injective.comp (Subgroup.subtype_injective A))
  let a : A := ⟨C.element true 1 0, C.element_mem true 1 0⟩
  have ha := square_of_twoGroup_embedding hA g hg a
  have hs : C.element true 1 0 ^ 2 = 1 := congrArg Subtype.val ha
  exact one_ne_zero ((C.element_square_eq_one_iff true 1 0).mp hs)

private theorem ree_not_janko {Q : Type*} [Group Q] {m : ℕ} (hm : 1 ≤ m)
    (hree : Chapter1.Section02.LocalModels.IsReeF4At Q m)
    (hj : Nonempty (Q ≃* Janko1.Model)) : False := by
  obtain ⟨d, ⟨e⟩⟩ := hree
  obtain ⟨eJ⟩ := hj
  have hd := (simpleBlock d .suzuki true).card_subgroup_dvd_card
  rw [suzuki_block_card, Nat.card_congr (e.symm.trans eJ).toEquiv, Janko1.card_model] at hd
  have h16 : 2^4 ∣ 2^((2*m+1)*2) := Nat.pow_dvd_pow 2 (by omega)
  have hh := h16.trans hd
  norm_num at hh

private theorem ree_not_odd {Q : Type*} [Group Q] {p m : ℕ}
    (hp : p.Prime) (ho : Odd p)
    (hodd : ClassicalGroup.IsPSL Q 2 p) (hm : 1 ≤ m)
    (hree : Chapter1.Section02.LocalModels.IsReeF4At Q m) : False := by
  obtain ⟨F, _, _, hF, ⟨eodd⟩⟩ := hodd
  obtain ⟨d, ⟨eree⟩⟩ := hree
  let eModel := eree.symm.trans eodd
  let A := Multiplicative (ReeF4.CoefficientField m)
  let eA := positiveLinearEquiv d
  let f : A →* GorensteinWalter.PSL2 F :=
    eModel.toMonoidHom.comp ((simpleBlock d .linear true).subtype.comp eA.toMonoidHom)
  have hf : Function.Injective f := eModel.injective.comp
    ((Subgroup.subtype_injective _).comp eA.injective)
  have hA (a : A) : a ^ 2 = 1 := by
    change 2 • a.toAdd = 0
    simp [nsmul_eq_mul, CharTwo.two_eq_zero]
  have hpA : IsPGroup 2 A := fun a => ⟨1, by simpa using hA a⟩
  obtain ⟨S, hS⟩ :=
    (hpA.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  have hd := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F
    ⟨p, 1, hp, ho, by omega, by simpa using hF⟩
  obtain ⟨n, _hn, ⟨eS⟩⟩ := hd S
  let g : A →* S := f.codRestrict (S : Subgroup _) (fun a => hS ⟨a, rfl⟩)
  let k : A →* DihedralGroup (2 ^ n) := eS.toMonoidHom.comp g
  have hk : Function.Injective k := by
    intro a b h
    exact hf (congrArg Subtype.val (eS.injective h))
  have hc : Nat.card A ≤ 4 := calc
    Nat.card A = Nat.card k.range := Nat.card_congr (MonoidHom.ofInjective hk).toEquiv
    _ ≤ 4 := DihedralGroup.card_le_four_of_square_eq_one k.range (by
      intro x
      obtain ⟨a, ha⟩ := x.property
      apply Subtype.ext
      change x.val ^ 2 = 1
      rw [← ha, ← map_pow, hA a, map_one])
  have hl : 8 ≤ Nat.card A := by
    change 8 ≤ Nat.card (ReeF4.CoefficientField m)
    rw [ReeF4.field_card]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 3 ≤ 2 * m + 1)
  omega

open Chapter1.Section02
/-- Every supplied genuine Ree fixed group with m ≥ 1 avoids the nonnormal list. -/
theorem ree_not_nonnormal {Q : Type*} [Group Q] {m : ℕ} (hm : 1 ≤ m)
    (hree : LocalModels.IsReeF4At Q m) : ¬ NonnormalCComponentModel Q := by
  intro h
  cases h with
  | linear_even n hn iso => exact ree_not_binary iso hree
  | suzuki n hn iso =>
    obtain ⟨d, ⟨e⟩⟩ := hree
    obtain ⟨eS⟩ := iso
    have hd := d.three_dvd_card
    rw [Nat.card_congr (e.symm.trans eS).toEquiv] at hd
    exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free n hn hd
  | linear_prime p hp ho iso => exact ree_not_odd hp ho iso hm hree
  | janko iso => exact ree_not_janko hm hree iso

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent.ModelComparison
