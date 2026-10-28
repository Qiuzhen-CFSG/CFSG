module

public import Theory.GroupTheory.SemidihedralAut
public import Theory.GroupTheory.SemidihedralStandardModel
public import Theory.GroupTheory.SpecificGroups.DihedralAut

/-!
# Automorphism squares on dihedral and semidihedral rotations

Both standard two-group models have a characteristic cyclic rotation subgroup
whose order is divisible by four. Inside any such subgroup, the kernel of the
fourth-power homomorphism is characteristic and cyclic of order four. Its
automorphism group has order two, so every automorphism square fixes its
order-four generators.

This is the intrinsic rotation calculation used by Aschbacher–Smith,
16.3.9 and 16.3.11, printed pp.1180–1181. It uses the actual dihedral and
semidihedral models, without a square-obstruction assumption.
-/

public section
open Subgroup

/-- The fourth-power kernel in a characteristic cyclic subgroup supplies an
order-four element fixed by the square of any automorphism. -/
theorem Subgroup.exists_order_four_fixed_by_automorphism_square {S : Type*} [Group S] [Finite S] (R : Subgroup S)
    [R.Characteristic] [IsCyclic R] (hR : 4 ∣ Nat.card R) (α : MulAut S) :
    ∃ x : S, orderOf x = 4 ∧ α (α x) = x := by
  let := IsCyclic.commGroup (α := R)
  let C : Subgroup R := (powMonoidHom 4 : R →* R).ker
  have hC : Nat.card C = 4 := by
    rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right hR]
  let : C.Characteristic := characteristic_iff_le_comap.mpr (by
    intro β x hx
    change (β x) ^ 4 = 1
    change x ^ 4 = 1 at hx
    rw [← map_pow, hx, map_one])
  let β := MulAut.characteristic C (MulAut.characteristic R α)
  have hAut : Nat.card (MulAut C) = 2 := by
    rw [IsCyclic.card_mulAut, hC]
    decide
  have hsq : β ^ 2 = 1 := by simpa only [hAut] using (pow_card_eq_one' (x := β))
  obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := C)
  refine ⟨x, ?_, ?_⟩
  · exact (orderOf_coe x.val).trans ((orderOf_coe x).trans (hx.trans hC))
  · exact congrArg (fun y : C => (y : S)) (DFunLike.congr_fun hsq x)

/-- The rotation subgroup has order divisible by four and is characteristic,
including the dihedral group of order eight. -/
theorem DihedralSemidihedral.exists_characteristic_cyclic_rotation {S : Type*} [Group S] [Finite S]
    (hmodel : (∃ n : ℕ, 2 ≤ n ∧ Nonempty (S ≃* DihedralGroup (2 ^ n))) ∨
      (∃ (n : ℕ) (hn : 4 ≤ n), Nonempty (S ≃* Semidihedral.StandardModel n hn))) :
    ∃ R : Subgroup S, R.Characteristic ∧ IsCyclic R ∧ 4 ∣ Nat.card R := by
  have transport {H : Type} [Group H] (e : S ≃* H) (R : Subgroup H)
      [R.Characteristic] [IsCyclic R] (hcard : 4 ∣ Nat.card R) :
      ∃ R : Subgroup S, R.Characteristic ∧ IsCyclic R ∧ 4 ∣ Nat.card R := by
    let R' := R.comap e.toMonoidHom
    have he : R' ≃* R :=
      { toFun := fun x => ⟨e x, x.property⟩
        invFun := fun x => ⟨e.symm x, by change e (e.symm x) ∈ R; simpa only [e.apply_symm_apply] using x.property⟩
        left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
        right_inv := fun x => Subtype.ext (e.apply_symm_apply x)
        map_mul' := fun x y => Subtype.ext (e.map_mul x y) }
    refine ⟨R', ?_, he.isCyclic.mpr inferInstance, (Nat.card_congr he.toEquiv).symm ▸ hcard⟩
    apply characteristic_iff_le_comap.mpr
    intro α x hx
    have hh := characteristic_iff_le_comap.mp (inferInstance : R.Characteristic)
      (e.symm.trans (α.trans e)) (by exact hx)
    change e (α (e.symm (e x))) ∈ R at hh
    change e (α x) ∈ R
    simpa only [e.symm_apply_apply] using hh
  rcases hmodel with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · let R := zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ n))
    let : R.Characteristic := DihedralGroup.rotations_characteristic
      (lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) hn))
    apply transport e R
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
    exact pow_dvd_pow 2 hn
  · let a := Semidihedral.standardRotation n hn
    let b := Semidihedral.standardReflection n hn
    let : (zpowers a).Characteristic := Semidihedral.rotations_characteristic hn a b
      (Semidihedral.standardRotation_order n hn) (Semidihedral.standardReflection_order n hn)
      (Semidihedral.standard_conjugation n hn) (Semidihedral.standard_generators n hn)
    apply transport e (zpowers a)
    rw [Nat.card_zpowers, Semidihedral.standardRotation_order]
    exact pow_dvd_pow 2 (by omega : 2 ≤ n - 1)
