module
public import Theory.GroupTheory.SpecificGroups.DihedralAut
public import Theory.GroupTheory.SpecificGroups.KleinFourFixedAut
public import Theory.PGroupCore
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.Tactic.IntervalCases

/-!
# A characteristic-two group with a small dihedral core

A group with self-centralizing two-core, a nontrivial central element, and a
faithful embedding of its core in the dihedral group of order eight is a
two-group. If the core has order eight, all its automorphisms form a two-group.
Otherwise it has order at most four, and the fixed central point leaves at most
two points for an automorphism to permute.

This is the centralizer calculation in Aschbacher--Smith 2.4.34, printed p.548.
-/
public section
namespace Theory.GroupTheory
open Subgroup

private theorem small_fixed_automorphisms
    {P : Type*} [Group P] [Finite P] (hc : Nat.card P ≤ 4)
    (A : Subgroup (MulAut P)) (v : P) (hv : v ≠ 1)
    (hfix : ∀ f ∈ A, f v = v) : IsPGroup 2 A := by
  classical
  let : Fintype P := Fintype.ofFinite P
  let R := {x : P // x ∉ ({1, v} : Set P)}
  have hp (f : A) (x : P) :
      ((f : MulAut P) x ∉ ({1, v} : Set P)) ↔ x ∉ ({1, v} : Set P) := by
    have hf := hfix f f.property
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [← hf, f.val.injective.eq_iff]
    simp [hf]
  let restrict : A → Equiv.Perm R := fun f =>
    Equiv.Perm.subtypePerm f.val.toEquiv (hp f)
  have hinj : Function.Injective restrict := by
    intro f g h
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    by_cases hx : x = 1
    · subst x; simp
    by_cases hxv : x = v
    · subst x; rw [hfix f f.property, hfix g g.property]
    have hr : x ∉ ({1, v} : Set P) := by simpa using And.intro hx hxv
    exact congrArg Subtype.val (Equiv.congr_fun h (⟨x, hr⟩ : R))
  have hcardR : Fintype.card R ≤ 2 := by
    dsimp [R]
    rw [Fintype.card_subtype_compl]
    have htwo : Nat.card {x : P // x ∈ ({1, v} : Set P)} = 2 := by
      rw [Nat.card_coe_set_eq]
      simp [Ne.symm hv]
    simp only [← Nat.card_eq_fintype_card, htwo]
    omega
  have hcard : Nat.card A ≤ 2 := by
    have h := Nat.card_le_card_of_injective restrict hinj
    simp only [Nat.card_eq_fintype_card, Fintype.card_perm] at h
    simpa only [Nat.card_eq_fintype_card] using
      h.trans ((Nat.factorial_le hcardR).trans_eq (show Nat.factorial 2 = 2 from rfl))
  have hpos : 0 < Nat.card A := Nat.card_pos
  apply IsPGroup.of_card_dvd_pow (n := 1)
  have hcases : Nat.card A = 1 ∨ Nat.card A = 2 := by omega
  rcases hcases with h | h <;> simp only [h, pow_one, one_dvd, dvd_refl]

/-- A self-centralizing two-core which embeds in D₈ and has a nonidentity
ambient-central point forces the whole finite group to be a two-group. -/
theorem isTwoGroup_of_dihedral_core_and_central_point
    {H : Type*} [Group H] [Finite H]
    (hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (i : H) (hi : i ≠ 1) (hic : i ∈ center H)
    (f : pCore 2 H →* DihedralGroup 4) (hf : Function.Injective f) :
    IsPGroup 2 H := by
  let P := pCore 2 H
  let action : H →* MulAut P := MulAut.conjNormal
  have hiP : i ∈ P := hchar (mem_centralizer_iff.mpr fun a _ => mem_center_iff.mp hic a)
  let v : P := ⟨i, hiP⟩
  have hv : v ≠ 1 := fun he => hi (congrArg Subtype.val he)
  have hfix : ∀ a ∈ action.range, a v = v := by
    rintro a ⟨g, rfl⟩
    apply Subtype.ext
    change g * i * g⁻¹ = i
    rw [(mem_center_iff.mp hic g), mul_inv_cancel_right]
  have hPdiv : Nat.card P ∣ 8 := by
    have h := card_dvd_of_injective f hf
    simpa only [DihedralGroup.nat_card] using h
  have hPsmall : Nat.card P ≤ 4 ∨ Nat.card P = 8 := by
    obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card P ∣ 2^3 from hPdiv)
    rw [he]
    interval_cases k <;> decide
  have hrange : IsPGroup 2 action.range := by
    rcases hPsmall with h | h
    · exact small_fixed_automorphisms h action.range v hv hfix
    · have hsurj : Function.Surjective f :=
        (Nat.bijective_iff_injective_and_card _).mpr ⟨hf, by
          simpa only [DihedralGroup.nat_card] using h⟩ |>.surjective
      let e : P ≃* DihedralGroup 4 := MulEquiv.ofBijective f ⟨hf, hsurj⟩
      have hd : IsPGroup 2 (DihedralGroup 4) := IsPGroup.of_card (n := 3) (by
        simp only [DihedralGroup.nat_card]; decide)
      have ha : IsPGroup 2 (MulAut P) :=
        (DihedralGroup.isPGroup_mulAut_of_two_lt (by decide) hd).of_equiv
          (MulAut.congr e).symm
      exact ha.to_subgroup action.range
  have hker : IsPGroup 2 action.ker := pCore_isPGroup.to_le (by
    change (MulAut.conjNormal : H →* MulAut (pCore 2 H)).ker ≤ pCore 2 H
    rw [MulAut.conjNormal_ker_eq_centralizer]
    exact hchar)
  have hpre := hrange.comap_of_ker_isPGroup action hker
  rw [MonoidHom.comap_range_self] at hpre
  exact hpre.of_equiv Subgroup.topEquiv

end Theory.GroupTheory
