module
public import GorensteinWalter.DihedralCore
public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

/-!
# Four-group products in groups with dihedral Sylow subgroups of order sixteen

Every four-group in D₁₆ contains the central involution and a reflection.
Conjugating that reflection by a generator of the rotations produces a
product of order four. Its conjugacy class is the square of any order-eight
element. Sylow conjugacy extends this calculation to the ambient group.

Source: the involution-centralizer argument in Guralnick--Malle,
Classification of 2F-modules I, Proposition 4.1, manuscript p.9.
-/

public section
namespace Theory.GroupTheory.DihedralSixteenProducts
open Subgroup GorensteinWalter
open scoped Pointwise
private abbrev D := DihedralGroup 8

private theorem fourth_ne_one_square (q : D) (hq : q ^ 4 ≠ 1) :
    q ^ 2 = DihedralGroup.r 2 ∨ q ^ 2 = DihedralGroup.r 6 := by
  have hc : ∀ q : D, q ^ 4 ≠ 1 →
      q ^ 2 = DihedralGroup.r 2 ∨ q ^ 2 = DihedralGroup.r 6 := by decide
  exact hc q hq

private theorem reflection_product (j : ZMod 8) :
    DihedralGroup.sr j *
      (DihedralGroup.r 1 * DihedralGroup.sr j * (DihedralGroup.r 1)⁻¹) =
      DihedralGroup.r 6 := by
  have hc : ∀ j : ZMod 8, DihedralGroup.sr j *
      (DihedralGroup.r 1 * DihedralGroup.sr j * (DihedralGroup.r 1)⁻¹) =
      DihedralGroup.r 6 := by decide
  exact hc j

/-- The calculation in the sixteen-element dihedral group. -/
theorem model_product (q : DihedralGroup 8) (hq : orderOf q = 8)
    (A : Subgroup (DihedralGroup 8)) (hA : IsKleinFour A) :
    ∃ t g a b : DihedralGroup 8, t ∈ A ∧ orderOf t = 2 ∧ Commute g t ∧ a ∈ A ∧ b ∈ A ∧
      IsConj (q ^ 2) (a * (g * b * g⁻¹)) := by
  have hcentral : DihedralGroup.r (4 : ZMod 8) ∈ center D := by
    rw [mem_center_iff]
    decide
  have htA : DihedralGroup.r (4 : ZMod 8) ∈ A :=
    center_mem_kleinFour_of_dihedral_mulEquiv (m := 3) (by decide)
      (MulEquiv.refl D) A hA hcentral
  let R : Subgroup D := zpowers (DihedralGroup.r 1)
  have hn : ¬ A ≤ R := by
    intro ha
    let : IsKleinFour A := hA
    exact IsKleinFour.not_isCyclic (G := A) (Subgroup.isCyclic_of_le ha)
  obtain ⟨s, hs, hsR⟩ := SetLike.not_le_iff_exists.mp hn
  obtain ⟨j, hj⟩ : ∃ j : ZMod 8, DihedralGroup.sr j ∈ A := by
    cases s with
    | r i => exact (hsR (r_mem_zpowers_r_one i)).elim
    | sr i => exact ⟨i, hs⟩
  refine ⟨DihedralGroup.r 4, DihedralGroup.r 1, DihedralGroup.sr j,
    DihedralGroup.sr j, htA, ?_, ?_, hj, hj, ?_⟩
  · exact orderOf_eq_prime (by decide) (by decide)
  · change DihedralGroup.r (1 : ZMod 8) * DihedralGroup.r 4 =
      DihedralGroup.r 4 * DihedralGroup.r 1
    decide
  · rw [reflection_product]
    have hq4 : q ^ 4 ≠ 1 := by
      intro he
      have hd := orderOf_dvd_of_pow_eq_one he
      rw [hq] at hd
      norm_num at hd
    rcases fourth_ne_one_square q hq4 with h2 | h6
    · rw [h2]
      apply isConj_iff.mpr
      exact ⟨DihedralGroup.sr 0, by decide⟩
    · rw [h6]

/-- Sylow conjugacy makes the local calculation apply to an arbitrary
order-eight actor and an arbitrary four-group of the ambient group. -/
theorem product_of_dihedral_sylows {G : Type*} [Group G] [Finite G]
    (hSylow : ∀ S : Sylow 2 G, Nonempty (S ≃* DihedralGroup 8))
    (r : G) (hr : orderOf r = 8) (A : Subgroup G) (hA : IsKleinFour A) :
    ∃ t g a b : G, t ∈ A ∧ orderOf t = 2 ∧ Commute g t ∧ a ∈ A ∧ b ∈ A ∧
      IsConj (r ^ 2) (a * (g * b * g⁻¹)) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hAp : IsPGroup 2 A := IsPGroup.of_card (n := 2) hA.card_four
  obtain ⟨S, hAS⟩ := hAp.exists_le_sylow
  have hRp : IsPGroup 2 (zpowers r) := IsPGroup.of_card (n := 3)
    (by rw [Nat.card_zpowers, hr]; rfl)
  obtain ⟨R, hRS⟩ := hRp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G R S
  have hrS : c * r * c⁻¹ ∈ (S : Subgroup G) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    exact Set.mem_smul_set.mpr ⟨r, hRS (mem_zpowers r), rfl⟩
  let rS : S := ⟨c * r * c⁻¹, hrS⟩
  have hrS8 : orderOf rS = 8 := by
    rw [← Subgroup.orderOf_coe]
    change orderOf (MulAut.conj c r) = 8
    rw [MulEquiv.orderOf_eq, hr]
  obtain ⟨e⟩ := hSylow S
  let B := A.subgroupOf S
  let eB : B ≃* A := subgroupOfEquivOfLe hAS
  let C := B.map e.toMonoidHom
  let eC : B ≃* C := B.equivMapOfInjective e.toMonoidHom e.injective
  have hC : IsKleinFour C := {
    card_four := (Nat.card_congr eC.toEquiv).symm.trans
      ((Nat.card_congr eB.toEquiv).trans hA.card_four)
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eC).symm.trans
      ((Monoid.exponent_eq_of_mulEquiv eB).trans hA.exponent_two) }
  obtain ⟨t, g, a, b, ht, ht2, hgt, ha, hb, hp⟩ :=
    model_product (e rS) ((e.orderOf_eq rS).trans hrS8) C hC
  let f : DihedralGroup 8 →* G := (S : Subgroup G).subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  have hmem : ∀ y ∈ C, f y ∈ A := by
    rintro y ⟨z, hz, rfl⟩
    change (e.symm (e z) : G) ∈ A
    rw [e.symm_apply_apply]
    exact hz
  refine ⟨f t, f g, f a, f b, hmem t ht, ?_, hgt.map f, hmem a ha,
    hmem b hb, ?_⟩
  · rw [orderOf_injective f hf, ht2]
  · have he : IsConj ((c * r * c⁻¹) ^ 2) (f a * (f g * f b * (f g)⁻¹)) := by
      have hh := f.map_isConj hp
      have hfr : f (e rS) = c * r * c⁻¹ := by
        change (e.symm (e rS) : G) = _
        rw [e.symm_apply_apply]
      simpa only [map_pow, map_mul, map_inv, hfr] using hh
    apply IsConj.trans (b := (c * r * c⁻¹) ^ 2) ?_ he
    apply isConj_iff.mpr
    exact ⟨c, map_pow (MulAut.conj c) r 2⟩

end Theory.GroupTheory.DihedralSixteenProducts
