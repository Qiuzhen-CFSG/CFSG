module

public import Theory.Mathieu.M12.BlockGeometry.SecondSquareControl
public import Theory.Mathieu.M12.ExceptionalParabolics
public import Theory.GroupTheory.AbelianExponentFourRecognition

/-!
# The literal C₄ × C₄ kernel in the M₁₂ row of F.6.18

The two marked commuting square roots from the actual natural-four normalizer
have distinct nontrivial squares. Their cyclic groups are disjoint, and their
product is the already constructed normal radical. This identifies that same
radical with C₄ × C₄. A twelve-element complement supplies its actual dihedral
quotient, preserving the original second parabolic and subgroup inclusion.

Source: Aschbacher–Smith, F.6.18(12), printed p.310; the marked permutations
and normality calculation are those of 14.2.21 and GLS3 Table 5.3b.
-/

public noncomputable section
open Subgroup
open Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair
open Sporadic.Mathieu.M12SmallPair.SecondSquareControl
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu.InnerSquare

abbrev C4Square := Multiplicative (ZMod 4) × Multiplicative (ZMod 4)

private theorem rootOne_order : orderOf rootOne = 4 :=
  orderOf_eq_four_of_fourth_power (by decide +kernel) (by decide +kernel)
private theorem rootTwo_order : orderOf rootTwo = 4 :=
  orderOf_eq_four_of_fourth_power (by decide +kernel) (by decide +kernel)
private theorem roots_commute : Commute rootOne rootTwo := by
  change rootOne * rootTwo = rootTwo * rootOne
  decide +kernel

private def productHom : zpowers rootOne × zpowers rootTwo →* M12 :=
  (zpowers rootOne).subtype.noncommCoprod (zpowers rootTwo).subtype (by
    intro a b
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp a.property
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp b.property
    change Commute (a : M12) (b : M12)
    rw [← hi, ← hj]
    exact roots_commute.zpow_zpow i j)

private theorem productHom_injective : Function.Injective productHom := by
  apply (MonoidHom.noncommCoprod_injective _ _ _).mpr
  refine ⟨Subtype.val_injective, Subtype.val_injective, ?_⟩
  simpa only [range_subtype] using
    disjoint_zpowers_of_order_four_distinct_squares rootOne_order rootTwo_order
      (by decide +kernel : rootOne ^ 2 ≠ rootTwo ^ 2)

private theorem productHom_range : productHom.range = radical := by
  rw [productHom, MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  apply le_antisymm
  · exact sup_le (zpowers_le.mpr (subset_closure (by simp)))
      (zpowers_le.mpr (subset_closure (by simp)))
  · apply (closure_le _).mpr
    rintro x (rfl | rfl)
    · exact Subgroup.mem_sup_left (mem_zpowers rootOne)
    · exact Subgroup.mem_sup_right (mem_zpowers rootTwo)

/-- The same normal radical used in the natural-four action is C₄ × C₄. -/
def radicalEquiv : radical ≃* C4Square :=
  ((MonoidHom.ofInjective productHom_injective).trans
    (MulEquiv.subgroupCongr productHom_range)).symm.trans
      ((mulEquivOfCyclicCardEq (by rw [Nat.card_zpowers, rootOne_order]; simp [Nat.card_eq_fintype_card]) :
          zpowers rootOne ≃* Multiplicative (ZMod 4)).prodCongr
        (mulEquivOfCyclicCardEq (by rw [Nat.card_zpowers, rootTwo_order]; simp [Nat.card_eq_fintype_card]) :
          zpowers rootTwo ≃* Multiplicative (ZMod 4)))

theorem radical_card : Nat.card radical = 16 := by
  rw [Nat.card_congr radicalEquiv.toEquiv]
  simp [C4Square, Nat.card_eq_fintype_card]

/-- Small coordinates for membership in the literal normal radical. -/
theorem mem_radical_iff (x : M12) : x ∈ radical ↔
    ∃ i j : Fin 4, rootOne ^ i.val * rootTwo ^ j.val = x := by
  constructor
  · intro hx
    rw [← productHom_range] at hx
    obtain ⟨⟨a,b⟩, hab⟩ := hx
    obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp a.property)
    obtain ⟨j, hj, hjb⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp b.property)
    have hi4 : i < 4 := by simpa only [rootOne_order, Finset.mem_range] using hi
    have hj4 : j < 4 := by simpa only [rootTwo_order, Finset.mem_range] using hj
    change (a : M12) * (b : M12) = x at hab
    exact ⟨⟨i,hi4⟩,⟨j,hj4⟩, by simpa only [hia, hjb] using hab⟩
  · rintro ⟨i,j,rfl⟩
    exact radical.mul_mem (radical.pow_mem (subset_closure (by simp)) _)
      (radical.pow_mem (subset_closure (by simp)) _)

/-- The denominator as a subgroup of the actual second parabolic. -/
@[expose] def localRadical : Subgroup secondParabolic := radical.subgroupOf secondParabolic

instance : localRadical.Normal := SecondSquareControl.radical_normal

def localRadicalEquiv : localRadical ≃* C4Square :=
  (subgroupOfEquivOfLe (radical_le_sylow.trans inf_le_right)).trans radicalEquiv

theorem localRadical_card : Nat.card localRadical = 16 := by
  rw [Nat.card_congr localRadicalEquiv.toEquiv]
  simp [C4Square, Nat.card_eq_fintype_card]

private def rotation : secondParabolic :=
  ⟨SylowEnumeration.wordElement 160, SylowEnumeration.wordElement_mem 160⟩
private def reflection : secondParabolic :=
  ⟨SylowEnumeration.wordElement 47, SylowEnumeration.wordElement_mem 47⟩
private def dihedralValue : DihedralGroup 6 → secondParabolic
  | .r i => rotation ^ i.val
  | .sr i => reflection * rotation ^ i.val

private theorem dihedralValue_mul : ∀ x y : DihedralGroup 6,
    dihedralValue (x*y) = dihedralValue x * dihedralValue y := by decide +kernel

private def dihedralHom : DihedralGroup 6 →* secondParabolic where
  toFun := dihedralValue
  map_one' := by decide +kernel
  map_mul' := dihedralValue_mul

private theorem complement_disjoint : ∀ x : DihedralGroup 6, ∀ i j : Fin 4,
    (dihedralValue x : M12) = rootOne ^ i.val * rootTwo ^ j.val → x = 1 := by
  decide +kernel

private def quotientHom : DihedralGroup 6 →* secondParabolic ⧸ localRadical :=
  (QuotientGroup.mk' localRadical).comp dihedralHom

private theorem quotientHom_injective : Function.Injective quotientHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro x hx
  have hm : dihedralHom x ∈ localRadical := (QuotientGroup.eq_one_iff _).mp hx
  obtain ⟨i,j,hij⟩ := (mem_radical_iff (dihedralHom x : M12)).mp hm
  exact (complement_disjoint x i j hij.symm)

private theorem quotient_card : Nat.card (secondParabolic ⧸ localRadical) = 12 := by
  have h := localRadical.card_mul_index
  rw [localRadical_card, card_secondParabolic] at h
  change localRadical.index = 12
  omega

/-- The actual second parabolic modulo its C₄ × C₄ radical is D₁₂. -/
def secondQuotientEquiv : (secondParabolic ⧸ localRadical) ≃* DihedralGroup 6 :=
  (MulEquiv.ofBijective quotientHom
    (quotientHom_injective.bijective_of_nat_card_le (by
      rw [quotient_card, DihedralGroup.nat_card]))).symm

/-- The complete extension assertion on the source's original second vertex. -/
theorem second_extension : ∃ N : Subgroup secondParabolic, ∃ _ : N.Normal,
    Nonempty (N ≃* C4Square) ∧ Nonempty ((secondParabolic ⧸ N) ≃* DihedralGroup 6) :=
  ⟨localRadical, inferInstance, ⟨localRadicalEquiv⟩, ⟨secondQuotientEquiv⟩⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu.InnerSquare
