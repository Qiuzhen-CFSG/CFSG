module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.SquareCalculation
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# The actual binary central extension in the M₁₂ cover calculation

The quotient is R/⟨v₄⟩, with its literal projection and the injected image
of Z(K). The coordinate map has exactly that image as kernel. In particular
the kernel has order two, the quotient has order 32, and a zero square form
identifies this actual group with the elementary abelian group of rank five.

Source: Aschbacher–Smith, I.2.2(5), printed p.412 / PDF p.423.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
open Theory.LinearAlgebra.BinaryCubicOrbits
variable {K : Type*} [Group K] {u : K}
namespace SquareCoordinates
variable (d : SquareCoordinates u)

abbrev BinaryQuotient := (centralizerCore u) ⧸ d.squareLine

noncomputable def quotientCoordinates : d.BinaryQuotient →* Multiplicative Space :=
  d.doubleQuotientCoordinates.toMonoidHom.comp (QuotientGroup.mk' d.quotientCenter)

@[simp] theorem quotientCoordinates_mk (r : centralizerCore u) :
    d.quotientCoordinates (QuotientGroup.mk' d.squareLine r) = d.coordinates r := rfl

theorem quotientCoordinates_surjective : Function.Surjective d.quotientCoordinates :=
  d.doubleQuotientCoordinates.surjective.comp (QuotientGroup.mk'_surjective _)

theorem quotientCoordinates_ker : d.quotientCoordinates.ker = d.quotientCenter := by
  ext x
  change d.doubleQuotientCoordinates (QuotientGroup.mk' d.quotientCenter x) = 1 ↔ _
  rw [d.doubleQuotientCoordinates.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff x

theorem quotient_square_eq_one_iff (r : d.BinaryQuotient) :
    r ^ 2 = 1 ↔ d.quadratic (d.quotientCoordinates r).toAdd = 0 := by
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective d.squareLine r
  exact d.square_in_quotient_eq_one_iff r

theorem quotient_square_mem (r : d.BinaryQuotient) : r ^ 2 ∈ d.quotientCenter := by
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective d.squareLine r
  rw [← map_pow, ← d.center_image_eq]
  exact mem_map_of_mem _ (d.square_central r)

theorem quotientCenter_le_center : d.quotientCenter ≤ center d.BinaryQuotient := by
  rw [← d.center_image_eq]
  rintro _ ⟨z, hz, rfl⟩
  apply mem_center_iff.mpr
  intro x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective d.squareLine x
  simp only [← map_mul]
  exact congrArg (QuotientGroup.mk' d.squareLine) (mem_center_iff.mp hz x)

def centerInjection : center K →* d.BinaryQuotient :=
  (QuotientGroup.mk' d.squareLine).comp (Subgroup.inclusion d.ambient_center_le)

@[simp] theorem centerInjection_apply (z : center K) :
    d.centerInjection z = QuotientGroup.mk' d.squareLine
      ⟨z, d.ambient_center_le z.property⟩ := rfl

theorem centerInjection_range : d.centerInjection.range = d.quotientCenter := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact mem_map.mpr ⟨⟨z, d.ambient_center_le z.property⟩, z.property, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨⟨r, hr⟩, rfl⟩

private theorem squareLine_elements (r : centralizerCore u) (hr : r ∈ d.squareLine) :
    r = 1 ∨ r = d.root ^ 2 := by
  classical
  have hp : (d.root ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact d.fourth_power _
  have hf : IsOfFinOrder (d.root ^ 2) := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hp⟩
  by_cases h1 : d.root ^ 2 = 1
  · simpa [squareLine, h1] using hr
  have ho : orderOf (d.root ^ 2) = 2 := orderOf_eq_prime hp h1
  change r ∈ zpowers (d.root ^ 2) at hr
  rw [hf.mem_zpowers_iff_mem_range_orderOf, ho] at hr
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hr
  have hi2 := Finset.mem_range.mp hi
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · exact Or.inl (by simpa using hix.symm)
  · exact Or.inr (by simpa using hix.symm)

theorem centerInjection_injective (hu : u ∉ center K) :
    Function.Injective d.centerInjection := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro z hz
  have hzL : (⟨z, d.ambient_center_le z.property⟩ : centralizerCore u) ∈ d.squareLine :=
    (QuotientGroup.eq_one_iff _).mp hz
  rcases d.squareLine_elements _ hzL with h | h
  · change z = 1
    exact Subtype.ext (congrArg (fun x : centralizerCore u => (x : K)) h)
  · exfalso
    apply hu
    apply (QuotientGroup.eq_one_iff u).mp
    change QuotientGroup.mk' (center K) u = 1
    have he : (z : K) = (d.root : K) ^ 2 := congrArg Subtype.val h
    rw [← d.root_square_mark, ← he]
    exact (QuotientGroup.eq_one_iff _).mpr z.property

theorem quotientCenter_card (hu : u ∉ center K) (hZ : Nat.card (center K) = 2) :
    Nat.card d.quotientCenter = 2 := by
  rw [← d.centerInjection_range]
  exact (Nat.card_congr (MonoidHom.ofInjective (d.centerInjection_injective hu)).toEquiv).symm.trans hZ

theorem quotient_card (hu : u ∉ center K) (hZ : Nat.card (center K) = 2) :
    Nat.card d.BinaryQuotient = 32 := by
  have h := d.quotientCenter.card_mul_index
  rw [d.quotientCenter_card hu hZ, index_eq_card,
    Nat.card_congr d.doubleQuotientCoordinates.toEquiv] at h
  have hc : Nat.card (Multiplicative Space) = 16 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [hc] at h
  exact h.symm

theorem quotient_elementary (hq : d.quadratic = 0) :
    IsElementaryAbelian 2 d.BinaryQuotient := by
  have hs (r : d.BinaryQuotient) : r ^ 2 = 1 :=
    (d.quotient_square_eq_one_iff r).mpr (by rw [hq]; rfl)
  have hi (r : d.BinaryQuotient) : r⁻¹ = r :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs r)
  refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  calc
    x * y = (x * y)⁻¹ := (hi _).symm
    _ = y * x := by rw [mul_inv_rev, hi, hi]

/-- A genuine model identification in the elementary branch. -/
theorem quotient_equiv_elementary [Finite K] (hu : u ∉ center K)
    (hZ : Nat.card (center K) = 2) (hq : d.quadratic = 0) :
    Nonempty (d.BinaryQuotient ≃* Multiplicative (Fin 5 → ZMod 2)) := by
  let := d.quotient_elementary hq
  have hc : Nat.card d.BinaryQuotient =
      2 ^ Module.finrank (ZMod 2) (Additive d.BinaryQuotient) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive d.BinaryQuotient)
  have hd : Module.finrank (ZMod 2) (Additive d.BinaryQuotient) = 5 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    change 2 ^ Module.finrank (ZMod 2) (Additive d.BinaryQuotient) = 2 ^ 5
    rw [← hc, d.quotient_card hu hZ]
  let e : Additive d.BinaryQuotient ≃ₗ[ZMod 2] (Fin 5 → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [hd])
  exact ⟨e.toAddEquiv.toMultiplicativeRight⟩

end SquareCoordinates
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
