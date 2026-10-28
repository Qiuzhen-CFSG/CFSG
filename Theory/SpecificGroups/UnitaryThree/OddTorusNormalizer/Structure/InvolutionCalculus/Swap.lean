module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# A swap acting on a two-factor abelian image

For a homomorphism from `A × A` whose kernel lies in the diagonal cubic
subgroup, an element exchanging the two factors fixes exactly the diagonal
image. Its commutator with the image is exactly the anti-diagonal image,
which embeds injectively. With the full diagonal cubic kernel, the fixed
image is isomorphic to the cubic-power image of `A`.

These group calculations are applied to the actual frame-torus maps in
`InvolutionCalculus.lean`. They use the commutator convention `a*b*a⁻¹*b⁻¹`.
Source: GLS4, Chapter 4, Lemma 3.11(c), and Chapter 2, Lemma 17.4.
-/

public section

open Subgroup
open scoped commutatorElement
namespace UnitaryThree.OddTorusNormalizer.InvolutionCalculus
variable {A G : Type*} [CommGroup A] [Group G]

@[expose] def diagonalMap (f : A × A →* G) : A →* G :=
  f.comp ((MonoidHom.id A).prod (MonoidHom.id A))

@[expose] def antiDiagonalMap (f : A × A →* G) : A →* G :=
  f.comp ((MonoidHom.id A).prod (invMonoidHom : A →* A))

lemma eq_one_of_inv_eq_cube {a : A} (hi : a = a⁻¹) (hc : a ^ 3 = 1) : a = 1 := by
  have h2 : a ^ 2 = 1 := by
    rw [pow_two]
    calc a * a = a * a⁻¹ := congrArg (a * ·) hi
         _ = 1 := mul_inv_cancel a
  simpa only [pow_succ, h2, one_mul] using hc

lemma antiDiagonalMap_injective (f : A × A →* G)
    (hk : ∀ x, f x = 1 → x.1 = x.2 ∧ x.2 ^ 3 = 1) :
    Function.Injective (antiDiagonalMap f) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  obtain ⟨hi, hc⟩ := hk (a, a⁻¹) ha
  change a = a⁻¹ at hi
  change (a⁻¹) ^ 3 = 1 at hc
  exact eq_one_of_inv_eq_cube hi (by simpa only [← hi] using hc)

lemma swap_eq_iff (f : A × A →* G)
    (hk : ∀ x, f x = 1 → x.1 = x.2 ∧ x.2 ^ 3 = 1) (a b : A) :
    f (b, a) = f (a, b) ↔ a = b := by
  constructor
  · intro h
    have hh : f (a / b, b / a) = 1 := by
      change f ((a, b) / (b, a)) = 1
      rw [map_div, h, div_self']
    obtain ⟨hi, hc⟩ := hk _ hh
    change a / b = b / a at hi
    change (b / a) ^ 3 = 1 at hc
    have hi' : a / b = (a / b)⁻¹ := by simpa using hi
    exact div_eq_one.mp (eq_one_of_inv_eq_cube hi' (by simpa only [← hi] using hc))
  · rintro rfl; rfl

lemma inf_centralizer_eq_diagonal_range (f : A × A →* G) (t : G)
    (hk : ∀ x, f x = 1 → x.1 = x.2 ∧ x.2 ^ 3 = 1)
    (hact : ∀ a b, t * f (a, b) * t⁻¹ = f (b, a)) :
    f.range ⊓ centralizer {t} = (diagonalMap f).range := by
  have hfix (a b : A) : f (a, b) ∈ centralizer {t} ↔ a = b := by
    rw [mem_centralizer_singleton_iff]
    have he : f (a, b) * t = t * f (a, b) ↔ f (b, a) = f (a, b) := by
      rw [← hact a b]
      constructor
      · intro h; rw [← h, mul_inv_cancel_right]
      · intro h
        have hh := congrArg (fun g => g * t) h
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh.symm
    rw [he, swap_eq_iff f hk]
  ext g
  constructor
  · rintro ⟨⟨⟨a, b⟩, rfl⟩, hc⟩
    obtain rfl := (hfix a b).mp hc
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨(a, a), rfl⟩, (hfix a a).mpr rfl⟩

lemma swap_commutator (f : A × A →* G) (t : G)
    (hact : ∀ a b, t * f (a, b) * t⁻¹ = f (b, a)) (a b : A) :
    ⁅f (a, b), t⁆ = antiDiagonalMap f (a / b) := by
  calc
    ⁅f (a, b), t⁆ = f (a, b) * (t * f (a, b) * t⁻¹)⁻¹ := by
      simp [commutatorElement_def, mul_assoc]
    _ = f ((a, b) / (b, a)) := by rw [hact, map_div, div_eq_mul_inv]
    _ = antiDiagonalMap f (a / b) := by
      change f (a / b, b / a) = f (a / b, (a / b)⁻¹)
      congr 1
      simp

lemma commutator_eq_antiDiagonal_range (f : A × A →* G) (t : G)
    (ht : orderOf t = 2)
    (hact : ∀ a b, t * f (a, b) * t⁻¹ = f (b, a)) :
    ⁅f.range, zpowers t⁆ = (antiDiagonalMap f).range := by
  classical
  apply le_antisymm
  · apply commutator_le.mpr
    rintro _ ⟨⟨a, b⟩, rfl⟩ y hy
    have hfin : IsOfFinOrder t := orderOf_pos_iff.mp (by rw [ht]; decide)
    have hy' := hfin.mem_zpowers_iff_mem_range_orderOf.mp hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy'
    have hk2 : k < 2 := by simpa only [Finset.mem_range, ht] using hk
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · simp
    · rw [pow_one, swap_commutator f t hact]
      exact ⟨a / b, rfl⟩
  · rintro _ ⟨a, rfl⟩
    have h := commutator_mem_commutator (show f (a, 1) ∈ f.range from ⟨(a, 1), rfl⟩)
      (mem_zpowers t)
    simpa only [swap_commutator f t hact, div_one] using h

noncomputable def commutatorEquiv (f : A × A →* G) (t : G)
    (ht : orderOf t = 2)
    (hk : ∀ x, f x = 1 → x.1 = x.2 ∧ x.2 ^ 3 = 1)
    (hact : ∀ a b, t * f (a, b) * t⁻¹ = f (b, a)) :
    ↥⁅f.range, zpowers t⁆ ≃* A :=
  (MulEquiv.subgroupCongr (commutator_eq_antiDiagonal_range f t ht hact)).trans
    (MonoidHom.ofInjective (antiDiagonalMap_injective f hk)).symm

noncomputable def diagonalRangeEquivCubeRange (f : A × A →* G)
    (hk : ∀ x, f x = 1 ↔ x.1 = x.2 ∧ x.2 ^ 3 = 1) :
    (diagonalMap f).range ≃* (powMonoidHom 3 : A →* A).range := by
  have he : (diagonalMap f).ker = (powMonoidHom 3 : A →* A).ker := by
    ext a
    change f (a, a) = 1 ↔ a ^ 3 = 1
    simpa only [true_and] using hk (a, a)
  exact (QuotientGroup.quotientKerEquivRange (diagonalMap f)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq he).trans
      (QuotientGroup.quotientKerEquivRange (powMonoidHom 3 : A →* A)))

end UnitaryThree.OddTorusNormalizer.InvolutionCalculus
