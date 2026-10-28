module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.TwoPrimary.PlaneModel
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.AtlasPort.LinearGroups.SL2Order
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# An odd-index pair of symplectic planes and its involution fusion

Two copies of the actual SL₂ matrix group act on the perpendicular planes
⟨e₀,f₀⟩ and ⟨e₁,f₁⟩. Their interchange extends this injective product map
to SL₂ wreath C₂ in the actual symplectic four-space matrix group. Its
literal range has index p²(p²+1)/2, odd for every odd prime p.

The change of basis with columns e₀−e₁, e₀+e₁, (f₀−f₁)/2, (f₀+f₁)/2
is symplectic and conjugates the one-plane sign to the interchange.
Only the invertibility of 2 is needed, including at p=5. These constructions
fill every field of `PlaneModel`, the geometric input to the section and
transfer argument in `TwoPrimary.exists_section_on_plane_model`.

The pair-matrix calculation follows the existing coordinate construction in
`OddNondefining.ProductTori`; the order formulas are the independently proved
SL₂ and symplectic-group counts. No central-cover assumption is used.

Source: the odd type C₂ multiplier argument behind GLS3 §6.1, and
Aschbacher–Smith, A.2.2(2), printed p.33, I.1.1–4, printed pp.407–408.
-/

public section
noncomputable section
open Matrix

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.TwoPrimary
namespace PlaneGeometry

variable {F : Type*} [Field F]
local notation "SL" => SpecialLinearGroup (Fin 2) F

private def pairMatrix (A B : SL) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks !![A 0 0, 0; 0, B 0 0] !![A 0 1, 0; 0, B 0 1]
    !![A 1 0, 0; 0, B 1 0] !![A 1 1, 0; 0, B 1 1]

private theorem pairMatrix_mem (A B : SL) : pairMatrix A B ∈ Matrix.symplecticGroup (Fin 2) F := by
  have hA : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [det_fin_two] using A.property
  have hB : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    simpa only [det_fin_two] using B.property
  rw [pairMatrix, SymplecticGroup.fromBlocks_mem_iff]
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, mul_comm, hA, hB]

/-- The actions on the two perpendicular coordinate planes. -/
def pairHom : (SL × SL) →* Sp F where
  toFun A := ⟨pairMatrix A.1 A.2, pairMatrix_mem A.1 A.2⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pairMatrix]
  map_mul' A B := by
    apply Subtype.ext
    change pairMatrix (A.1 * B.1) (A.2 * B.2) = pairMatrix A.1 A.2 * pairMatrix B.1 B.2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pairMatrix, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem pairHom_injective : Function.Injective (pairHom (F := F)) := by
  intro A B h
  have he (x y : Fin 2 ⊕ Fin 2) := congrArg (fun g : Sp F => g.val x y) h
  apply Prod.ext
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact he (.inl 0) (.inl 0)
    · exact he (.inl 0) (.inr 0)
    · exact he (.inr 0) (.inl 0)
    · exact he (.inr 0) (.inr 0)
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact he (.inl 1) (.inl 1)
    · exact he (.inl 1) (.inr 1)
    · exact he (.inr 1) (.inl 1)
    · exact he (.inr 1) (.inr 1)


private def swapMatrix : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks !![0, 1; 1, 0] 0 0 !![0, 1; 1, 0]

/-- Simultaneously interchange e₀ with e₁ and f₀ with f₁. -/
def swap : Sp F := ⟨swapMatrix, by
  rw [swapMatrix, SymplecticGroup.fromBlocks_mem_iff]
  refine ⟨by simp, by simp, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two]⟩

theorem swap_sq : (swap (F := F)) * swap = 1 := by
  apply Subtype.ext
  change swapMatrix * swapMatrix = (1 : Matrix _ _ F)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapMatrix, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

/-- The nonidentity element of C₂ interchanges the two SL₂ factors. -/
def action : Multiplicative (ZMod 2) →* MulAut (SL × SL) where
  toFun c := if c.toAdd = 0 then 1 else MulEquiv.prodComm
  map_one' := by simp
  map_mul' c d := by
    obtain ⟨c, rfl⟩ := (Multiplicative.ofAdd : ZMod 2 ≃ Multiplicative (ZMod 2)).surjective c
    obtain ⟨d, rfl⟩ := (Multiplicative.ofAdd : ZMod 2 ≃ Multiplicative (ZMod 2)).surjective d
    fin_cases c <;> fin_cases d <;>
      apply MulEquiv.ext <;> rintro ⟨x, y⟩ <;> rfl

@[simp] theorem action_generator : action (F := F) (.ofAdd 1) = MulEquiv.prodComm := by
  simp [action]

def swapHom : Multiplicative (ZMod 2) →* Sp F where
  toFun c := if c.toAdd = 0 then 1 else swap
  map_one' := by simp
  map_mul' c d := by
    obtain ⟨c, rfl⟩ := (Multiplicative.ofAdd : ZMod 2 ≃ Multiplicative (ZMod 2)).surjective c
    obtain ⟨d, rfl⟩ := (Multiplicative.ofAdd : ZMod 2 ≃ Multiplicative (ZMod 2)).surjective d
    fin_cases c <;> fin_cases d
    · exact (one_mul (1 : Sp F)).symm
    · exact (one_mul swap).symm
    · exact (mul_one swap).symm
    · exact swap_sq.symm

@[simp] theorem swapHom_generator : swapHom (.ofAdd 1) = swap (F := F) := by
  simp [swapHom]

theorem swap_pair (A : SL × SL) : swap * pairHom A = pairHom (A.2, A.1) * swap := by
  apply Subtype.ext
  change swapMatrix * pairMatrix A.1 A.2 = pairMatrix A.2 A.1 * swapMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapMatrix, pairMatrix, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem compatibility (c : Multiplicative (ZMod 2)) :
    (pairHom (F := F)).comp (action c).toMonoidHom =
      (MulAut.conj (swapHom c)).toMonoidHom.comp pairHom := by
  obtain ⟨c, rfl⟩ := (Multiplicative.ofAdd : ZMod 2 ≃ Multiplicative (ZMod 2)).surjective c
  fin_cases c
  · ext A : 1
    change pairHom A = (1 : Sp F) * pairHom A * 1⁻¹
    simp
  · ext A : 1
    change pairHom (A.2, A.1) = swap * pairHom A * swap⁻¹
    rw [swap_pair, mul_inv_cancel_right]

/-- The literal wreath-product embedding in the symplectic matrix group. -/
def inclusion : (SL × SL) ⋊[action] Multiplicative (ZMod 2) →* Sp F :=
  SemidirectProduct.lift pairHom swapHom compatibility

@[simp] theorem inclusion_inl (A : SL × SL) :
    inclusion (SemidirectProduct.inl A) = pairHom A :=
  SemidirectProduct.lift_inl _ _ _ _

@[simp] theorem inclusion_inr :
    inclusion (SemidirectProduct.inr (.ofAdd 1)) = swap (F := F) := by
  simp [inclusion]

theorem swap_not_mem_range : swap (F := F) ∉ pairHom.range := by
  rintro ⟨A, hA⟩
  have h := congrArg (fun g : Sp F => g.val (.inl 0) (.inl 1)) hA
  simp [pairHom, pairMatrix, swap, swapMatrix] at h

theorem inclusion_injective : Function.Injective (inclusion (F := F)) := by
  apply (injective_iff_map_eq_one _).mpr
  rintro ⟨A, c⟩ h
  obtain ⟨c, rfl⟩ := (Multiplicative.ofAdd : ZMod 2 ≃ Multiplicative (ZMod 2)).surjective c
  fin_cases c
  · have hA : pairHom A = 1 := by
      change pairHom A * 1 = 1 at h
      simpa only [mul_one] using h
    have hA' : A = 1 := pairHom_injective (hA.trans (map_one pairHom).symm)
    subst A
    rfl
  · have hA : pairHom A * swap = 1 := by
      exact h
    exfalso
    apply swap_not_mem_range (F := F)
    refine ⟨A⁻¹, ?_⟩
    rw [map_inv]
    exact (eq_inv_of_mul_eq_one_right hA).symm

private def fusionMatrix : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks !![1, 1; -1, 1] 0 0 !![(2 : F)⁻¹, (2 : F)⁻¹; -(2 : F)⁻¹, (2 : F)⁻¹]

/-- The normalized sum/difference basis, requiring only that 2 is invertible. -/
def fusion (h2 : (2 : F) ≠ 0) : Sp F := ⟨fusionMatrix, by
  rw [fusionMatrix, SymplecticGroup.fromBlocks_mem_iff]
  refine ⟨by simp, by simp, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring⟩

theorem fusion_intertwine (h2 : (2 : F) ≠ 0) :
    fusion h2 * pairHom (-1, 1) = swap * fusion h2 := by
  apply Subtype.ext
  change fusionMatrix * pairMatrix (-1) 1 = swapMatrix * fusionMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fusionMatrix, pairMatrix, swapMatrix, mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two]

theorem swap_conjugate (h2 : (2 : F) ≠ 0) :
    IsConj (inclusion (F := F) (SemidirectProduct.inl (-1, 1)))
      (inclusion (SemidirectProduct.inr (.ofAdd 1))) := by
  rw [inclusion_inl, inclusion_inr, isConj_iff]
  exact ⟨fusion h2, by rw [fusion_intertwine, mul_inv_cancel_right]⟩

section Counting
variable {p : ℕ} [Fact p.Prime]

theorem card_range : Nat.card (inclusion (F := ZMod p)).range =
    (p * (p ^ 2 - 1)) ^ 2 * 2 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective inclusion_injective).toEquiv,
    SemidirectProduct.card, Nat.card_prod, Atlas.card_sl_two, Nat.card_zmod]
  simp [pow_two]

/-- The exact range index, in a form that avoids natural-number division. -/
theorem twice_index (hp : 3 < p) :
    (inclusion (F := ZMod p)).range.index * 2 = p ^ 2 * (p ^ 2 + 1) := by
  have hp0 : 0 < p := by omega
  have hp2 : 1 < p ^ 2 := by nlinarith
  have hp2pos : 0 < p ^ 2 - 1 := Nat.sub_pos_of_lt hp2
  have hfac : p ^ 4 - 1 = (p ^ 2 - 1) * (p ^ 2 + 1) := by
    have hs := Nat.sub_add_cancel (by omega : 1 ≤ p ^ 2)
    have ht := Nat.sub_add_cancel (show 1 ≤ p ^ 4 by nlinarith [sq_nonneg (p^2)])
    nlinarith
  have hc := (inclusion (F := ZMod p)).range.index_mul_card
  rw [card_range, Theory.SpecificGroups.SymplecticFour.card_sp, Nat.card_zmod, hfac] at hc
  apply Nat.eq_of_mul_eq_mul_right (show 0 < (p * (p ^ 2 - 1)) ^ 2 by positivity)
  calc
    (inclusion (F := ZMod p)).range.index * 2 * (p * (p ^ 2 - 1)) ^ 2 =
        (inclusion (F := ZMod p)).range.index * ((p * (p ^ 2 - 1)) ^ 2 * 2) := by ring
    _ = p ^ 4 * (p ^ 2 - 1) * ((p ^ 2 - 1) * (p ^ 2 + 1)) := hc
    _ = p ^ 2 * (p ^ 2 + 1) * (p * (p ^ 2 - 1)) ^ 2 := by ring

theorem index_eq (hp : 3 < p) :
    (inclusion (F := ZMod p)).range.index = p ^ 2 * (p ^ 2 + 1) / 2 := by
  have := twice_index hp
  omega

/-- The coordinate plane-pair subgroup contains a Sylow two-subgroup. -/
theorem odd_index (hp : 3 < p) : Odd (inclusion (F := ZMod p)).range.index := by
  have ho : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hm : p % 4 = 1 ∨ p % 4 = 3 := by rw [Nat.odd_iff] at ho; omega
  have hmod : (p ^ 2 * (p ^ 2 + 1)) % 4 = 2 := by
    rcases hm with hm | hm <;> norm_num [Nat.mul_mod, Nat.add_mod, Nat.pow_mod, hm]
  have hi := twice_index hp
  rw [← hi] at hmod
  rw [Nat.odd_iff]
  omega

end Counting

end PlaneGeometry

/-- The concrete unordered pair of coordinate symplectic planes, with its
swap and the ambient conjugacy needed by the central-cover argument. -/
@[expose] def planeModel {p : ℕ} [Fact p.Prime] (hp : 3 < p) : PlaneModel p where
  action := PlaneGeometry.action
  action_generator := PlaneGeometry.action_generator
  inclusion := PlaneGeometry.inclusion
  injective := PlaneGeometry.inclusion_injective
  odd_index := PlaneGeometry.odd_index hp
  swap_conjugate := PlaneGeometry.swap_conjugate (by
    intro h
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < p)
      ((ZMod.natCast_eq_zero_iff 2 p).mp h))

/-- The geometric input to `exists_section_on_plane_model`, without any
assumption on central covers or rank-one splitting. -/
theorem nonempty_planeModel {p : ℕ} [Fact p.Prime] (hp : 3 < p) :
    Nonempty (PlaneModel p) := ⟨planeModel hp⟩

section Five
local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- In particular the literal range has odd index 325 over the five-element field. -/
theorem planeModel_index_five : (planeModel (p := 5) (by decide)).inclusion.range.index = 325 := by
  change (PlaneGeometry.inclusion (F := ZMod 5)).range.index = 325
  rw [PlaneGeometry.index_eq (by decide : 3 < 5)]
  norm_num

end Five

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.TwoPrimary
end
