module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Basic
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TransvectionLifts
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup
import Mathlib.Tactic.Ring

/-!
# Ordered positive-root coordinates in every characteristic

The literal product x₆(b)x₀(k)x₄(w)x₂(v) parametrizes the standard unipotent
subgroup. Its multiplication law retains both the minus sign and the term
−2cw which disappear in characteristic two. The matrix entries prove
injectivity; the existing order q⁴ proves surjectivity. Over Fₚ this subgroup
has index prime to p, as required by central transfer.

Source: the type C₂ calculation for the multiplier in GLS3 §6.1, used with
Aschbacher–Smith A.2.2(2) and I.1.1–4, printed pp.33 and 407–408.
-/

@[expose] public section
noncomputable section
open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.DefiningPrime
variable {F : Type*} [Field F]

/-- Coordinates are root parameters, in the order 6, 0, 4, 2. -/
def element (b k w v : F) : unipotent (F := F) :=
  ⟨rootElement 6 b * rootElement 0 k * rootElement 4 w * rootElement 2 v,
    mul_mem (mul_mem (mul_mem (positive_root_mem_unipotent 6 b (by simp))
      (positive_root_mem_unipotent 0 k (by simp)))
      (positive_root_mem_unipotent 4 w (by simp)))
      (positive_root_mem_unipotent 2 v (by simp))⟩

theorem element_matrix (b k w v : F) :
    (element b k w v).val.val = fromBlocks !![1,b;0,1]
      !![k+b*w,w+b*v;w,v] 0 !![1,0;-b,1] := by
  change rootMatrix 6 b * rootMatrix 0 k * rootMatrix 4 w * rootMatrix 2 v = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.fromBlocks, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.single] <;> ring

theorem element_injective : Function.Injective (fun x : F × F × F × F =>
    element x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  rintro ⟨b,k,w,v⟩ ⟨c,l,t,a⟩ h
  have hh := congrArg (fun g : unipotent (F := F) => g.val.val) h
  rw [element_matrix, element_matrix] at hh
  have hb : b = c := congrArg (fun M => M (.inl 0) (.inl 1)) hh
  have hk : k+b*w = l+c*t := congrArg (fun M => M (.inl 0) (.inr 0)) hh
  have hw : w = t := congrArg (fun M => M (.inl 1) (.inr 0)) hh
  have hv : v = a := congrArg (fun M => M (.inl 1) (.inr 1)) hh
  subst c; subst t; subst a
  exact Prod.ext rfl (Prod.ext (add_right_cancel hk) rfl)

theorem element_surjective [Finite F] : Function.Surjective (fun x : F × F × F × F =>
    element x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr ⟨element_injective, ?_⟩ |>.surjective
  simp only [Nat.card_prod, card_unipotent]
  ring

theorem element_mul (b k w v c l t a : F) :
    element b k w v * element c l t a =
    element (b+c) (k+l-2*c*w+c^2*v) (w+t-c*v) (v+a) := by
  apply Subtype.ext
  apply Subtype.ext
  change (element b k w v).val.val * (element c l t a).val.val = _
  rw [element_matrix, element_matrix, element_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] <;> ring

theorem element_zero : element (0:F) 0 0 0 = 1 := by
  apply Subtype.ext
  simp [element, RootSubgroup.element_zero]

/-- The literal matrix unipotent subgroup has index prime to the defining prime. -/
theorem not_dvd_index_unipotent {p : ℕ} [Fact p.Prime] :
    ¬ p ∣ (unipotent (F := ZMod p)).index := by
  rw [index_unipotent, Nat.card_zmod]
  have hp := Fact.out (p := p.Prime)
  have hpow (k : ℕ) (hk : k ≠ 0) : ¬ p ∣ p^k - 1 := by
    intro h
    have hd := Nat.dvd_sub (dvd_pow_self p hk) h
    have hpos : 1 ≤ p^k := Nat.one_le_pow k p hp.pos
    have he : p^k - (p^k-1) = 1 := by omega
    rw [he] at hd
    exact hp.not_dvd_one hd
  exact fun h => (hp.dvd_mul.mp h).elim (hpow 2 (by decide)) (hpow 4 (by decide))

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.DefiningPrime
