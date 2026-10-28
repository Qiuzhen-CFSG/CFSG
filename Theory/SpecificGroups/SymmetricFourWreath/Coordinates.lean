module

public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum

/-!
# Coordinates for the symmetric-four wreath product

The square action embeds D₈ into S₄. Applying this embedding in both base
coordinates embeds D₈ wr C₂ as a Sylow two-subgroup of S₄ wr C₂. The two
S₄ factor maps and the pure swapping involution remain explicit, so that
subgroups and elements can be transported with their markings.

Source: Aschbacher–Smith, setup for 13.9.2, printed p.969 (PDF p.986).
-/

@[expose] public section
namespace SymmetricFourWreath

abbrev C2 := Multiplicative (ZMod 2)
abbrev S4 := Equiv.Perm (Fin 4)
abbrev W := RegularWreathProduct S4 C2
abbrev D8 := DihedralGroup 4
abbrev P := RegularWreathProduct D8 C2

def turn : C2 := Multiplicative.ofAdd 1

theorem turn_ne_one : turn ≠ 1 := by decide
@[simp] theorem turn_sq : turn * turn = 1 := by decide
@[simp] theorem turn_inv : turn⁻¹ = turn := by decide

def squarePermutation : D8 → S4
  | .r i => finRotate 4 ^ i.val
  | .sr i => Equiv.swap 1 3 * finRotate 4 ^ i.val

def square : D8 →* S4 where
  toFun := squarePermutation
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem square_injective : Function.Injective square := by decide +kernel

/-- The coordinatewise square action on the dihedral wreath product. -/
def sylowEmbedding : P →* W where
  toFun x := ⟨fun i => square (x.left i), x.right⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp

theorem sylowEmbedding_injective : Function.Injective sylowEmbedding := by
  intro x y h
  apply RegularWreathProduct.ext
  · funext i
    apply square_injective
    exact congrArg (fun w : W => w.left i) h
  · exact congrArg (fun w : W => w.right) h

theorem card_P : Nat.card P = 128 := by
  rw [RegularWreathProduct.card, DihedralGroup.nat_card]
  norm_num [Nat.card_eq_fintype_card, C2]

theorem card_W : Nat.card W = 1152 := by
  rw [RegularWreathProduct.card]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial, C2, S4]

/-- A fixed Sylow subgroup, retaining its literal embedding in W. -/
noncomputable def standardSylow : Sylow 2 W := Sylow.ofCard sylowEmbedding.range (by
  rw [← Nat.card_congr (MonoidHom.ofInjective sylowEmbedding_injective).toEquiv,
    card_P, card_W]
  rw [show 1152 = 2 ^ 7 * 9 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 9)]
  norm_num)

@[simp] theorem standardSylow_coe :
    (standardSylow : Subgroup W) = sylowEmbedding.range := rfl

/-- The factor supported at coordinate i. -/
def factor (i : C2) : S4 →* W where
  toFun a := ⟨fun j => if j = i then a else 1, 1⟩
  map_one' := by ext <;> simp
  map_mul' a b := by
    apply RegularWreathProduct.ext
    · funext j
      by_cases h : j = i <;> simp [h]
    · rfl

theorem factor_injective (i : C2) : Function.Injective (factor i) := by
  intro a b h
  have := congrArg (fun w : W => w.left i) h
  simpa [factor] using this

def swap : W := RegularWreathProduct.inl turn

@[simp] theorem swap_sq : swap * swap = 1 := by
  change RegularWreathProduct.inl turn * RegularWreathProduct.inl turn = 1
  rw [← map_mul, turn_sq, map_one]

theorem swap_ne_one : swap ≠ 1 := by
  intro h
  exact turn_ne_one (congrArg RegularWreathProduct.right h)

/-- Conjugation by the pure swap interchanges the two actual factors. -/
theorem swap_factor (i : C2) (a : S4) :
    swap * factor i a * swap⁻¹ = factor (turn * i) a := by
  apply RegularWreathProduct.ext
  · funext j
    have h : turn * j = i ↔ j = turn * i := by
      rw [← turn_inv, inv_mul_eq_iff_eq_mul, turn_inv]
    simp [swap, factor, h]
  · simp [swap, factor]

/-- The two factors commute elementwise. -/
theorem factor_commute {i j : C2} (h : i ≠ j) (a b : S4) :
    Commute (factor i a) (factor j b) := by
  apply RegularWreathProduct.ext
  · funext k
    by_cases hi : k = i
    · subst k
      simp [factor, h]
    · by_cases hj : k = j
      · subst k; simp [factor, Ne.symm h]
      · simp [factor, hi, hj]
  · rfl

/-- The central involution in the first dihedral factor. -/
def t : W := factor 1 (square (DihedralGroup.r 2))

/-- The diagonal central involution. -/
def z : W := t * (swap * t * swap⁻¹)

theorem t_mem_standardSylow : t ∈ (standardSylow : Subgroup W) := by
  refine ⟨⟨fun i => if i = 1 then DihedralGroup.r 2 else 1, 1⟩, ?_⟩
  apply RegularWreathProduct.ext
  · funext i
    by_cases hi : i = 1 <;> simp [sylowEmbedding, t, factor, hi]
  · rfl

theorem swap_mem_standardSylow : swap ∈ (standardSylow : Subgroup W) := by
  refine ⟨RegularWreathProduct.inl turn, ?_⟩
  apply RegularWreathProduct.ext
  · funext i; simp [sylowEmbedding, swap]
  · rfl

theorem z_mem_standardSylow : z ∈ (standardSylow : Subgroup W) :=
  (standardSylow : Subgroup W).mul_mem t_mem_standardSylow
    ((standardSylow : Subgroup W).mul_mem
      ((standardSylow : Subgroup W).mul_mem swap_mem_standardSylow t_mem_standardSylow)
      ((standardSylow : Subgroup W).inv_mem swap_mem_standardSylow))

theorem t_sq : t * t = 1 := by
  rw [t, ← map_mul, ← map_mul]
  have h : DihedralGroup.r (2 : ZMod 4) * DihedralGroup.r 2 = 1 := by decide
  rw [h, map_one, map_one]

theorem t_ne_one : t ≠ 1 := by
  intro h
  have ht := (factor_injective 1) (h.trans (map_one (factor 1)).symm)
  have hr := square_injective (ht.trans (map_one square).symm)
  exact (by decide : DihedralGroup.r (2 : ZMod 4) ≠ 1) hr

end SymmetricFourWreath
