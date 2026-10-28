module

public import Theory.Character.PermutationActionCharacter
public import Theory.Character.ScalarProductMultiplicity
public import Theory.Character.AlternatingSix.Rational.NormOne
public import Theory.Character.Inflation
public import Theory.Character.AbelianLinearCharacters
public import Theory.Character.Generalized
public import Mathlib.GroupTheory.Perm.Sign

/-!
# The four quadratic rows of the equal-sign subgroup of S₃ × S₃

Each of the four linear forms on the elementary-nine subgroup extends to
a surjection onto S₃. Pulling back its permutation character minus one
constructs four genuine irreducible characters of degree two. All finite
calculations below concern this order-eighteen quotient.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.LocalCharactersModel

abbrev S3 := Equiv.Perm (Fin 3)

def equalSign : Subgroup (S3 × S3) where
  carrier := {p | Equiv.Perm.sign p.1 = Equiv.Perm.sign p.2}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    change Equiv.Perm.sign (a.1 * b.1) = Equiv.Perm.sign (a.2 * b.2)
    rw [map_mul, map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    change Equiv.Perm.sign a.1⁻¹ = Equiv.Perm.sign a.2⁻¹
    rw [map_inv, map_inv, ha]

abbrev D := equalSign

local instance : DecidablePred (· ∈ equalSign) := fun _ => inferInstanceAs (Decidable (_ = _))
local instance modelFintype : Fintype D := Subtype.fintype _

def reflection (d : D) : S3 :=
  if Equiv.Perm.sign d.val.1 = 1 then 1 else Equiv.swap 0 1

def slope (i : Fin 4) (d : D) : S3 :=
  ![d.val.1, d.val.2, d.val.1 * reflection d * d.val.2,
    d.val.1 * d.val.2⁻¹ * reflection d] i

theorem slope_one : ∀ i : Fin 4, slope i 1 = 1 := by decide +kernel

theorem slope_mul : ∀ (i : Fin 4) (a b : D),
    slope i (a * b) = slope i a * slope i b := by decide +kernel

def quotient (i : Fin 4) : D →* S3 where
  toFun := slope i
  map_one' := slope_one i
  map_mul' := slope_mul i

def rowValue (i : Fin 4) (d : D) : ℤ :=
  (Finset.univ.filter (fun x : Fin 3 => slope i d x = x)).card - (1 : ℤ)

def row (i : Fin 4) : ClassFunction D := fun d => (rowValue i d : ℂ)

theorem card : Nat.card D = 18 := by rw [Nat.card_eq_fintype_card]; decide +kernel

theorem row_one (i : Fin 4) : row i 1 = 2 := by
  have h : ∀ i : Fin 4, rowValue i 1 = 2 := by decide +kernel
  simp only [row, h, Int.cast_ofNat]

private theorem square_sum : ∀ i : Fin 4, ∑ d : D, rowValue i d * rowValue i d = 18 := by
  decide +kernel

theorem row_norm (i : Fin 4) : @scalarProduct D (Fintype.ofFinite D) (row i) (row i) = 1 := by
  rw [Subsingleton.elim (Fintype.ofFinite D) modelFintype]
  unfold scalarProduct
  simp only [row, star_intCast, ← Int.cast_mul, ← Int.cast_sum, square_sum, card]
  norm_num

def permRep (i : Fin 4) : Representation ℂ D (Fin 3 → ℂ) :=
  (Representation.permutationAction S3 (Fin 3)).comp (quotient i)

private theorem row_permutation (i : Fin 4) :
    row i = (permRep i).character - 1 := by
  ext d
  change (rowValue i d : ℂ) =
    (Representation.permutationAction S3 (Fin 3)).character (quotient i d) - 1
  rw [Representation.permutationAction_character]
  simp only [rowValue, Int.cast_sub, Int.cast_natCast, Int.cast_one,
    Nat.card_eq_fintype_card, Fintype.card_subtype, MulAction.fixedBy,
    quotient, MonoidHom.coe_mk, OneHom.coe_mk]
  rfl

theorem row_generalized (i : Fin 4) : IsGeneralizedCharacter (row i) := by
  rw [row_permutation]
  exact (show IsCharacter
    (permRep i).character from ⟨3, permRep i, rfl⟩).sub_one_isGeneralized

theorem row_irreducible (i : Fin 4) : IsIrreducibleCharacter (row i) :=
  (row_generalized i).irreducible_of_norm_one (row_norm i)
    (by rw [row_one]; norm_num)

theorem row_injective : Function.Injective row := by
  have h : ∀ i j : Fin 4, (∀ d : D, rowValue i d = rowValue j d) → i = j := by
    decide +kernel
  intro i j hij
  apply h i j
  intro d
  have hh : (rowValue i d : ℂ) = (rowValue j d : ℂ) := congrFun hij d
  exact_mod_cast hh

theorem row_equal_of_three_regular (i j : Fin 4) (d : D)
    (hd : ¬ 3 ∣ orderOf d) : row i d = row j d := by
  have h : ∀ (i j : Fin 4) (d : D), rowValue i d ≠ rowValue j d → d ^ 3 = 1 ∧ d ≠ 1 := by
    decide +kernel
  by_contra hn
  have hv : rowValue i d ≠ rowValue j d := fun he => hn (congrArg (fun z : ℤ => (z : ℂ)) he)
  obtain ⟨hp, hne⟩ := h i j d hv
  exact hd (by rw [orderOf_eq_prime hp hne])

def signValue (d : D) : ℤ := (Equiv.Perm.sign d.val.1 : ℤ)

def signRow : D →* ℂ where
  toFun d := (signValue d : ℂ)
  map_one' := by simp [signValue]
  map_mul' a b := by simp [signValue, map_mul, Int.cast_mul]

theorem signRow_linear : IsLinearCharacter (signRow : D → ℂ) := signRow.isLinearCharacter

def alphaValue (i : Fin 4) (d : D) : ℤ := 1 + signValue d - rowValue i d

def alpha (i : Fin 4) : ClassFunction D := fun d => (alphaValue i d : ℂ)

theorem alpha_eq (i : Fin 4) : alpha i = 1 + (signRow : D → ℂ) - row i := by
  ext d
  simp [alpha, alphaValue, signRow, row]

theorem alpha_generalized (i : Fin 4) : IsGeneralizedCharacter (alpha i) := by
  rw [alpha_eq]
  obtain ⟨n, ρ, _, hρ⟩ := signRow_linear.1
  exact (isCharacter_one.add ⟨n, ρ, hρ⟩).isGeneralized.sub (row_generalized i)

theorem alpha_one (i : Fin 4) : alpha i 1 = 0 := by
  simp only [alpha_eq, Pi.sub_apply, Pi.add_apply, Pi.one_apply, map_one, row_one]
  norm_num

theorem alpha_three_regular (i : Fin 4) (d : D) (hd : ¬ 3 ∣ orderOf d) : alpha i d = 0 := by
  have h : ∀ (i : Fin 4) (d : D), alphaValue i d ≠ 0 → d ^ 3 = 1 ∧ d ≠ 1 := by
    decide +kernel
  have hz : alphaValue i d = 0 := by
    by_contra hn
    obtain ⟨hp, hne⟩ := h i d hn
    exact hd (by rw [orderOf_eq_prime hp hne])
  simp [alpha, hz]

theorem alpha_inner (i j : Fin 4) :
    @scalarProduct D (Fintype.ofFinite D) (alpha i) (alpha j) = 2 + if i = j then 1 else 0 := by
  rw [Subsingleton.elim (Fintype.ofFinite D) modelFintype]
  have h : ∀ i j : Fin 4, ∑ d : D, alphaValue i d * alphaValue j d =
      18 * (2 + if i = j then 1 else 0) := by decide +kernel
  unfold scalarProduct
  simp only [alpha, star_intCast, ← Int.cast_mul, ← Int.cast_sum, h, card]
  split_ifs <;> norm_num

theorem alpha_principal (i : Fin 4) :
    @scalarProduct D (Fintype.ofFinite D) (alpha i) 1 = 1 := by
  rw [Subsingleton.elim (Fintype.ofFinite D) modelFintype]
  have h : ∀ i : Fin 4, ∑ d : D, alphaValue i d = 18 := by decide +kernel
  unfold scalarProduct
  simp only [alpha, Pi.one_apply, star_one, mul_one, ← Int.cast_sum, h, card]
  norm_num

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.LocalCharactersModel
