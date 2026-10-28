module

public import Theory.SpecificGroups.SymmetricFourWreath.Coordinates
public import Theory.ElementaryAbelian.Basic

/-!
# Four elementary subgroups in the dihedral wreath Sylow

Each square-dihedral factor has two elementary four-groups: the normal
Klein four in S₄ and the four-group containing the opposite transpositions.
Their four products give explicit elementary groups of order sixteen in
the marked Sylow. Exhaustion of the maximum-order family is a separate
geometric assertion.

Source: Aschbacher–Smith 13.9.2(1), printed p.969 (PDF p.986).
-/

@[expose] public section
namespace SymmetricFourWreath
open Subgroup

/-- `true` is the normal Klein four of S₄; `false` is the other square four-group. -/
def plane (b : Bool) : Subgroup D8 where
  carrier := {x | x = DihedralGroup.r 0 ∨ x = DihedralGroup.r 2 ∨
    x = DihedralGroup.sr (if b then 1 else 0) ∨
    x = DihedralGroup.sr (if b then 3 else 2)}
  one_mem' := by cases b <;> decide +kernel
  mul_mem' := by cases b <;> decide +kernel
  inv_mem' := by cases b <;> decide +kernel

instance plane_decidable (b : Bool) : DecidablePred (· ∈ plane b) := fun x =>
  inferInstanceAs (Decidable (x = DihedralGroup.r 0 ∨ x = DihedralGroup.r 2 ∨
    x = DihedralGroup.sr (if b then 1 else 0) ∨
    x = DihedralGroup.sr (if b then 3 else 2)))

instance plane_elementary (b : Bool) : IsElementaryAbelian 2 (plane b) where
  is_comm.comm := by cases b <;> decide +kernel
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    cases b <;> decide +kernel)

theorem card_plane (b : Bool) : Nat.card (plane b) = 4 := by
  rw [Nat.card_eq_fintype_card]
  cases b <;> decide +kernel

/-- The base direct product, with its ordered coordinates. -/
def pair : D8 × D8 →* P where
  toFun a := ⟨fun i => if i = 1 then a.1 else a.2, 1⟩
  map_one' := by ext <;> simp
  map_mul' a b := by
    apply RegularWreathProduct.ext
    · funext i
      by_cases hi : i = 1 <;> simp [hi]
    · rfl

theorem pair_injective : Function.Injective pair := by
  intro a b h
  apply Prod.ext
  · have := congrArg (fun w : P => w.left 1) h
    simpa [pair] using this
  · have := congrArg (fun w : P => w.left turn) h
    simpa [pair, turn_ne_one] using this

/-- The four products before embedding in S₄ wr C₂. -/
def elementaryInP (b c : Bool) : Subgroup P := ((plane b).prod (plane c)).map pair

/-- The actual four coordinate subgroups in the symmetric wreath product. -/
def elementary (b c : Bool) : Subgroup W := (elementaryInP b c).map sylowEmbedding

private instance plane_prod_elementary (b c : Bool) :
    IsElementaryAbelian 2 ((plane b).prod (plane c)) where
  is_comm.comm := by
    intro x y
    apply Subtype.ext
    exact Prod.ext
      (congrArg Subtype.val (IsMulCommutative.is_comm.comm
        (⟨x.1.1, x.2.1⟩ : plane b) ⟨y.1.1, y.2.1⟩))
      (congrArg Subtype.val (IsMulCommutative.is_comm.comm
        (⟨x.1.2, x.2.2⟩ : plane c) ⟨y.1.2, y.2.2⟩))
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro x
    apply Subtype.ext
    exact Prod.ext (elemPow_eq_one_of_isElementaryAbelian x.1.1 x.2.1)
      (elemPow_eq_one_of_isElementaryAbelian x.1.2 x.2.2))

instance elementaryInP_elementary (b c : Bool) : IsElementaryAbelian 2 (elementaryInP b c) :=
  IsElementaryAbelian.map pair

instance elementary_elementary (b c : Bool) : IsElementaryAbelian 2 (elementary b c) :=
  IsElementaryAbelian.map sylowEmbedding

theorem card_elementary (b c : Bool) : Nat.card (elementary b c) = 16 := by
  rw [elementary, Subgroup.card_map_of_injective sylowEmbedding_injective,
    elementaryInP, Subgroup.card_map_of_injective pair_injective,
    Nat.card_congr (Subgroup.prodEquiv (plane b) (plane c)).toEquiv, Nat.card_prod,
    card_plane, card_plane]

theorem elementary_le_standardSylow (b c : Bool) :
    elementary b c ≤ (standardSylow : Subgroup W) := Subgroup.map_le_range sylowEmbedding (elementaryInP b c)

/-- The candidate A, later identified with the literal two-core. -/
abbrev A : Subgroup W := elementary true true

/-- The second coordinate elementary subgroup (the source's B). -/
abbrev B : Subgroup W := elementary false false

/-- The dihedral base inside the original symmetric wreath product. -/
def J : Subgroup W := pair.range.map sylowEmbedding

end SymmetricFourWreath
