module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# A concrete quaternion–dihedral central product

The 32 elements are a quaternion coordinate and two binary coordinates. The
binary coordinates represent two dihedral reflections, whose commutator is the
central quaternion involution. Multiplication inserts that involution when the
second reflection passes the first. All group laws and factor calculations are
checked by reduction on these finite coordinates.

The quaternion and dihedral embeddings commute, generate the model, and meet
precisely in their common central involution. These explicit interfaces support
recognition of the minus-type extraspecial group and finite automorphism tables.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed pp.389–390,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

@[expose] public section

namespace MinusExtraspecial
@[ext] structure Model where
  q : QuaternionGroup 2
  r : Bool
  s : Bool
  deriving DecidableEq, Fintype

def z : QuaternionGroup 2 := .a 2
instance : One Model := ⟨⟨1, false, false⟩⟩
instance : Mul Model := ⟨fun a b =>
  ⟨a.q * b.q * (if a.s && b.r then z else 1), a.r ^^ b.r, a.s ^^ b.s⟩⟩
instance : Inv Model := ⟨fun a =>
  ⟨a.q⁻¹ * (if a.s && a.r then z else 1), a.r, a.s⟩⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
instance : Group Model where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide

def quaternion : QuaternionGroup 2 →* Model where
  toFun q := ⟨q, false, false⟩
  map_one' := rfl
  map_mul' := by decide

def rotation : Model := ⟨1, true, true⟩
def reflection : Model := ⟨1, false, true⟩
def dihedral : DihedralGroup 4 →* Model where
  toFun
    | .r i => rotation ^ i.val
    | .sr i => reflection * rotation ^ i.val
  map_one' := rfl
  map_mul' := by decide

theorem fintype_card_model : Fintype.card Model = 32 := by decide

theorem card_model : Nat.card Model = 32 := by
  rw [Nat.card_eq_fintype_card, fintype_card_model]
theorem quaternion_injective : Function.Injective quaternion := by decide
theorem dihedral_injective : Function.Injective dihedral := by decide
theorem factors_commute (q : QuaternionGroup 2) (d : DihedralGroup 4) :
    Commute (quaternion q) (dihedral d) :=
  (show ∀ q d, quaternion q * dihedral d = dihedral d * quaternion q from by decide) q d
theorem factors_generate : ∀ x : Model, ∃ q d, quaternion q * dihedral d = x := by decide
theorem factors_overlap : ∀ q d, quaternion q = dihedral d ↔
    (q = 1 ∧ d = 1) ∨ (q = .a 2 ∧ d = .r 2) := by decide
/-- Four generators used to encode an automorphism by its images. -/
def generators : Fin 4 → Model
  | 0 => quaternion (.a 1)
  | 1 => quaternion (.xa 0)
  | 2 => ⟨1, true, false⟩
  | 3 => ⟨1, false, true⟩

/-- Evaluate the canonical coordinate word at four prescribed images. -/
def word (v : Fin 4 → Model) (x : Model) : Model :=
  (match x.q with
    | .a i => v 0 ^ i.val
    | .xa i => v 1 * v 0 ^ i.val) *
    (if x.r then v 2 else 1) * (if x.s then v 3 else 1)

theorem word_generators : ∀ x : Model, word generators x = x := by decide

/-- Automorphisms are determined by the images of the four generators. -/
theorem aut_word (a : MulAut Model) (x : Model) :
    word (fun i => a (generators i)) x = a x := by
  conv_rhs => rw [← word_generators x]
  unfold word
  rw [map_mul, map_mul]
  congr 2
  · cases x.q <;> simp only [map_mul, map_pow]
  · cases x.r <;> simp only [Bool.false_eq_true, ↓reduceIte, map_one]
  · cases x.s <;> simp only [Bool.false_eq_true, ↓reduceIte, map_one]

end MinusExtraspecial
