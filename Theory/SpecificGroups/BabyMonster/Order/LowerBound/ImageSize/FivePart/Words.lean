module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.Reduction

/-!
# The ATLAS local five-subgroup program

This interprets the unchanged `source/BG1-max21W1` register program, keeping
one-based register indices and the source instruction order. Each instruction
preserves membership in any subgroup containing the inputs. No order or
structural identification of the output subgroup is asserted.

Source: ATLAS of Finite Group Representations,
https://brauer.maths.qmul.ac.uk/Atlas/v3/subgroup/BG1-max21W1.
See `../source/README.md` for attribution and the source hash.
-/

@[expose] public section
namespace BabyMonster.OrderLowerBound.FivePart

/-- The three instruction forms used by the source program. Powers have the
exponent first, as in the ATLAS `pwr` instruction. -/
inductive Instruction where
  | mul (left right target : ℕ)
  | inv (source target : ℕ)
  | pow (exponent source target : ℕ)
  deriving DecidableEq

variable {G : Type*} [Group G]

/-- Execute one instruction; all right-hand sides use the old registers. -/
def Instruction.step (op : Instruction) (r : ℕ → G) : ℕ → G :=
  match op with
  | .mul i j k => Function.update r k (r i * r j)
  | .inv i k => Function.update r k (r i)⁻¹
  | .pow n i k => Function.update r k (r i ^ n)

/-- Execute instructions in source order. -/
def run : List Instruction → (ℕ → G) → (ℕ → G)
  | [], r => r
  | op :: rest, r => run rest (op.step r)

/-- All registers remain in a subgroup containing their initial values. -/
theorem run_mem (H : Subgroup G) (ops : List Instruction) (r : ℕ → G)
    (hr : ∀ i, r i ∈ H) : ∀ i, run ops r i ∈ H := by
  induction ops generalizing r with
  | nil => exact hr
  | cons op rest ih =>
    apply ih
    intro i
    cases op <;> simp only [Instruction.step, Function.update_apply]
    · split <;> first | exact H.mul_mem (hr _) (hr _) | exact hr _
    · split <;> first | exact H.inv_mem (hr _) | exact hr _
    · split <;> first | exact H.pow_mem (hr _) _ | exact hr _

/-- The source program, transcribed without register renumbering. -/
def program : List Instruction := [
  .mul 1 2 3,
  .mul 3 2 4,
  .mul 3 3 5,
  .mul 5 5 3,
  .mul 3 4 12,
  .mul 12 12 3,
  .mul 12 3 4,
  .mul 4 4 5,
  .mul 5 5 3,
  .mul 3 3 10,
  .mul 1 10 3,
  .mul 3 3 11,
  .mul 11 12 3,
  .mul 3 12 4,
  .mul 3 3 5,
  .mul 4 3 6,
  .mul 5 6 7,
  .mul 7 7 8,
  .mul 7 8 9,
  .mul 8 9 13,
  .mul 3 4 5,
  .mul 5 5 6,
  .mul 12 6 7,
  .mul 7 7 8,
  .mul 8 8 9,
  .mul 4 6 7,
  .mul 7 5 3,
  .inv 3 4,
  .mul 4 9 5,
  .mul 5 3 14,
  .mul 13 14 3,
  .mul 3 14 4,
  .mul 4 14 5,
  .mul 5 14 6,
  .pow 3 4 15,
  .mul 5 5 4,
  .mul 3 3 5,
  .mul 5 4 7,
  .pow 5 7 4,
  .pow 20 6 5,
  .pow 6 3 6,
  .mul 5 6 3,
  .inv 3 5,
  .mul 5 4 6,
  .mul 6 3 16,
  .mul 15 16 3,
  .mul 3 16 4,
  .mul 3 4 5,
  .mul 3 5 6,
  .pow 6 6 7,
  .inv 15 8,
  .mul 7 8 9,
  .mul 7 15 6,
  .mul 9 6 5,
  .mul 5 5 6,
  .mul 15 6 17,
  .inv 16 8,
  .mul 7 8 9,
  .pow 3 7 5,
  .mul 5 16 6,
  .mul 9 6 5,
  .mul 5 5 6,
  .mul 16 6 18,
  .mul 17 18 3,
  .mul 3 18 4,
  .mul 3 4 5,
  .mul 3 5 6,
  .pow 15 6 7,
  .mul 7 10 19,
  .mul 1 19 3,
  .pow 17 3 20,
  .pow 6 6 21,
  .mul 20 21 3,
  .pow 4 3 4,
  .inv 4 5,
  .mul 21 5 6,
  .mul 21 4 7,
  .mul 6 7 8,
  .mul 8 8 7,
  .mul 4 7 5,
  .inv 5 4,
  .mul 21 4 6,
  .mul 21 5 7,
  .mul 6 7 8,
  .mul 8 8 7,
  .mul 5 7 1,
  .mul 17 18 2
]

/-- Inputs in registers 1 and 2; unused registers initially contain one. -/
def initial (a b : G) : ℕ → G :=
  fun i => if i = 1 then a else if i = 2 then b else 1

/-- The two output registers of `BG1-max21W1`. -/
def generators (a b : G) (i : Fin 2) : G :=
  run program (initial a b) (i.val + 1)

/-- Word membership, independent of all concrete matrix calculations. -/
theorem generators_mem (H : Subgroup G) (a b : G) (ha : a ∈ H) (hb : b ∈ H)
    (i : Fin 2) : generators a b i ∈ H := by
  apply run_mem
  intro j
  simp only [initial]
  split
  · exact ha
  · split
    · exact hb
    · exact H.one_mem

/-- The actual subgroup obtained by evaluating the source program. -/
def image (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1) : Subgroup MatrixGroup :=
  Subgroup.closure (Set.range (generators (standardA ha) (standardB hb)))

/-- The candidate local subgroup is contained in the fixed standard image. -/
theorem image_le_standardImage (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1) :
    image ha hb ≤ standardImage ha hb := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  apply generators_mem
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

/-- Lagrange transfers any certified local divisor to the standard image. -/
theorem image_card_dvd_standardImage (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1) :
    Nat.card (image ha hb) ∣ Nat.card (standardImage ha hb) :=
  Subgroup.card_dvd_of_le (image_le_standardImage ha hb)

end BabyMonster.OrderLowerBound.FivePart
