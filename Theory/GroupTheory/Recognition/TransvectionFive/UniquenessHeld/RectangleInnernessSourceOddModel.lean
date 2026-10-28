module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.Action
public import Mathlib.Data.ZMod.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.FinCases

/-! Two commuting cubic actors on the actual Held six-bit rectangle. Their
restrictions to the common sixteen are the two independent binary tensor
rotations. The second actor retains the necessary central shifts on the
remaining two coordinates. -/

public section
namespace Theory.GroupTheory.TransvectionFive.UniquenessHeld.RectangleSourceOdd
open UniquenessLinear.PlaneCensus (Code)
open UniquenessMathieu.SourceNormalizer

abbrev Coordinates := ZMod 3 × ZMod 3
abbrev OddGroup := Multiplicative Coordinates

@[expose] def bits (v : Fin 6 → Code) (x : Code) : Code :=
  (if x.getLsbD 0 then v 0 else 0) ^^^ (if x.getLsbD 1 then v 1 else 0) ^^^
  (if x.getLsbD 2 then v 2 else 0) ^^^ (if x.getLsbD 3 then v 3 else 0) ^^^
  (if x.getLsbD 4 then v 4 else 0) ^^^ (if x.getLsbD 5 then v 5 else 0)

/-- The first tensor rotation, acting on both rows. -/
@[expose] def row (x : Code) : Code := bits ![8,16,32,9,18,36] x

/-- The second tensor rotation, with its actual Held central shifts. -/
@[expose] def column (x : Code) : Code := bits ![17,4,6,26,32,48] x

/-- The original common sixteen inside the six-bit rectangle. -/
@[expose] def common (x : Code) : Prop := x &&& 9 = 0
instance commonDecidable : DecidablePred common := fun _ => inferInstanceAs (Decidable (_ = _))

/-- The nine actual additive transformations. -/
@[expose] def act (a : Coordinates) (x : Code) : Code :=
  row^[a.1.val] (column^[a.2.val] x)

private theorem act_zero : ∀ x : Code, act 0 x = x := by decide
private theorem act_add : ∀ a b : Coordinates, ∀ x : Code,
    act (a+b) x = act a (act b x) := by decide
private theorem act_xor : ∀ a : Coordinates, ∀ x y : Code,
    act a (x ^^^ y) = act a x ^^^ act a y := by decide
private theorem act_exceptional : ∀ a : Coordinates, ∀ x : Code,
    Sextet.exceptional (act a x) = Sextet.exceptional x := by decide

/-- The two cubic factors embedded in the literal exceptional symmetry group. -/
def representation : OddGroup →* Sextet.symmetryGroup where
  toFun a := ⟨{
    toFun := act a.toAdd
    invFun := act (-a.toAdd)
    left_inv x := by rw [← act_add, neg_add_cancel, act_zero]
    right_inv x := by rw [← act_add, add_neg_cancel, act_zero]
  }, (Sextet.mem_symmetryGroup _).mpr ⟨act_xor _, act_exceptional _⟩⟩
  map_one' := Subtype.ext (Equiv.ext act_zero)
  map_mul' a b := Subtype.ext (Equiv.ext (act_add a.toAdd b.toAdd))

theorem representation_apply (a : OddGroup) (x : Code) :
    (representation a).val x = act a.toAdd x := rfl

/-- The action on the original common sixteen is faithful. -/
theorem faithful_common (a : Coordinates) (h : ∀ x : Code, common x → act a x = x) :
    a = 0 := by
  have cert : ∀ a : Coordinates, act a 2 = 2 → act a 4 = 4 →
      act a 16 = 16 → act a 32 = 32 → a = 0 := by decide
  exact cert a (h 2 (by decide)) (h 4 (by decide))
    (h 16 (by decide)) (h 32 (by decide))

theorem representation_injective : Function.Injective representation := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply Subgroup.eq_bot_iff.mpr
  intro a ha
  apply Subgroup.mem_bot.mpr
  apply Multiplicative.toAdd_injective
  apply faithful_common
  intro x _
  have h := congrArg (fun f : Sextet.symmetryGroup => f.val x) ha
  exact h

/-- Every actor preserves the actual common sixteen. -/
theorem act_common : ∀ a : Coordinates, ∀ x : Code, common (act a x) ↔ common x := by decide

/-- No nonidentity common-kernel element is fixed by the two cubic factors. -/
theorem common_fixed (x : Code) (hx : common x)
    (h : ∀ a : Coordinates, act a x = x) : x = 0 := by
  have cert : ∀ x : Code, common x → act (1,0) x = x → x = 0 := by decide
  exact cert x hx (h (1,0))

/-- The constructed subgroup really has order nine. -/
theorem oddGroup_card : Nat.card OddGroup = 9 := by
  simp [OddGroup, Coordinates, Nat.card_prod]

end Theory.GroupTheory.TransvectionFive.UniquenessHeld.RectangleSourceOdd
