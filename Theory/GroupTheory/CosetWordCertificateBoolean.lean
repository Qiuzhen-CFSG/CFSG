module

public import Theory.GroupTheory.CosetWordCertificate

/-!
# Boolean evaluation of the six-rule coset-word checker

Fieldwise Boolean equality avoids constructing decidable-equality proof trees
while evaluating a certificate. `checkBool_iff` proves that this checker accepts
exactly the same deductions as `CosetWordCertificate.check`. The chunk soundness
theorem therefore reuses the original witness-producing calculus unchanged.

Source: the Todd–Coxeter certificate calculus in `CosetWordCertificate`.
-/

@[expose] public section
namespace Subgroup.CosetWordCertificate

def factBEq {α : Type*} [BEq α] (f k : FactData α) : Bool :=
  f.left == k.left && f.word == k.word && f.right == k.right

def checkBool {α : Type*} [BEq α] [DecidableEq α] (C : Context α)
    (fs : Nat → FactData α) (n : Nat) (op : Instruction α) (out : FactData α) : Bool :=
  match op with
  | .refl i => factBEq out ⟨i, [], i⟩
  | .defining j => (!(j == 0)) && factBEq out ⟨C.parent j, [C.letter j], j⟩
  | .subgroup a => C.allowed a && factBEq out ⟨0, [a], 0⟩
  | .relator i r => factBEq out ⟨i, C.relator r, i⟩
  | .reverse p => Nat.blt p n &&
      factBEq out ⟨(fs p).right, FreeGroup.invRev (fs p).word, (fs p).left⟩
  | .compose p q => Nat.blt p n && Nat.blt q n && ((fs p).right == (fs q).left) &&
      factBEq out ⟨(fs p).left, reduce ((fs p).word ++ (fs q).word), (fs q).right⟩

def checkBoolChunk {α : Type*} [BEq α] [DecidableEq α] (C : Context α)
    (fs : Nat → FactData α) (ops : Nat → Instruction α) (start count : Nat) : Bool :=
  (List.range count).all fun k => checkBool C fs (start+k) (ops (start+k)) (fs (start+k))

theorem factBEq_eq_true_iff {α : Type*} [BEq α] [LawfulBEq α] (f k : FactData α) :
    factBEq f k = true ↔ f = k := by
  cases f
  cases k
  simp [factBEq, beq_iff_eq, and_assoc]

theorem checkBool_iff {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    (C : Context α) (fs : Nat → FactData α) (n : Nat)
    (op : Instruction α) (out : FactData α) :
    checkBool C fs n op out = true ↔ check C fs n op out = true := by
  cases op <;> simp [checkBool, check, factBEq_eq_true_iff, beq_iff_eq, and_assoc]

theorem checkBoolChunk_checked {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    (C : Context α) (fs : Nat → FactData α) (ops : Nat → Instruction α)
    (start count : Nat) (h : checkBoolChunk C fs ops start count = true) :
    checkChunk C fs ops start count = true := by
  apply List.all_eq_true.mpr
  intro k hk
  exact (checkBool_iff C fs _ _ _).mp (List.all_eq_true.mp h k hk)

theorem checkBoolChunk_sound {G α : Type*} [Group G] [BEq α] [LawfulBEq α] [DecidableEq α]
    {C : Context α} {H : Subgroup G} {g : α → G} {ρ : Nat → G}
    (valid : Valid C H g ρ) (fs : Nat → FactData α) (ops : Nat → Instruction α)
    (start count : Nat) (prior : ∀ n, n < start → Holds H g ρ (fs n))
    (checked : checkBoolChunk C fs ops start count = true) :
    ∀ n, n < start + count → Holds H g ρ (fs n) :=
  checkChunk_sound valid fs ops start count prior (checkBoolChunk_checked C fs ops start count checked)

end Subgroup.CosetWordCertificate
