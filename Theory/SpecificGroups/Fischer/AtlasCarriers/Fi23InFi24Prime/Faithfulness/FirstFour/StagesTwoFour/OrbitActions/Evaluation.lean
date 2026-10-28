module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.OrbitActions.ChecksFirst
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.OrbitActions.Witnesses
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Checks
/-!
# Short evaluations for the literal inverse-action comparisons

Write each requested generator as `u * v⁻¹`. A common preimage `z` with
`u z = x` and `v z = y` proves that the inverse generator sends `x` to `y`.
The first pair uses the certified intermediate actions of words 5 and 8;
the second uses the first orbit table and its checked inverse columns.
All word decompositions are proved against the original `Word` definitions.
Source: ATLAS F24G1-p306936B0, GLS3 Table 5.3v, and the retained word program.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.OrbitActions

def pair (i : Fin 2) (a : Fin 2) : Ambient :=
  if i = 0 then if a = 0 then Word.word5 aPerm bPerm else Word.word8 aPerm bPerm
  else gen 0 a

def numerator (i a : Fin 2) : List (Fin 2) :=
  if i = 0 then
    if a = 0 then [1,0,0,1,1,0,1,0,0,1,0,1,0,1,0,0]
    else [1,1,0,1,0,0,0,1,1,0,0,0,1]
  else
    if a = 0 then [0,1,1,1,0,0,1,0,1,1,0,0,0,0]
    else [0,1,0,1,0,0,1,0,1,1,0,0,0]

def denominator (i a : Fin 2) : List (Fin 2) :=
  if i = 0 then
    if a = 0 then [1,0,0,0,0,0,0,0,1,1,0,1,1,0,1]
    else [0,1,1,1,1,1,0,0,1,0,1,1,0]
  else
    if a = 0 then [0,1,0,1,1,0,1]
    else [1,1,0,1,1,1,0,1,1,1,0,1]

def product (i : Fin 2) (w : List (Fin 2)) : Ambient := (w.map (pair i)).prod

private theorem gen00 : gen 0 0 = Word.word11 aPerm bPerm := rfl
private theorem gen01 : gen 0 1 = Word.word14 aPerm bPerm := rfl
private theorem gen10 : gen 1 0 = Word.word17 aPerm bPerm := rfl
private theorem gen11 : gen 1 1 = Word.word20 aPerm bPerm := rfl

private theorem gen_formula (i a : Fin 2) :
    gen i a = product i (numerator i a) * (product i (denominator i a))⁻¹ := by
  fin_cases i <;> fin_cases a <;>
    simp [numerator, denominator, product, pair, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, ↓reduceIte, gen00, gen01, gen10, gen11,
      Word.word11, Word.word14, Word.word17, Word.word20, Word.word9, Word.word10,
      Word.word12, Word.word13, Word.word15, Word.word16, Word.word18, Word.word19,
      mul_assoc]

def run {I : Type} (f : Fin 2 → I → I) : List (Fin 2) → I → I
  | [], j => j
  | a :: w, j => f a (run f w j)

private theorem product_action {I : Type} (i : Fin 2) (f : Fin 2 → I → I)
    (L : I → Fin 306936) (h : ∀ a j, pair i a (L j) = L (f a j))
    (w : List (Fin 2)) (j : I) : product i w (L j) = L (run f w j) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simpa only [product, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, run]
      using (congrArg (pair i a) ih).trans (h a (run f w j))

private theorem inverse_of_common_preimage (p q : Ambient) (z x y : Fin 306936)
    (hp : p z = x) (hq : q z = y) : (p * q⁻¹)⁻¹ x = y := by
  rw [mul_inv_rev, inv_inv, Equiv.Perm.mul_apply, ← hp]
  exact (congrArg q (p.symm_apply_apply z)).trans hq

def firstStep (a : Fin 2) : Index → Index := ix (if a = 0 then Data.t30 else Data.t32)

private theorem firstStep_action (a : Fin 2) (j : Index) : pair 0 a (lab j) = lab (firstStep a j) := by
  fin_cases a
  · change Word.word5 aPerm bPerm (lab j) = lab (ix Data.t30 j)
    have h := support30 j
    rw [word5_eq] at h
    exact h
  · change Word.word8 aPerm bPerm (lab j) = lab (ix Data.t32 j)
    have h := support32 j
    rw [word8_eq] at h
    exact h

def commonFirst (a : Fin 2) (j : Fin (size 0)) : Index :=
  ⟨(if a = 0 then Data.common00 else Data.common01) j.val % 31671,
    Nat.mod_lt _ (by decide)⟩

def firstTest (a : Fin 2) (n : Nat) : Bool :=
  let j : Fin (size 0) := ⟨n % size 0, Nat.mod_lt _ (size_pos 0)⟩
  decide (lab (run firstStep (numerator 0 a) (commonFirst a j)) = label 0 j ∧
    lab (run firstStep (denominator 0 a) (commonFirst a j)) = label 0 (next 0 a j))

theorem first_inverse_of_check (a : Fin 2)
    (hc : ∀ j : Fin (size 0), firstTest a j.val = true) (j : Fin (size 0)) :
    (gen 0 a)⁻¹ (label 0 j) = label 0 (next 0 a j) := by
  have h := hc j
  simp only [firstTest, Nat.mod_eq_of_lt j.isLt, Fin.eta, decide_eq_true_eq] at h
  rw [gen_formula]
  exact inverse_of_common_preimage _ _ (lab (commonFirst a j)) _ _
    ((product_action 0 firstStep lab firstStep_action _ _).trans h.1)
    ((product_action 0 firstStep lab firstStep_action _ _).trans h.2)

def secondStep (a : Fin 2) : Fin (size 0) → Fin (size 0) := prev 0 a

private theorem secondStep_action (ha : ∀ a j, (gen 0 a)⁻¹ (label 0 j) = label 0 (next 0 a j))
    (a : Fin 2) (j : Fin (size 0)) : pair 1 a (label 0 j) = label 0 (secondStep a j) := by
  change gen 0 a (label 0 j) = label 0 (prev 0 a j)
  have h := congrArg (gen 0 a) (ha a (prev 0 a j))
  simpa only [next_prev, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using h.symm

def commonSecond (a : Fin 2) (j : Fin (size 1)) : Fin (size 0) :=
  ⟨(if a = 0 then Data.common10 else Data.common11) j.val % size 0,
    Nat.mod_lt _ (size_pos 0)⟩

def inclusion (j : Fin (size 1)) : Fin (size 0) :=
  ⟨Data.inclusion j.val % size 0, Nat.mod_lt _ (size_pos 0)⟩

def inclusionTest (n : Nat) : Bool :=
  let j : Fin (size 1) := ⟨n % size 1, Nat.mod_lt _ (size_pos 1)⟩
  decide (label 0 (inclusion j) = label 1 j)

def secondTest (a : Fin 2) (n : Nat) : Bool :=
  let j : Fin (size 1) := ⟨n % size 1, Nat.mod_lt _ (size_pos 1)⟩
  decide (run secondStep (numerator 1 a) (commonSecond a j) = inclusion j ∧
    run secondStep (denominator 1 a) (commonSecond a j) = inclusion (next 1 a j))

theorem second_inverse_of_check
    (hl : ∀ j, label 0 (inclusion j) = label 1 j)
    (ha : ∀ a j, (gen 0 a)⁻¹ (label 0 j) = label 0 (next 0 a j))
    (a : Fin 2) (hc : ∀ j : Fin (size 1), secondTest a j.val = true) (j : Fin (size 1)) :
    (gen 1 a)⁻¹ (label 1 j) = label 1 (next 1 a j) := by
  have h := hc j
  simp only [secondTest, Nat.mod_eq_of_lt j.isLt, Fin.eta, decide_eq_true_eq] at h
  rw [gen_formula]
  exact inverse_of_common_preimage _ _ (label 0 (commonSecond a j)) _ _
    ((product_action 1 secondStep (label 0) (secondStep_action ha) _ _).trans
      ((congrArg (label 0) h.1).trans (hl j)))
    ((product_action 1 secondStep (label 0) (secondStep_action ha) _ _).trans
      ((congrArg (label 0) h.2).trans (hl (next 1 a j))))

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.OrbitActions
