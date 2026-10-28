module
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryContracts
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd.Reflection
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryImages
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic.FinCases
/-!
# The ninth marked relation in a central covering image

This replays the exact word-equality graph from `RelatorLifts/Odd/Consequences`
for an arbitrary family of involutions, including a common central twist of
the marked image. The mapped specialization uses the original four even
equations and seventh equation as its input words; `BinaryOdd.Reflection` supplies the eighth and the reflected even
equations. Thus all uses of reflection have the literal covering compatibility.

The equation graph and its integer words are unchanged. The generic list
lemmas justify splits, overlaps and contextual replacements in the image.
Source: John Bray's `Held/Model/Source/HeG1-P1.M`, the frozen marked words in
`M1Restriction/Data.lean`, and the checked source graph in
`RelatorLifts/Odd/Consequences.lean`.
-/

public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd.MappedConsequences
/-- An arbitrary family of involutions, allowing a common central twist. -/
structure InvolutionFamily (E : Type*) [Group E] where
  val : ℤ → E
  inv_eq : ∀ n, (val n)⁻¹ = val n

variable {E : Type*} [Group E] {φ : InvolutionFamily E}
@[expose] def value (φ : InvolutionFamily E) (w : List ℤ) : E :=
  (w.map φ.val).prod
private theorem value_append (u v : List ℤ) : value φ (u ++ v) = value φ u * value φ v := by
  simp only [value, List.map_append, List.prod_append]

private theorem conjugate_inv (n : ℤ) : (φ.val n)⁻¹ = φ.val n := φ.inv_eq n

private theorem value_reverse (w : List ℤ) : value φ w.reverse = (value φ w)⁻¹ := by
  induction w with
  | nil => simp [value]
  | cons a w ih =>
    rw [List.reverse_cons, value_append, ih]
    simp only [value, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, mul_inv_rev, conjugate_inv]

private theorem relation_split (w : List ℤ) (hw : value φ w = 1)
    (flip : Bool) (offset : Nat) (l r : List ℤ)
    (hs : (if flip then w.reverse else w).rotate offset = l ++ r.reverse) :
    value φ l = value φ r := by
  have h : value φ (if flip then w.reverse else w) = 1 := by
    cases flip <;> simp only [Bool.false_eq_true, ↓reduceIte, value_reverse, hw, inv_one]
  have he : value φ ((if flip then w.reverse else w).rotate offset) = 1 := by
    simpa only [value, List.map_rotate] using
      List.prod_rotate_eq_one_of_prod_eq_one h offset
  rw [hs, value_append, value_reverse, mul_inv_eq_one] at he
  exact he

private theorem in_context {l r : List ℤ} (h : value φ l = value φ r)
    (pre post : List ℤ) : value φ (pre ++ l ++ post) = value φ (pre ++ r ++ post) := by
  simp only [value_append, h]

private theorem overlap {l₁ r₁ l₂ r₂ : List ℤ}
    (h₁ : value φ l₁ = value φ r₁) (h₂ : value φ l₂ = value φ r₂)
    (pre post : List ℤ) (hc : l₁ ++ post = pre ++ l₂) :
    value φ (r₁ ++ post) = value φ (pre ++ r₂) := by
  rw [value_append, ← h₁, ← value_append, hc, value_append, h₂, value_append]

private theorem inclusion {l₁ r₁ l₂ r₂ : List ℤ}
    (h₁ : value φ l₁ = value φ r₁) (h₂ : value φ l₂ = value φ r₂)
    (pre post : List ℤ) (hc : l₁ = pre ++ l₂ ++ post) :
    value φ r₁ = value φ (pre ++ r₂ ++ post) := by
  rw [← h₁, hc]
  exact in_context h₂ pre post

@[expose] def localWords : Fin 14 → List ℤ
  | 0 => [-2, -2]
  | 1 => [0, 0]
  | 2 => [2, 2]
  | 3 => [-2, 2, -2, 2, -2, 2, -2, 2, -2, 2]
  | 4 => [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0]
  | 5 => [0, -2, 0, -2, 0, -2, 0, -2, 0, -2, 0, -2]
  | 6 => [2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2, 0]
  | 7 => [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2]
  | 8 => [0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2]
  | 9 => [-2, 2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2]
  | 10 => [2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2]
  | 11 => [-2, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2, 0]
  | 12 => [2, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2]
  | 13 => [-2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2]

@[expose] def Relations (φ : InvolutionFamily E) : Prop := ∀ i, value φ (localWords i) = 1

private theorem eq0 (h : Relations φ) : value φ [-2, -2] = value φ [] := by
  have h0 : value φ [-2, -2] = value φ [] :=
    relation_split (localWords 0) (h 0) true 1 _ _ (by decide)
  have hl : value φ [-2, -2] = value φ [-2, -2] := rfl
  have hr : value φ [] = value φ [] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq1 (h : Relations φ) : value φ [0, 0] = value φ [] := by
  have h0 : value φ [0, 0] = value φ [] :=
    relation_split (localWords 1) (h 1) true 1 _ _ (by decide)
  have hl : value φ [0, 0] = value φ [0, 0] := rfl
  have hr : value φ [] = value φ [] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq2 (h : Relations φ) : value φ [2, 2] = value φ [] := by
  have h0 : value φ [2, 2] = value φ [] :=
    relation_split (localWords 2) (h 2) true 1 _ _ (by decide)
  have hl : value φ [2, 2] = value φ [2, 2] := rfl
  have hr : value φ [] = value φ [] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq3 (h : Relations φ) : value φ [-2, 2, -2, 2, -2] = value φ [2, -2, 2, -2, 2] := by
  have h0 : value φ [-2, 2, -2, 2, -2] = value φ [2, -2, 2, -2, 2] :=
    relation_split (localWords 3) (h 3) true 9 _ _ (by decide)
  have hl : value φ [-2, 2, -2, 2, -2] = value φ [-2, 2, -2, 2, -2] := rfl
  have hr : value φ [2, -2, 2, -2, 2] = value φ [2, -2, 2, -2, 2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq4 (h : Relations φ) : value φ [2, 0, 2, 0, 2, 0] = value φ [0, 2, 0, 2, 0, 2] := by
  have h0 : value φ [2, 0, 2, 0, 2, 0] = value φ [0, 2, 0, 2, 0, 2] :=
    relation_split (localWords 4) (h 4) true 11 _ _ (by decide)
  have hl : value φ [2, 0, 2, 0, 2, 0] = value φ [2, 0, 2, 0, 2, 0] := rfl
  have hr : value φ [0, 2, 0, 2, 0, 2] = value φ [0, 2, 0, 2, 0, 2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq5 (h : Relations φ) : value φ [-2, 0, -2, 0, -2, 0] = value φ [0, -2, 0, -2, 0, -2] := by
  have h0 : value φ [0, -2, 0, -2, 0, -2] = value φ [-2, 0, -2, 0, -2, 0] :=
    relation_split (localWords 5) (h 5) true 11 _ _ (by decide)
  have hl : value φ [0, -2, 0, -2, 0, -2] = value φ [0, -2, 0, -2, 0, -2] := rfl
  have hr : value φ [-2, 0, -2, 0, -2, 0] = value φ [-2, 0, -2, 0, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq6 (h : Relations φ) : value φ [2, 0, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, 2] := by
  have h0 : value φ [2, 0, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, 2] :=
    relation_split (localWords 11) (h 11) true 14 _ _ (by decide)
  have hl : value φ [2, 0, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [2, 0, 2, -2, 0, -2, 0, -2, 2, 0] := rfl
  have hr : value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, 2] = value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, 2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq7 (h : Relations φ) : value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, 2, 0] = value φ [2, 0, 2, -2, 0, -2, 0, -2, 2] := by
  have h0 : value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, 2, 0] = value φ [2, 0, 2, -2, 0, -2, 0, -2, 2] :=
    relation_split (localWords 11) (h 11) true 15 _ _ (by decide)
  have hl : value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, 2, 0] = value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, 2, 0] := rfl
  have hr : value φ [2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [2, 0, 2, -2, 0, -2, 0, -2, 2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq8 (h : Relations φ) : value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, 0] = value φ [0, 2, 0, 2, -2, 0, -2, 0, -2, 2] := by
  have h0 : value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, 0] = value φ [0, 2, 0, 2, -2, 0, -2, 0, -2, 2] :=
    relation_split (localWords 11) (h 11) true 16 _ _ (by decide)
  have hl : value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, 0] := rfl
  have hr : value φ [0, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [0, 2, 0, 2, -2, 0, -2, 0, -2, 2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq9 (h : Relations φ) : value φ [-2, 0, -2, 0, -2, 2, 0, 2, 0, 2] = value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, -2] := by
  have h0 : value φ [-2, 0, -2, 0, -2, 2, 0, 2, 0, 2] = value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, -2] :=
    relation_split (localWords 11) (h 11) true 17 _ _ (by decide)
  have hl : value φ [-2, 0, -2, 0, -2, 2, 0, 2, 0, 2] = value φ [-2, 0, -2, 0, -2, 2, 0, 2, 0, 2] := rfl
  have hr : value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, -2] = value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq10 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 0] = value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, -2] := by
  have h0 : value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 0] :=
    relation_split (localWords 11) (h 11) true 18 _ _ (by decide)
  have hl : value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, -2] := rfl
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq11 (h : Relations φ) : value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, -2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2] := by
  have h0 : value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, -2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2] :=
    relation_split (localWords 11) (h 11) true 18 _ _ (by decide)
  have hl : value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, -2, 0] = value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, -2, 0] := rfl
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq12 (h : Relations φ) : value φ [-2, 0, -2, 2, 0, 2, 0, 2, -2, 0] = value φ [0, -2, 2, 0, 2, 0, 2, -2, 0, -2] := by
  have h0 : value φ [-2, 0, -2, 2, 0, 2, 0, 2, -2, 0] = value φ [0, -2, 2, 0, 2, 0, 2, -2, 0, -2] :=
    relation_split (localWords 11) (h 11) true 19 _ _ (by decide)
  have hl : value φ [-2, 0, -2, 2, 0, 2, 0, 2, -2, 0] = value φ [-2, 0, -2, 2, 0, 2, 0, 2, -2, 0] := rfl
  have hr : value φ [0, -2, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [0, -2, 2, 0, 2, 0, 2, -2, 0, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq13 (h : Relations φ) : value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [-2, 0, -2, 0, -2, 2, 0, 2, 0] := by
  have h0 : value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [-2, 0, -2, 0, -2, 2, 0, 2, 0] :=
    relation_split (localWords 11) (h 11) true 12 _ _ (by decide)
  have hl : value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] := rfl
  have hr : value φ [-2, 0, -2, 0, -2, 2, 0, 2, 0] = value φ [-2, 0, -2, 0, -2, 2, 0, 2, 0] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq14 (h : Relations φ) : value φ [2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2] := by
  have h0 : value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2] = value φ [2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 0, 2] :=
    relation_split (localWords 7) (h 7) false 0 _ _ (by decide)
  have hl : value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2] := rfl
  have hr : value φ [2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq15 (h : Relations φ) : value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2] = value φ [2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 0] := by
  have h0 : value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2] = value φ [2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 0] :=
    relation_split (localWords 7) (h 7) false 0 _ _ (by decide)
  have hl : value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2] := rfl
  have hr : value φ [2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 0] = value φ [2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 0] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq16 (h : Relations φ) : value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2] := by
  have h0 : value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2] = value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 0] :=
    relation_split (localWords 7) (h 7) false 1 _ _ (by decide)
  have hl : value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2] := rfl
  have hr : value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 0] = value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq17 (h : Relations φ) : value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0] = value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2] := by
  have h0 : value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0] = value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2] :=
    relation_split (localWords 7) (h 7) false 1 _ _ (by decide)
  have hl : value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0] := rfl
  have hr : value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2] = value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq20 (h : Relations φ) : value φ [-2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0] = value φ [0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2] := by
  have h0 : value φ [0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2] = value φ [-2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0] :=
    relation_split (localWords 7) (h 7) false 3 _ _ (by decide)
  have hl : value φ [0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2] = value φ [0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2] := rfl
  have hr : value φ [-2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0] = value φ [-2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq21 (h : Relations φ) : value φ [0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0] = value φ [-2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2] := by
  have h0 : value φ [0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0] = value φ [-2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2] :=
    relation_split (localWords 7) (h 7) false 3 _ _ (by decide)
  have hl : value φ [0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0] = value φ [0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0] := rfl
  have hr : value φ [-2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2] = value φ [-2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq22 (h : Relations φ) : value φ [0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2] = value φ [-2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0] := by
  have h0 : value φ [-2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0] = value φ [0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2] :=
    relation_split (localWords 7) (h 7) false 4 _ _ (by decide)
  have hl : value φ [-2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0] = value φ [-2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0] := rfl
  have hr : value φ [0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2] = value φ [0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq26 (h : Relations φ) : value φ [0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2] = value φ [-2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2] := by
  have h0 : value φ [-2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2] :=
    relation_split (localWords 7) (h 7) false 6 _ _ (by decide)
  have hl : value φ [-2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [-2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2] := rfl
  have hr : value φ [0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2] = value φ [0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq28 (h : Relations φ) : value φ [-2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 0] = value φ [2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] := by
  have h0 : value φ [2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] = value φ [-2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 0] :=
    relation_split (localWords 7) (h 7) false 7 _ _ (by decide)
  have hl : value φ [2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] = value φ [2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] := rfl
  have hr : value φ [-2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 0] = value φ [-2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq29 (h : Relations φ) : value φ [2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0] = value φ [-2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] := by
  have h0 : value φ [2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0] = value φ [-2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] :=
    relation_split (localWords 7) (h 7) false 7 _ _ (by decide)
  have hl : value φ [2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0] = value φ [2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0] := rfl
  have hr : value φ [-2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] = value φ [-2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq30 (h : Relations φ) : value φ [2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] = value φ [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0] := by
  have h0 : value φ [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] :=
    relation_split (localWords 7) (h 7) false 8 _ _ (by decide)
  have hl : value φ [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0] = value φ [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0] := rfl
  have hr : value φ [2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq31 (h : Relations φ) : value φ [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0] := by
  have h0 : value φ [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0] :=
    relation_split (localWords 7) (h 7) false 8 _ _ (by decide)
  have hl : value φ [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2] = value φ [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2] := rfl
  have hr : value φ [2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq33 (h : Relations φ) : value φ [0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2] := by
  have h0 : value φ [0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2] :=
    relation_split (localWords 7) (h 7) false 9 _ _ (by decide)
  have hl : value φ [0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0] = value φ [0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0] := rfl
  have hr : value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq34 (h : Relations φ) : value φ [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2] = value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0] := by
  have h0 : value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0] = value φ [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2] :=
    relation_split (localWords 7) (h 7) false 10 _ _ (by decide)
  have hl : value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0] = value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0] := rfl
  have hr : value φ [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2] = value φ [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq35 (h : Relations φ) : value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2] = value φ [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2] := by
  have h0 : value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2] = value φ [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2] :=
    relation_split (localWords 7) (h 7) false 10 _ _ (by decide)
  have hl : value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2] = value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2] := rfl
  have hr : value φ [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2] = value φ [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq36 (h : Relations φ) : value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2] = value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2] := by
  have h0 : value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2] = value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2] :=
    relation_split (localWords 7) (h 7) false 11 _ _ (by decide)
  have hl : value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2] = value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2] := rfl
  have hr : value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2] = value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq37 (h : Relations φ) : value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2] = value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0] := by
  have h0 : value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2] = value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0] :=
    relation_split (localWords 7) (h 7) false 11 _ _ (by decide)
  have hl : value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2] = value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2] := rfl
  have hr : value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0] = value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq38 (h : Relations φ) : value φ [0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2] := by
  have h0 : value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2] = value φ [0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0] :=
    relation_split (localWords 7) (h 7) false 12 _ _ (by decide)
  have hl : value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2] = value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2] := rfl
  have hr : value φ [0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0] = value φ [0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq39 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0] = value φ [0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2] := by
  have h0 : value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0] = value φ [0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2] :=
    relation_split (localWords 7) (h 7) false 12 _ _ (by decide)
  have hl : value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0] := rfl
  have hr : value φ [0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2] = value φ [0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq40 (h : Relations φ) : value φ [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2] = value φ [2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0] := by
  have h0 : value φ [2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0] = value φ [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2] :=
    relation_split (localWords 7) (h 7) false 13 _ _ (by decide)
  have hl : value φ [2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0] = value φ [2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0] := rfl
  have hr : value φ [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2] = value φ [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq41 (h : Relations φ) : value φ [2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2] = value φ [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2] := by
  have h0 : value φ [2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2] = value φ [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2] :=
    relation_split (localWords 7) (h 7) false 13 _ _ (by decide)
  have hl : value φ [2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2] = value φ [2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2] := rfl
  have hr : value φ [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2] = value φ [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq42 (h : Relations φ) : value φ [2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2] = value φ [0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2] := by
  have h0 : value φ [0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2] = value φ [2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2] :=
    relation_split (localWords 7) (h 7) false 14 _ _ (by decide)
  have hl : value φ [0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2] = value φ [0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2] := rfl
  have hr : value φ [2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2] = value φ [2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq43 (h : Relations φ) : value φ [0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2] = value φ [2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] := by
  have h0 : value φ [0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2] = value φ [2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] :=
    relation_split (localWords 7) (h 7) false 14 _ _ (by decide)
  have hl : value φ [0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2] = value φ [0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2] := rfl
  have hr : value φ [2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] = value φ [2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq44 (h : Relations φ) : value φ [0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] = value φ [2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2] := by
  have h0 : value φ [2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2] = value φ [0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] :=
    relation_split (localWords 7) (h 7) false 15 _ _ (by decide)
  have hl : value φ [2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2] = value φ [2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2] := rfl
  have hr : value φ [0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] = value φ [0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq45 (h : Relations φ) : value φ [2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2] = value φ [0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2] := by
  have h0 : value φ [2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2] = value φ [0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2] :=
    relation_split (localWords 7) (h 7) false 15 _ _ (by decide)
  have hl : value φ [2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2] = value φ [2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2] := rfl
  have hr : value φ [0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2] = value φ [0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq46 (h : Relations φ) : value φ [2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2] = value φ [0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2] := by
  have h0 : value φ [0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2] = value φ [2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2] :=
    relation_split (localWords 7) (h 7) false 16 _ _ (by decide)
  have hl : value φ [0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2] = value φ [0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2] := rfl
  have hr : value φ [2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2] = value φ [2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq49 (h : Relations φ) : value φ [2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2] := by
  have h0 : value φ [2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2] :=
    relation_split (localWords 7) (h 7) false 17 _ _ (by decide)
  have hl : value φ [2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0] = value φ [2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0] := rfl
  have hr : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq50 (h : Relations φ) : value φ [2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2] = value φ [-2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0] := by
  have h0 : value φ [-2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0] = value φ [2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2] :=
    relation_split (localWords 7) (h 7) false 18 _ _ (by decide)
  have hl : value φ [-2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0] = value φ [-2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0] := rfl
  have hr : value φ [2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2] = value φ [2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq53 (h : Relations φ) : value φ [2, 0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0, -2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2] := by
  have h0 : value φ [2, 0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0, -2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2] :=
    relation_split (localWords 7) (h 7) false 19 _ _ (by decide)
  have hl : value φ [2, 0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0, -2, 0] = value φ [2, 0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0, -2, 0] := rfl
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq55 (h : Relations φ) : value φ [0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2] = value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] := by
  have h0 : value φ [0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2] = value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] :=
    relation_split (localWords 7) (h 7) false 20 _ _ (by decide)
  have hl : value φ [0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2] = value φ [0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2] := rfl
  have hr : value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] = value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq56 (h : Relations φ) : value φ [0, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] = value φ [-2, 0, -2, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2] := by
  have h0 : value φ [-2, 0, -2, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2] = value φ [0, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] :=
    relation_split (localWords 7) (h 7) false 21 _ _ (by decide)
  have hl : value φ [-2, 0, -2, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2] = value φ [-2, 0, -2, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2] := rfl
  have hr : value φ [0, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] = value φ [0, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq66 (h : Relations φ) : value φ [0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2] = value φ [2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] := by
  have h0 : value φ [2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] = value φ [0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2] :=
    relation_split (localWords 7) (h 7) false 26 _ _ (by decide)
  have hl : value φ [2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] = value φ [2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] := rfl
  have hr : value φ [0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2] = value φ [0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq79 (h : Relations φ) : value φ [0, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2, -2] := by
  have h0 : value φ [0, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2, -2] :=
    relation_split (localWords 8) (h 8) false 5 _ _ (by decide)
  have hl : value φ [0, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0] = value φ [0, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0] := rfl
  have hr : value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2, -2] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq81 (h : Relations φ) : value φ [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2] = value φ [0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2] := by
  have h0 : value φ [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2] = value φ [0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2] :=
    relation_split (localWords 8) (h 8) false 6 _ _ (by decide)
  have hl : value φ [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2] = value φ [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2] := rfl
  have hr : value φ [0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2] = value φ [0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq82 (h : Relations φ) : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2] = value φ [0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2] := by
  have h0 : value φ [0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2] :=
    relation_split (localWords 8) (h 8) false 7 _ _ (by decide)
  have hl : value φ [0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2] = value φ [0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2] := rfl
  have hr : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq83 (h : Relations φ) : value φ [0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] := by
  have h0 : value φ [0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] :=
    relation_split (localWords 8) (h 8) false 7 _ _ (by decide)
  have hl : value φ [0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 2] = value φ [0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 2] := rfl
  have hr : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq84 (h : Relations φ) : value φ [0, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] = value φ [2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 2] := by
  have h0 : value φ [2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 2] = value φ [0, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] :=
    relation_split (localWords 8) (h 8) false 8 _ _ (by decide)
  have hl : value φ [2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 2] = value φ [2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 2] := rfl
  have hr : value φ [0, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] = value φ [0, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq86 (h : Relations φ) : value φ [2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] = value φ [-2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 2, 0] := by
  have h0 : value φ [-2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 2, 0] = value φ [2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] :=
    relation_split (localWords 8) (h 8) false 9 _ _ (by decide)
  have hl : value φ [-2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 2, 0] := rfl
  have hr : value φ [2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] = value φ [2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq93 (h : Relations φ) : value φ [2, 0, 2, -2, 2, -2, 0, -2, 2, 0, 2, 0, -2, 2] = value φ [0, 2, -2, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2] := by
  have h0 : value φ [2, 0, 2, -2, 2, -2, 0, -2, 2, 0, 2, 0, -2, 2] = value φ [0, 2, -2, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2] :=
    relation_split (localWords 8) (h 8) false 12 _ _ (by decide)
  have hl : value φ [2, 0, 2, -2, 2, -2, 0, -2, 2, 0, 2, 0, -2, 2] = value φ [2, 0, 2, -2, 2, -2, 0, -2, 2, 0, 2, 0, -2, 2] := rfl
  have hr : value φ [0, 2, -2, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2] = value φ [0, 2, -2, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq96 (h : Relations φ) : value φ [0, 2, 0, 2, -2, 2, 0, -2, 0, 2, -2, 0, -2, 0] = value φ [2, -2, 2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2] := by
  have h0 : value φ [2, -2, 2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2] = value φ [0, 2, 0, 2, -2, 2, 0, -2, 0, 2, -2, 0, -2, 0] :=
    relation_split (localWords 8) (h 8) false 14 _ _ (by decide)
  have hl : value φ [2, -2, 2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2] = value φ [2, -2, 2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2] := rfl
  have hr : value φ [0, 2, 0, 2, -2, 2, 0, -2, 0, 2, -2, 0, -2, 0] = value φ [0, 2, 0, 2, -2, 2, 0, -2, 0, 2, -2, 0, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq100 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2, -2, 0] = value φ [2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, -2] := by
  have h0 : value φ [2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, -2] = value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2, -2, 0] :=
    relation_split (localWords 8) (h 8) false 16 _ _ (by decide)
  have hl : value φ [2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, -2] = value φ [2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, -2] := rfl
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2, -2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq101 (h : Relations φ) : value φ [2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, -2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2, -2] := by
  have h0 : value φ [2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, -2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2, -2] :=
    relation_split (localWords 8) (h 8) false 16 _ _ (by decide)
  have hl : value φ [2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, -2, 0] = value φ [2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, -2, 0] := rfl
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2, -2] = value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq103 (h : Relations φ) : value φ [-2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2] = value φ [2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2] := by
  have h0 : value φ [-2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2] = value φ [2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2] :=
    relation_split (localWords 8) (h 8) false 17 _ _ (by decide)
  have hl : value φ [-2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2] = value φ [-2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2] := rfl
  have hr : value φ [2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2] = value φ [2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq116 (h : Relations φ) : value φ [0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2, 0, 2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2] := by
  have h0 : value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2] = value φ [0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2, 0, 2] :=
    relation_split (localWords 8) (h 8) false 24 _ _ (by decide)
  have hl : value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2] := rfl
  have hr : value φ [0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2, 0, 2] = value φ [0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq117 (h : Relations φ) : value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2] = value φ [0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2, 0] := by
  have h0 : value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2] = value φ [0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2, 0] :=
    relation_split (localWords 8) (h 8) false 24 _ _ (by decide)
  have hl : value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2] := rfl
  have hr : value φ [0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2, 0] = value φ [0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2, 0] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq118 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2] := by
  have h0 : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2] = value φ [-2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2, 0] :=
    relation_split (localWords 8) (h 8) false 25 _ _ (by decide)
  have hl : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2] := rfl
  have hr : value φ [-2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2, 0] = value φ [-2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq120 (h : Relations φ) : value φ [2, -2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2] = value φ [-2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2, 0] := by
  have h0 : value φ [-2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2, 0] = value φ [2, -2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2] :=
    relation_split (localWords 8) (h 8) false 26 _ _ (by decide)
  have hl : value φ [-2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2, 0] = value φ [-2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2, 0] := rfl
  have hr : value φ [2, -2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2] = value φ [2, -2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq132 (h : Relations φ) : value φ [2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0] = value φ [-2, 2, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2] := by
  have h0 : value φ [2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0] = value φ [-2, 2, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2] :=
    relation_split (localWords 9) (h 9) false 6 _ _ (by decide)
  have hl : value φ [2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0] = value φ [2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0] := rfl
  have hr : value φ [-2, 2, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2] = value φ [-2, 2, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq144 (h : Relations φ) : value φ [-2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2, -2, 2, -2, 2] = value φ [0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] := by
  have h0 : value φ [0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] = value φ [-2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2, -2, 2, -2, 2] :=
    relation_split (localWords 9) (h 9) false 14 _ _ (by decide)
  have hl : value φ [0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] = value φ [0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] := rfl
  have hr : value φ [-2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2, -2, 2, -2, 2] = value φ [-2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2, -2, 2, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq147 (h : Relations φ) : value φ [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2, -2, 2] = value φ [0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2] := by
  have h0 : value φ [0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2] = value φ [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2, -2, 2] :=
    relation_split (localWords 9) (h 9) false 16 _ _ (by decide)
  have hl : value φ [0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2] = value φ [0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2] := rfl
  have hr : value φ [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2, -2, 2] = value φ [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq149 (h : Relations φ) : value φ [-2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2] = value φ [0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2, -2] := by
  have h0 : value φ [-2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2] = value φ [0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2, -2] :=
    relation_split (localWords 9) (h 9) false 17 _ _ (by decide)
  have hl : value φ [-2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2] = value φ [-2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2] := rfl
  have hr : value φ [0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2, -2] = value φ [0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq150 (h : Relations φ) : value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2] = value φ [0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2] := by
  have h0 : value φ [0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2] = value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2] :=
    relation_split (localWords 9) (h 9) false 18 _ _ (by decide)
  have hl : value φ [0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2] = value φ [0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2] := rfl
  have hr : value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2] = value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq151 (h : Relations φ) : value φ [0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] = value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0] := by
  have h0 : value φ [0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] = value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0] :=
    relation_split (localWords 9) (h 9) false 18 _ _ (by decide)
  have hl : value φ [0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] = value φ [0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] := rfl
  have hr : value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0] = value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq152 (h : Relations φ) : value φ [2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] = value φ [0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0] := by
  have h0 : value φ [2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] = value φ [0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0] :=
    relation_split (localWords 9) (h 9) false 19 _ _ (by decide)
  have hl : value φ [2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] = value φ [2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] := rfl
  have hr : value φ [0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0] = value φ [0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq156 (h : Relations φ) : value φ [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2] = value φ [0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2] := by
  have h0 : value φ [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2] = value φ [0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2] :=
    relation_split (localWords 9) (h 9) false 22 _ _ (by decide)
  have hl : value φ [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2] = value φ [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2] := rfl
  have hr : value φ [0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2] = value φ [0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq158 (h : Relations φ) : value φ [0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2, -2, 2] = value φ [2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] := by
  have h0 : value φ [0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2, -2, 2] = value φ [2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] :=
    relation_split (localWords 9) (h 9) false 23 _ _ (by decide)
  have hl : value φ [0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2, -2, 2] = value φ [0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2, -2, 2] := rfl
  have hr : value φ [2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] = value φ [2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq159 (h : Relations φ) : value φ [-2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2, -2, 2] = value φ [0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] := by
  have h0 : value φ [-2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2, -2, 2] = value φ [0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] :=
    relation_split (localWords 9) (h 9) false 24 _ _ (by decide)
  have hl : value φ [-2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2, -2, 2] = value φ [-2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2, -2, 2] := rfl
  have hr : value φ [0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] = value φ [0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq169 (h : Relations φ) : value φ [2, -2, 2, -2, 2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2] = value φ [0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0] := by
  have h0 : value φ [2, -2, 2, -2, 2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2] = value φ [0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0] :=
    relation_split (localWords 9) (h 9) false 31 _ _ (by decide)
  have hl : value φ [2, -2, 2, -2, 2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2] = value φ [2, -2, 2, -2, 2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2] := rfl
  have hr : value φ [0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0] = value φ [0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq171 (h : Relations φ) : value φ [-2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0] = value φ [2, -2, 2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2] := by
  have h0 : value φ [2, -2, 2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2] = value φ [-2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0] :=
    relation_split (localWords 9) (h 9) false 33 _ _ (by decide)
  have hl : value φ [2, -2, 2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2] = value φ [2, -2, 2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2] := rfl
  have hr : value φ [-2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0] = value φ [-2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq174 (h : Relations φ) : value φ [2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0] = value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] := by
  have h0 : value φ [2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0] = value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] :=
    relation_split (localWords 9) (h 9) true 14 _ _ (by decide)
  have hl : value φ [2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0] = value φ [2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0] := rfl
  have hr : value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] = value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq192 (h : Relations φ) : value φ [2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0, 2] := by
  have h0 : value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0, 2] = value φ [2, -2, 2, 0, 2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2] :=
    relation_split (localWords 10) (h 10) false 11 _ _ (by decide)
  have hl : value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0, 2] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0, 2] := rfl
  have hr : value φ [2, -2, 2, 0, 2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2] = value φ [2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2] :=
    ((in_context (eq4 h) [2, -2] [-2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2]).trans (in_context (eq4 h) [2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2] [-2, 0, -2, 2, 0, -2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq220 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0] := by
  have h0 : value φ [2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2] = value φ [-2, 2, 0, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, 0, -2, 0, 2, -2, 2, 0, 2, 0] :=
    relation_split (localWords 10) (h 10) false 29 _ _ (by decide)
  have hl : value φ [2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0] :=
    ((in_context (eq192 h) [] [0, 2]).trans ((in_context (eq4 h) [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 0] [2]).trans ((in_context (eq1 h) [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2] [2, 0, 2, 0, 2, 2]).trans (in_context (eq2 h) [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0] []))))
  have hr : value φ [-2, 2, 0, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, 0, -2, 0, 2, -2, 2, 0, 2, 0] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0] :=
    ((in_context (eq4 h) [-2] [-2, 2, -2, 2, 0, 2, 0, 2, 0, -2, 0, 2, -2, 2, 0, 2, 0]).trans (in_context (eq4 h) [-2, 0, 2, 0, 2, 0, 2, -2, 2, -2] [-2, 0, 2, -2, 2, 0, 2, 0]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq228 (h : Relations φ) : value φ [-2, 2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0] = value φ [0, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2] := by
  have h0 : value φ [0, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2] = value φ [-2, 2, -2, 2, 0, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, 0, -2, 0, 2, -2, 2, 0, 2, 0] :=
    relation_split (localWords 10) (h 10) false 31 _ _ (by decide)
  have hl : value φ [0, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2] = value φ [0, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2] := rfl
  have hr : value φ [-2, 2, -2, 2, 0, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, 0, -2, 0, 2, -2, 2, 0, 2, 0] = value φ [-2, 2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0] :=
    ((in_context (eq4 h) [-2, 2, -2] [-2, 2, -2, 2, 0, 2, 0, 2, 0, -2, 0, 2, -2, 2, 0, 2, 0]).trans ((in_context (eq4 h) [-2, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2] [-2, 0, 2, -2, 2, 0, 2, 0]).trans (in_context (eq220 h) [-2, 2] [])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq261 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, 2, -2] = value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2] := by
  have h0 : value φ [0, -2, 2, 0, -2, 2, 0, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, 0, -2, 0, 2] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, 2, -2] :=
    relation_split (localWords 10) (h 10) true 10 _ _ (by decide)
  have hl : value φ [0, -2, 2, 0, -2, 2, 0, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, 0, -2, 0, 2] = value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2] :=
    ((in_context (eq4 h) [0, -2, 2, 0, -2] [-2, 2, -2, 2, 0, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, 0, -2, 0, 2]).trans ((in_context (eq4 h) [0, -2, 2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 2, -2] [-2, 2, -2, 2, 0, 2, 0, 2, 0, -2, 0, 2]).trans ((in_context (eq228 h) [0] [2, 0, -2, 0, 2]).trans ((in_context (eq1 h) [] [2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 2, 0, -2, 0, 2]).trans ((in_context (eq2 h) [2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0] [0, -2, 0, 2]).trans ((in_context (eq1 h) [2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2] [-2, 0, 2]).trans ((in_context (eq0 h) [2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0] [0, 2]).trans ((in_context (eq1 h) [2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2] [2]).trans (in_context (eq2 h) [2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2] [])))))))))
  have hr : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, 2, -2] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, 2, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq267 (h : Relations φ) : value φ [-2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2] = value φ [2, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0] := by
  have h0 : value φ [2, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0] = value φ [-2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2] :=
    relation_split (localWords 12) (h 12) false 0 _ _ (by decide)
  have hl : value φ [2, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0] = value φ [2, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0] := rfl
  have hr : value φ [-2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2] = value φ [-2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq275 (h : Relations φ) : value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2] = value φ [-2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0] := by
  have h0 : value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2] = value φ [-2, 2, 0, -2, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0] :=
    relation_split (localWords 12) (h 12) false 5 _ _ (by decide)
  have hl : value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2] = value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2] := rfl
  have hr : value φ [-2, 2, 0, -2, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0] = value φ [-2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0] :=
    (in_context (eq3 h) [-2, 2, 0] [0, 2, 0, 2, -2, 0, 2, 0])
  exact hl.symm.trans (h0.trans hr)

private theorem eq276 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2] = value φ [2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0] := by
  have h0 : value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2] = value φ [2, -2, 2, 0, -2, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0] :=
    relation_split (localWords 12) (h 12) false 6 _ _ (by decide)
  have hl : value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2] := rfl
  have hr : value φ [2, -2, 2, 0, -2, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0] = value φ [2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0] :=
    (in_context (eq3 h) [2, -2, 2, 0] [0, 2, 0, 2, -2, 0, 2, 0])
  exact hl.symm.trans (h0.trans hr)

private theorem eq277 (h : Relations φ) : value φ [-2, 2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0] := by
  have h0 : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0] = value φ [-2, 2, -2, 2, 0, -2, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2] :=
    relation_split (localWords 12) (h 12) false 7 _ _ (by decide)
  have hl : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0] := rfl
  have hr : value φ [-2, 2, -2, 2, 0, -2, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2] = value φ [-2, 2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2] :=
    (in_context (eq3 h) [-2, 2, -2, 2, 0] [0, 2, 0, 2, -2, 0, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq278 (h : Relations φ) : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2] = value φ [-2, 2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0] := by
  have h0 : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2] = value φ [-2, 2, -2, 2, 0, -2, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0] :=
    relation_split (localWords 12) (h 12) false 7 _ _ (by decide)
  have hl : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2] := rfl
  have hr : value φ [-2, 2, -2, 2, 0, -2, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0] = value φ [-2, 2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0] :=
    (in_context (eq3 h) [-2, 2, -2, 2, 0] [0, 2, 0, 2, -2, 0])
  exact hl.symm.trans (h0.trans hr)

private theorem eq283 (h : Relations φ) : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2] = value φ [2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0] := by
  have h0 : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2] = value φ [2, 0, 2, 0, -2, 2, -2, 2, 0, -2, 2, -2, 2, -2, 0, 2, 0] :=
    relation_split (localWords 12) (h 12) false 11 _ _ (by decide)
  have hl : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2] := rfl
  have hr : value φ [2, 0, 2, 0, -2, 2, -2, 2, 0, -2, 2, -2, 2, -2, 0, 2, 0] = value φ [2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0] :=
    (in_context (eq3 h) [2, 0, 2, 0, -2, 2, -2, 2, 0] [0, 2, 0])
  exact hl.symm.trans (h0.trans hr)

private theorem eq287 (h : Relations φ) : value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2, 2, -2, 2] = value φ [0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] := by
  have h0 : value φ [0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] = value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, -2, 2, -2, 2, -2] :=
    relation_split (localWords 12) (h 12) false 14 _ _ (by decide)
  have hl : value φ [0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] = value φ [0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] := rfl
  have hr : value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, -2, 2, -2, 2, -2] = value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2, 2, -2, 2] :=
    (in_context (eq3 h) [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0] [])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq292 (h : Relations φ) : value φ [2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2] = value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, -2, 2] := by
  have h0 : value φ [2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2] = value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, -2, 2] :=
    relation_split (localWords 12) (h 12) false 17 _ _ (by decide)
  have hl : value φ [2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2] = value φ [2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2] := rfl
  have hr : value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, -2, 2] = value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, -2, 2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq293 (h : Relations φ) : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, -2] = value φ [0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2] := by
  have h0 : value φ [0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2] = value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, -2] :=
    relation_split (localWords 12) (h 12) false 18 _ _ (by decide)
  have hl : value φ [0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2] = value φ [0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2] := rfl
  have hr : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, -2] = value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq295 (h : Relations φ) : value φ [-2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2] = value φ [0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0] := by
  have h0 : value φ [-2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, -2] = value φ [0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0] :=
    relation_split (localWords 12) (h 12) false 19 _ _ (by decide)
  have hl : value φ [-2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, -2] = value φ [-2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2] :=
    (in_context (eq3 h) [-2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] [])
  have hr : value φ [0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0] = value φ [0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq296 (h : Relations φ) : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2] = value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0] := by
  have h0 : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, -2, 0] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2] :=
    relation_split (localWords 12) (h 12) false 20 _ _ (by decide)
  have hl : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, -2, 0] = value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0] :=
    (in_context (eq3 h) [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] [0])
  have hr : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq300 (h : Relations φ) : value φ [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2] = value φ [0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2] := by
  have h0 : value φ [-2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, -2, 0, 2, -2] = value φ [0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2] :=
    relation_split (localWords 12) (h 12) false 22 _ _ (by decide)
  have hl : value φ [-2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, -2, 0, 2, -2] = value φ [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2] :=
    (in_context (eq3 h) [-2, 0, 2, 0, -2, 2, 0, 2, 0] [0, 2, -2])
  have hr : value φ [0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2] = value φ [0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq302 (h : Relations φ) : value φ [0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2] = value φ [-2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] := by
  have h0 : value φ [0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, -2, 0, 2, -2, 2, -2] = value φ [-2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] :=
    relation_split (localWords 12) (h 12) false 23 _ _ (by decide)
  have hl : value φ [0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, -2, 0, 2, -2, 2, -2] = value φ [0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2] :=
    (in_context (eq3 h) [0, 2, 0, -2, 2, 0, 2, 0] [0, 2, -2, 2, -2])
  have hr : value φ [-2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] = value φ [-2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq303 (h : Relations φ) : value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2] = value φ [0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] := by
  have h0 : value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, -2, 0, 2, -2, 2, -2] = value φ [0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] :=
    relation_split (localWords 12) (h 12) false 24 _ _ (by decide)
  have hl : value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, -2, 0, 2, -2, 2, -2] = value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2] :=
    (in_context (eq3 h) [2, 0, -2, 2, 0, 2, 0] [0, 2, -2, 2, -2])
  have hr : value φ [0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] = value φ [0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq306 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2] = value φ [0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0] := by
  have h0 : value φ [-2, 2, 0, 2, 0, -2, 2, -2, 2, -2, 0, 2, -2, 2, -2, 0, 2] = value φ [0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0] :=
    relation_split (localWords 12) (h 12) false 26 _ _ (by decide)
  have hl : value φ [-2, 2, 0, 2, 0, -2, 2, -2, 2, -2, 0, 2, -2, 2, -2, 0, 2] = value φ [-2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2] :=
    (in_context (eq3 h) [-2, 2, 0, 2, 0] [0, 2, -2, 2, -2, 0, 2])
  have hr : value φ [0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0] = value φ [0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq308 (h : Relations φ) : value φ [2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2] = value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] := by
  have h0 : value φ [2, 0, 2, 0, -2, 2, -2, 2, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2] = value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] :=
    relation_split (localWords 12) (h 12) false 27 _ _ (by decide)
  have hl : value φ [2, 0, 2, 0, -2, 2, -2, 2, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2] = value φ [2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2] :=
    (in_context (eq3 h) [2, 0, 2, 0] [0, 2, -2, 2, -2, 0, 2, 0, 2])
  have hr : value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] = value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq314 (h : Relations φ) : value φ [2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0] := by
  have h0 : value φ [-2, 2, -2, 2, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0] :=
    relation_split (localWords 12) (h 12) false 31 _ _ (by decide)
  have hl : value φ [-2, 2, -2, 2, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2] = value φ [2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2] :=
    (in_context (eq3 h) [] [0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2])
  have hr : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq316 (h : Relations φ) : value φ [2, -2, 2, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0] := by
  have h0 : value φ [2, -2, 2, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0] :=
    relation_split (localWords 12) (h 12) false 32 _ _ (by decide)
  have hl : value φ [2, -2, 2, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2] = value φ [2, -2, 2, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2] := rfl
  have hr : value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq319 (h : Relations φ) : value φ [2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2] = value φ [-2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] := by
  have h0 : value φ [2, 0, -2, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2] = value φ [-2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] :=
    relation_split (localWords 12) (h 12) true 30 _ _ (by decide)
  have hl : value φ [2, 0, -2, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2] = value φ [2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2] :=
    (in_context (eq3 h) [2, 0] [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2])
  have hr : value φ [-2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] = value φ [-2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq335 (h : Relations φ) : value φ [-2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2] = value φ [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, -2] := by
  have h0 : value φ [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, -2] = value φ [-2, 2, -2, 0, -2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 0, 2, 0, 2, -2, 0, 2] :=
    relation_split (localWords 13) (h 13) false 11 _ _ (by decide)
  have hl : value φ [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, -2] = value φ [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, -2] := rfl
  have hr : value φ [-2, 2, -2, 0, -2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 0, 2, 0, 2, -2, 0, 2] = value φ [-2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2] :=
    ((in_context (eq5 h) [-2, 2] [2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 0, 2, 0, 2, -2, 0, 2]).trans (in_context (eq5 h) [-2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2] [2, 0, 2, -2, 0, 2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq370 (h : Relations φ) : value φ [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] = value φ [2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 0, 2] := by
  have h0 : value φ [-2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 0] = value φ [2, -2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 0, 2] :=
    relation_split (localWords 13) (h 13) false 29 _ _ (by decide)
  have hl : value φ [-2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 0] = value φ [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] :=
    ((in_context (eq335 h) [] [0, -2, 0, -2, 0, -2, 2, -2, 0]).trans ((in_context (eq5 h) [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0] [-2, 0, -2, 0, -2, 2, -2, 0]).trans ((in_context (eq1 h) [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2] [-2, 0, -2, 0, -2, -2, 0, -2, 0, -2, 2, -2, 0]).trans ((in_context (eq3 h) [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0] [0, -2, 0, -2, -2, 0, -2, 0, -2, 2, -2, 0]).trans ((in_context (eq0 h) [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0] [0, -2, 0, -2, 2, -2, 0]).trans ((in_context (eq1 h) [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2] [-2, 0, -2, 2, -2, 0]).trans ((in_context (eq0 h) [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0] [0, -2, 2, -2, 0]).trans ((in_context (eq1 h) [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 2] [-2, 2, -2, 0]).trans ((in_context (eq3 h) [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, 2] [2, -2, 0]).trans ((in_context (eq2 h) [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0] [-2, 2, -2, 2, 2, -2, 0]).trans ((in_context (eq2 h) [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, -2, 2, -2] [-2, 0]).trans (in_context (eq0 h) [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, -2, 2] [0]))))))))))))
  have hr : value φ [2, -2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 0, 2] = value φ [2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 0, 2] :=
    ((in_context (eq5 h) [2] [2, -2, 2, -2, 0, -2, 0, -2, 0, 2]).trans (in_context (eq3 h) [2, 0, -2, 0, -2, 0] [0, -2, 0, -2, 0, 2]))
  exact hl.symm.trans (h0.trans hr)

private theorem eq419 (h : Relations φ) : value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2] = value φ [-2, 0, 2, 0, 2, 0, 2] := by
  have h0 : value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, -2, 0, -2, 0] = value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, 0, -2, 0, -2, 0, -2] :=
    overlap (eq11 h) (eq5 h) [0, -2, 0, -2, 2, 0, 2, 0, 2] [-2, 0, -2, 0] (by decide)
  have hl : value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, -2, 0, -2, 0] = value φ [-2, 0, 2, 0, 2, 0, 2] :=
    ((in_context (eq0 h) [-2, 2, 0, 2, 0, 2, -2, 0] [0, -2, 0]).trans ((in_context (eq1 h) [-2, 2, 0, 2, 0, 2, -2] [-2, 0]).trans ((in_context (eq0 h) [-2, 2, 0, 2, 0, 2] [0]).trans (in_context (eq4 h) [-2] []))))
  have hr : value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, 0, -2, 0, -2, 0, -2] = value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2] :=
    (in_context (eq4 h) [0, -2, 0, -2] [-2, 0, -2, 0, -2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq420 (h : Relations φ) : value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2] = value φ [0, -2, 0, 2, 0, 2, 0, 2] := by
  have h0 : value φ [0, -2, 0, -2, 0, -2, -2, 0, -2, 2, 0, 2, 0, 2] = value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2] :=
    overlap (eq5 h) (eq9 h) [-2, 0, -2, 0] [-2, 0, -2, 2, 0, 2, 0, 2] (by decide)
  have hl : value φ [0, -2, 0, -2, 0, -2, -2, 0, -2, 2, 0, 2, 0, 2] = value φ [0, -2, 0, 2, 0, 2, 0, 2] :=
    ((in_context (eq0 h) [0, -2, 0, -2, 0] [0, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq1 h) [0, -2, 0, -2] [-2, 2, 0, 2, 0, 2]).trans (in_context (eq0 h) [0, -2, 0] [2, 0, 2, 0, 2])))
  have hr : value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2] = value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq421 (h : Relations φ) : value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0] = value φ [-2, 0, 2, 0, 2, 0, 2, -2] := by
  have h0 : value φ [-2, 0, 2, 0, 2, 0, 2, -2] = value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0] :=
    overlap (eq419 h) (eq0 h) [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0] [-2] (by decide)
  have hl : value φ [-2, 0, 2, 0, 2, 0, 2, -2] = value φ [-2, 0, 2, 0, 2, 0, 2, -2] := rfl
  have hr : value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0] = value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq422 (h : Relations φ) : value φ [2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2, 0] = value φ [0, 2, 0, -2, 0, -2, 0, -2, 2] := by
  have h0 : value φ [0, 2, 0, 2, 0, 2, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2, 0] :=
    overlap (eq4 h) (eq13 h) [2, 0, 2, 0] [2, 0, 2, -2, 0, -2, 0, -2, 2] (by decide)
  have hl : value φ [0, 2, 0, 2, 0, 2, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [0, 2, 0, -2, 0, -2, 0, -2, 2] :=
    ((in_context (eq2 h) [0, 2, 0, 2, 0] [0, 2, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq1 h) [0, 2, 0, 2] [2, -2, 0, -2, 0, -2, 2]).trans (in_context (eq2 h) [0, 2, 0] [-2, 0, -2, 0, -2, 2])))
  have hr : value φ [2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2, 0] = value φ [2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq423 (h : Relations φ) : value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2] := by
  have h0 : value φ [0, -2, 0, 2, 0, 2, 0, 2, -2] = value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0] :=
    overlap (eq420 h) (eq0 h) [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0] [-2] (by decide)
  have hl : value φ [0, -2, 0, 2, 0, 2, 0, 2, -2] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2] := rfl
  have hr : value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0] = value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq424 (h : Relations φ) : value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0] := by
  have h0 : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0] = value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2] :=
    overlap (eq421 h) (eq1 h) [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2] [0] (by decide)
  have hl : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0] := rfl
  have hr : value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq425 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2] = value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2] := by
  have h0 : value φ [0, -2, 0, -2, 0, -2, -2, 2, 0, 2, 0, 2] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2] :=
    overlap (eq5 h) (eq9 h) [-2, 0] [-2, 2, 0, 2, 0, 2] (by decide)
  have hl : value φ [0, -2, 0, -2, 0, -2, -2, 2, 0, 2, 0, 2] = value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2] :=
    (in_context (eq0 h) [0, -2, 0, -2, 0] [2, 0, 2, 0, 2])
  have hr : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq426 (h : Relations φ) : value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 0] := by
  have h0 : value φ [0, -2, 0, -2, 0, -2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 0] = value φ [-2, 0, -2, 0, -2, -2, 2, 0, 2, 0, 2, -2, 0, -2] :=
    overlap (eq5 h) (eq11 h) [-2, 0, -2, 0, -2] [-2, 0, -2, 2, 0, 2, 0, 2, -2, 0] (by decide)
  have hl : value φ [0, -2, 0, -2, 0, -2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 0] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 0] :=
    ((in_context (eq0 h) [0, -2, 0, -2, 0] [0, -2, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq1 h) [0, -2, 0, -2] [-2, 2, 0, 2, 0, 2, -2, 0]).trans (in_context (eq0 h) [0, -2, 0] [2, 0, 2, 0, 2, -2, 0])))
  have hr : value φ [-2, 0, -2, 0, -2, -2, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2] :=
    (in_context (eq0 h) [-2, 0, -2, 0] [2, 0, 2, 0, 2, -2, 0, -2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq427 (h : Relations φ) : value φ [2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2] = value φ [0, 2, 0, -2, 0, -2, 0, -2, 2, 0] := by
  have h0 : value φ [0, 2, 0, -2, 0, -2, 0, -2, 2, 0] = value φ [2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2] :=
    overlap (eq422 h) (eq1 h) [2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2] [0] (by decide)
  have hl : value φ [0, 2, 0, -2, 0, -2, 0, -2, 2, 0] = value φ [0, 2, 0, -2, 0, -2, 0, -2, 2, 0] := rfl
  have hr : value φ [2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2] = value φ [2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq428 (h : Relations φ) : value φ [2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0] = value φ [0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2] := by
  have h0 : value φ [2, 0, 2, -2, 0, -2, 0, -2, 2, 2, 0, 2, 0] = value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, 0, 2, 0, 2, 0, 2] :=
    overlap (eq7 h) (eq4 h) [0, 2, -2, 0, -2, 0, -2, 2, 0] [2, 0, 2, 0] (by decide)
  have hl : value φ [2, 0, 2, -2, 0, -2, 0, -2, 2, 2, 0, 2, 0] = value φ [2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0] :=
    ((in_context (eq2 h) [2, 0, 2, -2, 0, -2, 0, -2] [0, 2, 0]).trans (in_context (eq5 h) [2, 0, 2] [2, 0]))
  have hr : value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, 0, 2, 0, 2, 0, 2] = value φ [0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2] :=
    ((in_context (eq1 h) [0, 2, -2, 0, -2, 0, -2, 2] [2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [0, 2, -2, 0, -2, 0, -2] [0, 2, 0, 2]).trans (in_context (eq5 h) [0, 2] [2, 0, 2])))
  exact hl.symm.trans (h0.trans hr)

private theorem eq429 (h : Relations φ) : value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, 2, 0] = value φ [0, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2] := by
  have h0 : value φ [0, 2, 0, 2, 0, 2, 2, -2, 0, -2, 0, -2, 2] = value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, 2, 0] :=
    overlap (eq4 h) (eq13 h) [2, 0] [2, -2, 0, -2, 0, -2, 2] (by decide)
  have hl : value φ [0, 2, 0, 2, 0, 2, 2, -2, 0, -2, 0, -2, 2] = value φ [0, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2] :=
    (in_context (eq2 h) [0, 2, 0, 2, 0] [-2, 0, -2, 0, -2, 2])
  have hr : value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, 2, 0] = value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, 2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq430 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0] = value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2] := by
  have h0 : value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0] :=
    overlap (eq425 h) (eq0 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0] [-2] (by decide)
  have hl : value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2] = value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2] := rfl
  have hr : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq431 (h : Relations φ) : value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2] := by
  have h0 : value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0] :=
    overlap (eq426 h) (eq0 h) [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0] [-2] (by decide)
  have hl : value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2] := rfl
  have hr : value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0] = value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq432 (h : Relations φ) : value φ [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [2, -2, 2, -2, 0, 2, 0, 2, -2, 0, -2, 0] := by
  have h0 : value φ [2, -2, 2, -2, 2, 2, 0, 2, 0, 2, -2, 0, -2, 0] = value φ [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] :=
    overlap (eq3 h) (eq10 h) [-2, 2, -2, 2] [2, 0, 2, 0, 2, -2, 0, -2, 0] (by decide)
  have hl : value φ [2, -2, 2, -2, 2, 2, 0, 2, 0, 2, -2, 0, -2, 0] = value φ [2, -2, 2, -2, 0, 2, 0, 2, -2, 0, -2, 0] :=
    (in_context (eq2 h) [2, -2, 2, -2] [0, 2, 0, 2, -2, 0, -2, 0])
  have hr : value φ [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq433 (h : Relations φ) : value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] = value φ [-2, 0, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2] := by
  have h0 : value φ [-2, 0, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2] = value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] :=
    overlap (eq13 h) (eq3 h) [2, 0, 2, 0, 2, -2, 0, -2, 0] [-2, 2, -2] (by decide)
  have hl : value φ [-2, 0, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2] = value φ [-2, 0, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2] := rfl
  have hr : value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] = value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq434 (h : Relations φ) : value φ [-2, 2, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0] := by
  have h0 : value φ [2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0] = value φ [-2, 2, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] :=
    overlap (eq3 h) (eq8 h) [-2, 2, -2] [0, -2, 0, -2, 2, 0, 2, 0] (by decide)
  have hl : value φ [2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0] = value φ [2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0] := rfl
  have hr : value φ [-2, 2, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [-2, 2, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq435 (h : Relations φ) : value φ [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2] = value φ [2, -2, 2, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2] := by
  have h0 : value φ [2, -2, 2, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2] = value φ [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2] :=
    overlap (eq432 h) (eq0 h) [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2] [-2] (by decide)
  have hl : value φ [2, -2, 2, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2] = value φ [2, -2, 2, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2] := rfl
  have hr : value φ [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2] = value φ [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq452 (h : Relations φ) : value φ [2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] = value φ [0, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2] := by
  have h0 : value φ [0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2, 2, -2, 2, -2] = value φ [2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] :=
    overlap (eq46 h) (eq3 h) [2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0] [2, -2, 2, -2] (by decide)
  have hl : value φ [0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2, 2, -2, 2, -2] = value φ [0, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2] :=
    ((in_context (eq2 h) [0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2] [-2, 2, -2]).trans ((in_context (eq0 h) [0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2] [2, -2]).trans (in_context (eq2 h) [0, 2, -2, 2, 0, -2, 0, -2, 2, 0] [-2])))
  have hr : value φ [2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] = value φ [2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq494 (h : Relations φ) : value φ [2, 0, 2, 0, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] = value φ [0, 2, 0, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2] := by
  have h0 : value φ [0, 2, 0, 2, 0, 2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2] = value φ [2, 0, 2, 0, 2, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] :=
    overlap (eq4 h) (eq43 h) [2, 0, 2, 0, 2] [2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2] (by decide)
  have hl : value φ [0, 2, 0, 2, 0, 2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2] = value φ [0, 2, 0, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2] :=
    ((in_context (eq2 h) [0, 2, 0, 2, 0] [0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2]).trans ((in_context (eq1 h) [0, 2, 0, 2] [2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2]).trans (in_context (eq2 h) [0, 2, 0] [-2, 2, 0, -2, 0, -2, 2, 0, 2, -2])))
  have hr : value φ [2, 0, 2, 0, 2, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] = value φ [2, 0, 2, 0, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] :=
    (in_context (eq2 h) [2, 0, 2, 0] [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq530 (h : Relations φ) : value φ [2, 0, 2, -2, 0, -2, 0, 2, -2, 0, 2, 0, 2, 0, 2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 0] := by
  have h0 : value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 0] = value φ [2, 0, 2, -2, 0, -2, 0, 2, -2, 0, 2, 0, 2, 0, 2] :=
    overlap (eq14 h) (eq4 h) [2, 0, 2, -2, 0, -2, 0, 2, -2] [0] (by decide)
  have hl : value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 0] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 0] := rfl
  have hr : value φ [2, 0, 2, -2, 0, -2, 0, 2, -2, 0, 2, 0, 2, 0, 2] = value φ [2, 0, 2, -2, 0, -2, 0, 2, -2, 0, 2, 0, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq584 (h : Relations φ) : value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, 0] = value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 0, 2, 0, 2] := by
  have h0 : value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 2, 0, 2, 0] = value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 0, 2, 0, 2, 0, 2] :=
    overlap (eq16 h) (eq4 h) [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0] [2, 0, 2, 0] (by decide)
  have hl : value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 2, 0, 2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, 0] :=
    (in_context (eq2 h) [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2] [0, 2, 0])
  have hr : value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 0, 2, 0, 2, 0, 2] = value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 0, 2, 0, 2] :=
    ((in_context (eq1 h) [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2] [2, 0, 2, 0, 2]).trans (in_context (eq2 h) [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2] [0, 2, 0, 2]))
  exact hl.symm.trans (h0.trans hr)

private theorem eq588 (h : Relations φ) : value φ [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2] = value φ [-2, 0, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2] := by
  have h0 : value φ [0, -2, 0, -2, 0, -2, -2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2] = value φ [-2, 0, -2, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2] :=
    overlap (eq5 h) (eq26 h) [-2, 0, -2] [-2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2] (by decide)
  have hl : value φ [0, -2, 0, -2, 0, -2, -2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2] = value φ [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2] :=
    (in_context (eq0 h) [0, -2, 0, -2, 0] [2, -2, 2, 0, 2, -2, 0, -2, 0, 2])
  have hr : value φ [-2, 0, -2, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [-2, 0, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2] :=
    (in_context (eq0 h) [-2, 0] [2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2])
  exact hl.symm.trans (h0.trans hr)

private theorem eq594 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, 0, -2, 0] = value φ [2, 0, -2, 0, -2, 2, 0, 2, -2, 2, 0, -2, 0, -2] := by
  have h0 : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2, -2, 0, -2, 0] = value φ [2, 0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0, 0, -2, 0, -2, 0, -2] :=
    overlap (eq53 h) (eq5 h) [2, 0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0] [-2, 0, -2, 0] (by decide)
  have hl : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2, -2, 0, -2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, 0, -2, 0] :=
    (in_context (eq0 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] [0, -2, 0])
  have hr : value φ [2, 0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0, 0, -2, 0, -2, 0, -2] = value φ [2, 0, -2, 0, -2, 2, 0, 2, -2, 2, 0, -2, 0, -2] :=
    ((in_context (eq1 h) [2, 0, -2, 0, -2, 2, 0, 2, -2, 2, -2] [-2, 0, -2, 0, -2]).trans (in_context (eq0 h) [2, 0, -2, 0, -2, 2, 0, 2, -2, 2] [0, -2, 0, -2]))
  exact hl.symm.trans (h0.trans hr)

private theorem eq610 (h : Relations φ) : value φ [0, 2, 0, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] = value φ [2, 0, 2, 0, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2] := by
  have h0 : value φ [0, 2, 0, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] = value φ [2, 0, 2, 0, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2] :=
    overlap (eq2 h) (eq494 h) [2] [0, 2, 0, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] (by decide)
  have hl : value φ [0, 2, 0, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] = value φ [0, 2, 0, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] := rfl
  have hr : value φ [2, 0, 2, 0, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2] = value φ [2, 0, 2, 0, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq664 (h : Relations φ) : value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] := by
  have h0 : value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 2, -2, 0, -2, 0] = value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] :=
    overlap (eq16 h) (eq10 h) [-2, 2, 0, 2, -2, 0, -2, 0, 2] [2, -2, 0, -2, 0] (by decide)
  have hl : value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 2, -2, 0, -2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] :=
    ((in_context (eq2 h) [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2] [-2, 0, -2, 0]).trans ((in_context (eq0 h) [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] [0, -2, 0]).trans (in_context (eq1 h) [2, -2, 0, -2, 0, -2, 2, -2, 0, 2] [-2, 0])))
  have hr : value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq675 (h : Relations φ) : value φ [0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0] := by
  have h0 : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 0, 2, 0, 2, 0] = value φ [0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2] :=
    overlap (eq83 h) (eq4 h) [0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2] [0, 2, 0, 2, 0] (by decide)
  have hl : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 0, 2, 0, 2, 0] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0] :=
    ((in_context (eq1 h) [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] [2, 0, 2, 0]).trans ((in_context (eq2 h) [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] [0, 2, 0]).trans (in_context (eq1 h) [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2] [2, 0])))
  have hr : value φ [0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2] = value φ [0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq686 (h : Relations φ) : value φ [2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] := by
  have h0 : value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, -2, 0, -2, 0] = value φ [2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] :=
    overlap (eq14 h) (eq10 h) [2, 0, 2, -2, 0, -2, 0, 2] [-2, 0, -2, 0] (by decide)
  have hl : value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, -2, 0, -2, 0] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] :=
    ((in_context (eq0 h) [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] [0, -2, 0]).trans (in_context (eq1 h) [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] [-2, 0]))
  have hr : value φ [2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq695 (h : Relations φ) : value φ [-2, 0, -2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] = value φ [0, -2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2] := by
  have h0 : value φ [0, -2, 0, -2, 0, -2, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2] = value φ [-2, 0, -2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] :=
    overlap (eq5 h) (eq55 h) [-2, 0, -2, 0, -2] [-2, 0, -2, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2] (by decide)
  have hl : value φ [0, -2, 0, -2, 0, -2, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2] = value φ [0, -2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2] :=
    ((in_context (eq0 h) [0, -2, 0, -2, 0] [0, -2, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq1 h) [0, -2, 0, -2] [-2, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2]).trans (in_context (eq0 h) [0, -2, 0] [2, 0, 2, -2, 2, -2, 0, -2, 0, -2])))
  have hr : value φ [-2, 0, -2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] = value φ [-2, 0, -2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq733 (h : Relations φ) : value φ [0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] := by
  have h0 : value φ [2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 0, -2, 0] = value φ [0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] :=
    overlap (eq66 h) (eq10 h) [0, 2, -2, 0, -2, 0, 2] [0, -2, 0] (by decide)
  have hl : value φ [2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 0, -2, 0] = value φ [2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] :=
    (in_context (eq1 h) [2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] [-2, 0])
  have hr : value φ [0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq769 (h : Relations φ) : value φ [2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 2] := by
  have h0 : value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, -2, 0, -2, 0, -2, 2] = value φ [2, 0, 2, -2, 0, -2, 0, 2, -2, -2, 0, -2, 0, -2, 2, 0, 2, 0] :=
    overlap (eq14 h) (eq13 h) [2, 0, 2, -2, 0, -2, 0, 2, -2] [-2, 0, -2, 0, -2, 2] (by decide)
  have hl : value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, -2, 0, -2, 0, -2, 2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 2] :=
    ((in_context (eq0 h) [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] [0, -2, 0, -2, 2]).trans (in_context (eq1 h) [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] [-2, 0, -2, 2]))
  have hr : value φ [2, 0, 2, -2, 0, -2, 0, 2, -2, -2, 0, -2, 0, -2, 2, 0, 2, 0] = value φ [2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0] :=
    (in_context (eq0 h) [2, 0, 2, -2, 0, -2, 0, 2] [0, -2, 0, -2, 2, 0, 2, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq844 (h : Relations φ) : value φ [0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2] = value φ [2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2] := by
  have h0 : value φ [2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2] = value φ [0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2] :=
    overlap (eq733 h) (eq0 h) [0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2] [-2] (by decide)
  have hl : value φ [2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2] = value φ [2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2] := rfl
  have hr : value φ [0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2] = value φ [0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq862 (h : Relations φ) : value φ [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, 0, -2, 0] = value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2] := by
  have h0 : value φ [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, 0, -2, 0] = value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 0, -2, 0, -2, 0, -2] :=
    overlap (eq35 h) (eq5 h) [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0] [0, -2, 0] (by decide)
  have hl : value φ [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, 0, -2, 0] = value φ [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, 0, -2, 0] := rfl
  have hr : value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 0, -2, 0, -2, 0, -2] = value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2] :=
    (in_context (eq1 h) [2, 0, -2, 2, 0, 2, 0, 2, -2, 2] [-2, 0, -2, 0, -2])
  exact hl.symm.trans (h0.trans hr)

private theorem eq863 (h : Relations φ) : value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0] = value φ [-2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2] := by
  have h0 : value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, -2, -2, 2, 0, -2, 0, -2, 2, 0] = value φ [-2, 0, -2, 0, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2] :=
    overlap (eq9 h) (eq39 h) [-2, 0, -2, 0] [-2, 2, 0, -2, 0, -2, 2, 0] (by decide)
  have hl : value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, -2, -2, 2, 0, -2, 0, -2, 2, 0] = value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0] :=
    (in_context (eq0 h) [2, 0, 2, 0, 2, -2, 0, -2, 0] [2, 0, -2, 0, -2, 2, 0])
  have hr : value φ [-2, 0, -2, 0, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2] = value φ [-2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2] :=
    (in_context (eq1 h) [-2, 0, -2] [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2])
  exact hl.symm.trans (h0.trans hr)

private theorem eq880 (h : Relations φ) : value φ [0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, 2, 0] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, 0, 2] := by
  have h0 : value φ [0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, 2, 0] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 0, 2, 0, 2, 0, 2] :=
    overlap (eq82 h) (eq4 h) [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] [0, 2, 0] (by decide)
  have hl : value φ [0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, 2, 0] = value φ [0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, 2, 0] := rfl
  have hr : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 0, 2, 0, 2, 0, 2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, 0, 2] :=
    (in_context (eq1 h) [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2] [2, 0, 2, 0, 2])
  exact hl.symm.trans (h0.trans hr)

private theorem eq893 (h : Relations φ) : value φ [2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2, 0] := by
  have h0 : value φ [2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2, 0] :=
    overlap (eq3 h) (eq117 h) [-2, 2] [0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2] (by decide)
  have hl : value φ [2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2] = value φ [2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2] := rfl
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2, 0] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq998 (h : Relations φ) : value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 2] = value φ [-2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0] := by
  have h0 : value φ [-2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 2, 0] = value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 2] :=
    overlap (eq863 h) (eq769 h) [2, 0] [2, 0] (by decide)
  have hl : value φ [-2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 2, 0] = value φ [-2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0] :=
    (in_context (eq2 h) [-2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2] [0])
  have hr : value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 2] = value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1019 (h : Relations φ) : value φ [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] = value φ [0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2] := by
  have h0 : value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] :=
    overlap (eq10 h) (eq686 h) [-2, 2, 0] [2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] (by decide)
  have hl : value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2] :=
    ((in_context (eq37 h) [0, -2] [0, 2, 0, 2, -2]).trans ((in_context (eq1 h) [0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2] [2, 0, 2, -2]).trans (in_context (eq2 h) [0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2] [0, 2, -2])))
  have hr : value φ [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] = value φ [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1024 (h : Relations φ) : value φ [-2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] = value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2] := by
  have h0 : value φ [-2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 2, 0, 2] = value φ [2, 0, 2, 2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2] :=
    overlap (eq863 h) (eq844 h) [2, 0, 2] [2, 0, 2] (by decide)
  have hl : value φ [-2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 2, 0, 2] = value φ [-2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] :=
    (in_context (eq2 h) [-2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2] [0, 2])
  have hr : value φ [2, 0, 2, 2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2] = value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2] :=
    (in_context (eq2 h) [2, 0] [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2])
  exact hl.symm.trans (h0.trans hr)

private theorem eq1032 (h : Relations φ) : value φ [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2] = value φ [2, 0, 2, 0, 2, -2, 2, -2, 2, 0] := by
  have h0 : value φ [2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 0, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2] :=
    overlap (eq40 h) (eq6 h) [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2] [0, 2, -2, 0, -2, 0, -2, 2, 0] (by decide)
  have hl : value φ [2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 0, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [2, 0, 2, 0, 2, -2, 2, -2, 2, 0] :=
    ((in_context (eq1 h) [2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2] [2, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq2 h) [2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2] [-2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq0 h) [2, 0, 2, 0, 2, -2, 2, 0, -2, 0] [0, -2, 0, -2, 2, 0]).trans ((in_context (eq1 h) [2, 0, 2, 0, 2, -2, 2, 0, -2] [-2, 0, -2, 2, 0]).trans ((in_context (eq0 h) [2, 0, 2, 0, 2, -2, 2, 0] [0, -2, 2, 0]).trans (in_context (eq1 h) [2, 0, 2, 0, 2, -2, 2] [-2, 2, 0]))))))
  have hr : value φ [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2] = value φ [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1047 (h : Relations φ) : value φ [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 2] := by
  have h0 : value φ [-2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 2, 0, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0] :=
    overlap (eq86 h) (eq434 h) [2, 0, -2, 0, 2, -2, 0, -2, 0] [0, 2, -2, 0, -2, 0, -2, 2] (by decide)
  have hl : value φ [-2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 2, 0, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 2] :=
    ((in_context (eq1 h) [-2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 2] [2, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq2 h) [-2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2] [-2, 0, -2, 0, -2, 2]).trans ((in_context (eq0 h) [-2, 2, 0, 2, 0, 2, -2, 2, -2, 0] [0, -2, 0, -2, 2]).trans ((in_context (eq1 h) [-2, 2, 0, 2, 0, 2, -2, 2, -2] [-2, 0, -2, 2]).trans (in_context (eq0 h) [-2, 2, 0, 2, 0, 2, -2, 2] [0, -2, 2])))))
  have hr : value φ [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0] = value φ [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1051 (h : Relations φ) : value φ [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] := by
  have h0 : value φ [2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, 0, -2, 2, 0, 2, 0, 2, -2, 0] = value φ [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2] :=
    overlap (eq31 h) (eq12 h) [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0] [0, -2, 2, 0, 2, 0, 2, -2, 0] (by decide)
  have hl : value φ [2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, 0, -2, 2, 0, 2, 0, 2, -2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] :=
    ((in_context (eq1 h) [2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2] [-2, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq0 h) [2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2] [2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq2 h) [2, -2, 0, -2, 0, -2, 2, -2, 2, 0] [0, 2, 0, 2, -2, 0]).trans ((in_context (eq1 h) [2, -2, 0, -2, 0, -2, 2, -2, 2] [2, 0, 2, -2, 0]).trans (in_context (eq2 h) [2, -2, 0, -2, 0, -2, 2, -2] [0, 2, -2, 0])))))
  have hr : value φ [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2] :=
    (in_context (eq1 h) [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] [-2, 2, 0, 2, 0, 2, -2, 0, -2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1052 (h : Relations φ) : value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2] = value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0] := by
  have h0 : value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, -2, 0, -2, 0, -2, 2, 0] = value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2] :=
    overlap (eq36 h) (eq6 h) [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2] [-2, 0, -2, 0, -2, 2, 0] (by decide)
  have hl : value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, -2, 0, -2, 0, -2, 2, 0] = value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0] :=
    ((in_context (eq0 h) [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0] [0, -2, 0, -2, 2, 0]).trans ((in_context (eq1 h) [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2] [-2, 0, -2, 2, 0]).trans ((in_context (eq0 h) [0, -2, 2, 0, 2, 0, 2, -2, 2, 0] [0, -2, 2, 0]).trans (in_context (eq1 h) [0, -2, 2, 0, 2, 0, 2, -2, 2] [-2, 2, 0]))))
  have hr : value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2] = value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1054 (h : Relations φ) : value φ [2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0] := by
  have h0 : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, -2, 0, -2, 2, 0, 2, 0] = value φ [2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] :=
    overlap (eq49 h) (eq8 h) [2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2] [-2, 0, -2, 2, 0, 2, 0] (by decide)
  have hl : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, -2, 0, -2, 2, 0, 2, 0] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0] :=
    ((in_context (eq0 h) [0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0] [0, -2, 2, 0, 2, 0]).trans ((in_context (eq1 h) [0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2] [-2, 2, 0, 2, 0]).trans ((in_context (eq0 h) [0, 2, 0, 2, -2, 0, 2, 0, -2, 2] [2, 0, 2, 0]).trans (in_context (eq2 h) [0, 2, 0, 2, -2, 0, 2, 0, -2] [0, 2, 0]))))
  have hr : value φ [2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1060 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2] = value φ [0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2] := by
  have h0 : value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, -2, -2, 2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2] :=
    overlap (eq10 h) (eq103 h) [-2, 2, 0, 2, 0, 2, -2, 0] [-2, 2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2] (by decide)
  have hl : value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, -2, -2, 2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2] = value φ [0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2] :=
    ((in_context (eq0 h) [0, -2, 0, -2, 2, 0, 2, 0, 2] [2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq2 h) [0, -2, 0, -2, 2, 0, 2, 0] [0, 2, 0, -2, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq1 h) [0, -2, 0, -2, 2, 0, 2] [2, 0, -2, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq2 h) [0, -2, 0, -2, 2, 0] [0, -2, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq1 h) [0, -2, 0, -2, 2] [-2, 2, -2, 0, -2, 0, -2]).trans (in_context (eq3 h) [0, -2, 0] [0, -2, 0, -2]))))))
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1159 (h : Relations φ) : value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2] = value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2] := by
  have h0 : value φ [0, -2, 2, 0, 2, 0, 2, -2, 0, -2, -2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [-2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2] :=
    overlap (eq12 h) (eq14 h) [-2, 0, -2, 2, 0] [-2, 0, 2, -2, 2, 0, 2, 0, 2] (by decide)
  have hl : value φ [0, -2, 2, 0, 2, 0, 2, -2, 0, -2, -2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2] :=
    ((in_context (eq0 h) [0, -2, 2, 0, 2, 0, 2, -2, 0] [0, 2, -2, 2, 0, 2, 0, 2]).trans (in_context (eq1 h) [0, -2, 2, 0, 2, 0, 2, -2] [2, -2, 2, 0, 2, 0, 2]))
  have hr : value φ [-2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2] = value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2] :=
    (in_context (eq1024 h) [] [0, -2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1225 (h : Relations φ) : value φ [2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, 0, 2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0] := by
  have h0 : value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 0, -2, 0, -2, 0, -2] = value φ [2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, 0, 2] :=
    overlap (eq530 h) (eq425 h) [2, 0, 2, -2, 0, -2, 0, 2] [-2, 0, -2, 0, -2] (by decide)
  have hl : value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 0, -2, 0, -2, 0, -2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0] :=
    ((in_context (eq5 h) [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] [-2]).trans ((in_context (eq1 h) [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] [-2, 0, -2, 0, -2, -2]).trans (in_context (eq0 h) [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0] [])))
  have hr : value φ [2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, 0, 2] = value φ [2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1245 (h : Relations φ) : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0] = value φ [0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2] := by
  have h0 : value φ [0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0] :=
    overlap (eq42 h) (eq998 h) [2, -2, 0] [0, 2, -2, 0, -2, 2] (by decide)
  have hl : value φ [0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2] = value φ [0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2] :=
    ((in_context (eq11 h) [0, 2, 0, 2, -2, 2] [-2, 2]).trans (in_context (eq0 h) [0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0] [2]))
  have hr : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1255 (h : Relations φ) : value φ [-2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2] = value φ [2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0] := by
  have h0 : value φ [2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0] = value φ [-2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2] :=
    overlap (eq28 h) (eq6 h) [-2, 0, -2, 0, -2, 2, -2] [-2, 2, 0] (by decide)
  have hl : value φ [2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0] = value φ [2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0] := rfl
  have hr : value φ [-2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2] = value φ [-2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1258 (h : Relations φ) : value φ [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2] = value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2] := by
  have h0 : value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 0, -2, 0, -2, 2, 0, 2, 0, 2] = value φ [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2] :=
    overlap (eq34 h) (eq9 h) [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2] [0, -2, 0, -2, 2, 0, 2, 0, 2] (by decide)
  have hl : value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 0, -2, 0, -2, 2, 0, 2, 0, 2] = value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2] :=
    ((in_context (eq1 h) [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2] [-2, 0, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq0 h) [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0] [0, -2, 2, 0, 2, 0, 2]).trans (in_context (eq1 h) [2, 0, -2, 2, 0, 2, 0, 2, -2, 2] [-2, 2, 0, 2, 0, 2])))
  have hr : value φ [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2] = value φ [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2] :=
    ((in_context (eq2 h) [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0] [0, 2, 0, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq1 h) [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2] [2, 0, 2, -2, 0, -2, 0, -2]).trans (in_context (eq2 h) [0, -2, 2, -2, 0, -2, 0, -2, 2, -2] [0, 2, -2, 0, -2, 0, -2])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1270 (h : Relations φ) : value φ [2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] = value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2] := by
  have h0 : value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, 2, 2, -2, 2, -2, 0, -2, 0, -2] = value φ [2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] :=
    overlap (eq6 h) (eq55 h) [2, 0, 2, -2] [2, -2, 2, -2, 0, -2, 0, -2] (by decide)
  have hl : value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, 2, 2, -2, 2, -2, 0, -2, 0, -2] = value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2] :=
    (in_context (eq2 h) [0, 2, -2, 0, -2, 0, -2, 2, 0] [-2, 2, -2, 0, -2, 0, -2])
  have hr : value φ [2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] = value φ [2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1284 (h : Relations φ) : value φ [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0, -2] = value φ [0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2, 0, -2, 0] := by
  have h0 : value φ [0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2, 0, -2, 0] = value φ [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0, -2] :=
    overlap (eq81 h) (eq5 h) [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2] [0, -2, 0] (by decide)
  have hl : value φ [0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2, 0, -2, 0] = value φ [0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2, 0, -2, 0] := rfl
  have hr : value φ [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0, -2] = value φ [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1309 (h : Relations φ) : value φ [-2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2] = value φ [0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] := by
  have h0 : value φ [0, -2, 2, 0, 2, 0, 2, -2, 0, -2, -2, 2, -2, 2, 0, 2, 0, 2] = value φ [-2, 0, -2, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2] :=
    overlap (eq12 h) (eq116 h) [-2, 0, -2, 2] [-2, 2, -2, 2, 0, 2, 0, 2] (by decide)
  have hl : value φ [0, -2, 2, 0, 2, 0, 2, -2, 0, -2, -2, 2, -2, 2, 0, 2, 0, 2] = value φ [0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] :=
    (in_context (eq0 h) [0, -2, 2, 0, 2, 0, 2, -2, 0] [2, -2, 2, 0, 2, 0, 2])
  have hr : value φ [-2, 0, -2, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2] = value φ [-2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2] :=
    (in_context (eq3 h) [-2, 0] [0, -2, 0, -2, 2, 0, -2, 0, 2, -2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1311 (h : Relations φ) : value φ [2, -2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, -2, 2, 0, 2] = value φ [-2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0] := by
  have h0 : value φ [-2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2, 0, 0, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [2, -2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2] :=
    overlap (eq120 h) (eq6 h) [2, -2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0] [0, 2, -2, 0, -2, 0, -2, 2, 0] (by decide)
  have hl : value φ [-2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2, 0, 0, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [-2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0] :=
    ((in_context (eq1 h) [-2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2] [2, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq2 h) [-2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2] [-2, 0, -2, 0, -2, 2, 0]).trans (in_context (eq0 h) [-2, 0, -2, 0, -2, 2, 0, -2, 0, 2] [0, -2, 0, -2, 2, 0])))
  have hr : value φ [2, -2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2] = value φ [2, -2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, -2, 2, 0, 2] :=
    ((in_context (eq1 h) [2, -2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2] [2, -2, 0, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq2 h) [2, -2, 0, 2, 0, 2, -2, 0, -2, 2, -2] [-2, 0, -2, 0, -2, 2, 0, 2]).trans (in_context (eq0 h) [2, -2, 0, 2, 0, 2, -2, 0, -2, 2] [0, -2, 0, -2, 2, 0, 2])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1391 (h : Relations φ) : value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2] = value φ [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2] := by
  have h0 : value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2] = value φ [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2] :=
    overlap (eq10 h) (eq14 h) [-2, 2, 0] [2, -2, 2, 0, 2, 0, 2] (by decide)
  have hl : value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2] = value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2] := rfl
  have hr : value φ [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2] = value φ [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq1396 (h : Relations φ) : value φ [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] := by
  have h0 : value φ [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 0, -2, 2, 0, 2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] :=
    overlap (eq30 h) (eq8 h) [2, -2, 0, -2, 0, -2, 2, -2, 2, 0] [0, -2, 2, 0, 2, 0] (by decide)
  have hl : value φ [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 0, -2, 2, 0, 2, 0] = value φ [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0] :=
    (in_context (eq1 h) [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] [-2, 2, 0, 2, 0])
  have hr : value φ [2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] :=
    ((in_context (eq1 h) [2, -2, 0, -2, 0, -2, 2, -2, 2] [2, 0, 2, -2, 0, -2, 0, -2, 2]).trans (in_context (eq2 h) [2, -2, 0, -2, 0, -2, 2, -2] [0, 2, -2, 0, -2, 0, -2, 2]))
  exact hl.symm.trans (h0.trans hr)

private theorem eq1398 (h : Relations φ) : value φ [0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0] = value φ [2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2] := by
  have h0 : value φ [0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0] = value φ [2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2] :=
    overlap (eq4 h) (eq33 h) [2, 0, 2] [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0] (by decide)
  have hl : value φ [0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0] = value φ [0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0] := rfl
  have hr : value φ [2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2] = value φ [2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq1422 (h : Relations φ) : value φ [0, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] = value φ [-2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 2] := by
  have h0 : value φ [0, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] = value φ [-2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 2] :=
    overlap (eq5 h) (eq84 h) [-2, 0, -2] [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] (by decide)
  have hl : value φ [0, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] = value φ [0, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] := rfl
  have hr : value φ [-2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 2] = value φ [-2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq1426 (h : Relations φ) : value φ [2, 0, 2, -2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 2] = value φ [0, 2, -2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2] := by
  have h0 : value φ [2, 0, 2, -2, 0, -2, 0, -2, 2, 2, -2, 2, -2, 0, -2, 2, 0, 2, 0, -2, 2] = value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, 0, 2, -2, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2] :=
    overlap (eq7 h) (eq93 h) [0, 2, -2, 0, -2, 0, -2, 2, 0] [2, -2, 2, -2, 0, -2, 2, 0, 2, 0, -2, 2] (by decide)
  have hl : value φ [2, 0, 2, -2, 0, -2, 0, -2, 2, 2, -2, 2, -2, 0, -2, 2, 0, 2, 0, -2, 2] = value φ [2, 0, 2, -2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 2] :=
    ((in_context (eq2 h) [2, 0, 2, -2, 0, -2, 0, -2] [-2, 2, -2, 0, -2, 2, 0, 2, 0, -2, 2]).trans (in_context (eq0 h) [2, 0, 2, -2, 0, -2, 0] [2, -2, 0, -2, 2, 0, 2, 0, -2, 2]))
  have hr : value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, 0, 2, -2, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2] = value φ [0, 2, -2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2] :=
    ((in_context (eq1 h) [0, 2, -2, 0, -2, 0, -2, 2] [2, -2, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq2 h) [0, 2, -2, 0, -2, 0, -2] [-2, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2]).trans (in_context (eq0 h) [0, 2, -2, 0, -2, 0] [2, 0, -2, 0, 2, -2, 0, -2, 0, -2])))
  exact hl.symm.trans (h0.trans hr)

private theorem eq1513 (h : Relations φ) : value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0, 2, 0, 2] = value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2, 0] := by
  have h0 : value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2] = value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0] :=
    overlap (eq1052 h) (eq427 h) [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] [0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2] (by decide)
  have hl : value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2] = value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0, 2, 0, 2] :=
    ((in_context (eq1 h) [0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2] [2, 0, -2, 0, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq2 h) [0, -2, 2, 0, 2, 0, 2, -2, 2, -2] [0, -2, 0, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq5 h) [0, -2, 2, 0, 2, 0, 2, -2, 2] [-2, 2, 0, 2]).trans (in_context (eq0 h) [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0] [2, 0, 2]))))
  have hr : value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0] = value φ [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2, 0] :=
    ((in_context (eq1 h) [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] [2, 0, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq2 h) [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2] [0, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq5 h) [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] [-2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq0 h) [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 0, -2, 0] [0, -2, 0, -2, 2, 0]).trans ((in_context (eq1 h) [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 0, -2] [-2, 0, -2, 2, 0]).trans ((in_context (eq0 h) [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 0] [0, -2, 2, 0]).trans ((in_context (eq1 h) [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2] [-2, 2, 0]).trans (in_context (eq0 h) [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] [2, 0]))))))))
  exact hl.symm.trans (h0.trans hr)

private theorem eq1514 (h : Relations φ) : value φ [0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2] = value φ [-2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2] := by
  have h0 : value φ [0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, -2, 0, -2] = value φ [-2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2] :=
    overlap (eq1019 h) (eq1159 h) [-2] [-2, 0, -2] (by decide)
  have hl : value φ [0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, -2, 0, -2] = value φ [0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2] :=
    (in_context (eq0 h) [0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] [0, -2])
  have hr : value φ [-2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2] = value φ [-2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq1520 (h : Relations φ) : value φ [0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2, 0, -2, 0, -2] = value φ [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0] := by
  have h0 : value φ [0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2, 0, -2, 0, -2] = value φ [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0] :=
    overlap (eq1284 h) (eq0 h) [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0] [-2] (by decide)
  have hl : value φ [0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2, 0, -2, 0, -2] = value φ [0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2, 0, -2, 0, -2] := rfl
  have hr : value φ [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0] = value φ [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq1524 (h : Relations φ) : value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0] = value φ [2, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2] := by
  have h0 : value φ [2, -2, 2, -2, 2, 2, -2, 2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0] :=
    overlap (eq3 h) (eq169 h) [-2, 2, -2] [2, -2, 2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2] (by decide)
  have hl : value φ [2, -2, 2, -2, 2, 2, -2, 2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2] = value φ [2, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2] :=
    ((in_context (eq2 h) [2, -2, 2, -2] [-2, 2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2]).trans ((in_context (eq0 h) [2, -2, 2] [2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2]).trans (in_context (eq2 h) [2, -2] [0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2])))
  have hr : value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1553 (h : Relations φ) : value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] := by
  have h0 : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] = value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2] :=
    overlap (eq424 h) (eq12 h) [0, -2, 0, -2, 0, 2, 0, 2, 0, 2] [2, 0, 2, 0, 2, -2, 0] (by decide)
  have hl : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] := rfl
  have hr : value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2] :=
    ((in_context (eq4 h) [0, -2, 0, -2, 0] [-2, 2, 0, 2, 0, 2, -2, 0, -2]).trans (in_context (eq1 h) [0, -2, 0, -2] [2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1573 (h : Relations φ) : value φ [-2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0] = value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2] := by
  have h0 : value φ [2, -2, 2, -2, 2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2] = value φ [-2, 2, -2, 2, 2, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0] :=
    overlap (eq3 h) (eq267 h) [-2, 2, -2, 2] [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2] (by decide)
  have hl : value φ [2, -2, 2, -2, 2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2] = value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2] :=
    ((in_context (eq2 h) [2, -2, 2, -2] [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2]).trans (in_context (eq0 h) [2, -2, 2] [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2]))
  have hr : value φ [-2, 2, -2, 2, 2, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0] = value φ [-2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0] :=
    ((in_context (eq2 h) [-2, 2, -2] [-2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0]).trans (in_context (eq0 h) [-2, 2] [0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1574 (h : Relations φ) : value φ [-2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2] = value φ [2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0] := by
  have h0 : value φ [2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0] = value φ [-2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2] :=
    overlap (eq0 h) (eq1573 h) [-2] [2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0] (by decide)
  have hl : value φ [2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0] = value φ [2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0] := rfl
  have hr : value φ [-2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2] = value φ [-2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1577 (h : Relations φ) : value φ [2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] = value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2] := by
  have h0 : value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, -2, 2, 2, -2, 2, -2] = value φ [2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, 2, -2, 2, -2, 2] :=
    overlap (eq292 h) (eq3 h) [2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2] [2, -2, 2, -2] (by decide)
  have hl : value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, -2, 2, 2, -2, 2, -2] = value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2] :=
    ((in_context (eq2 h) [0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, -2] [-2, 2, -2]).trans (in_context (eq0 h) [0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0] [2, -2]))
  have hr : value φ [2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, 2, -2, 2, -2, 2] = value φ [2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] :=
    ((in_context (eq2 h) [2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2] [-2, 2, -2, 2]).trans (in_context (eq0 h) [2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] [2, -2, 2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1578 (h : Relations φ) : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2] = value φ [0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] := by
  have h0 : value φ [0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] = value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2] :=
    overlap (eq2 h) (eq1577 h) [2] [0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] (by decide)
  have hl : value φ [0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] = value φ [0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] := rfl
  have hr : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2] = value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1580 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0] = value φ [2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2] := by
  have h0 : value φ [2, -2, 2, -2, 2, 2, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2] = value φ [-2, 2, -2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0] :=
    overlap (eq3 h) (eq316 h) [-2, 2, -2] [2, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2] (by decide)
  have hl : value φ [2, -2, 2, -2, 2, 2, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2] = value φ [2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2] :=
    ((in_context (eq2 h) [2, -2, 2, -2] [-2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2]).trans (in_context (eq0 h) [2, -2, 2] [0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2]))
  have hr : value φ [-2, 2, -2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0] :=
    (in_context (eq0 h) [-2, 2] [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1583 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0] := by
  have h0 : value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2] :=
    overlap (eq425 h) (eq12 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0] [0, -2, 2, 0, 2, 0, 2, -2, 0] (by decide)
  have hl : value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0] = value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0] :=
    ((in_context (eq4 h) [0, -2, 0, -2, 0] [-2, 2, 0, 2, 0, 2, -2, 0]).trans (in_context (eq1 h) [0, -2, 0, -2] [2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0]))
  have hr : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2] :=
    ((in_context (eq1 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2] [-2, 2, 0, 2, 0, 2, -2, 0, -2]).trans (in_context (eq0 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0] [2, 0, 2, 0, 2, -2, 0, -2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1584 (h : Relations φ) : value φ [-2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] := by
  have h0 : value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] = value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2] :=
    overlap (eq426 h) (eq12 h) [-2, 0, -2, 0, 2, 0, 2, 0, 2] [2, 0, 2, 0, 2, -2, 0] (by decide)
  have hl : value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] := rfl
  have hr : value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [-2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2] :=
    ((in_context (eq4 h) [-2, 0, -2, 0] [-2, 2, 0, 2, 0, 2, -2, 0, -2]).trans (in_context (eq1 h) [-2, 0, -2] [2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1585 (h : Relations φ) : value φ [2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2] = value φ [0, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] := by
  have h0 : value φ [0, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] = value φ [2, 0, 2, 0, -2, 0, -2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2] :=
    overlap (eq427 h) (eq6 h) [2, 0, 2, 0, -2, 0, -2, 0, -2] [-2, 0, -2, 0, -2, 2, 0] (by decide)
  have hl : value φ [0, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] = value φ [0, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] := rfl
  have hr : value φ [2, 0, 2, 0, -2, 0, -2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2] = value φ [2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2] :=
    ((in_context (eq5 h) [2, 0, 2, 0] [2, -2, 0, -2, 0, -2, 2, 0, 2]).trans (in_context (eq1 h) [2, 0, 2] [-2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1586 (h : Relations φ) : value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2] = value φ [0, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0] := by
  have h0 : value φ [0, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [2, -2, 0, -2, 0, -2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2] :=
    overlap (eq8 h) (eq428 h) [2, -2, 0, -2, 0, -2] [-2, 0, -2, 0, -2, 2, 0] (by decide)
  have hl : value φ [0, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [0, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0] := rfl
  have hr : value φ [2, -2, 0, -2, 0, -2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2] = value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2] :=
    (in_context (eq5 h) [2] [2, 0, -2, 0, -2, 0, -2, 2, 0, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1623 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2] = value φ [0, 2] := by
  have h0 : value φ [0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2] :=
    overlap (eq1060 h) (eq156 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2] [-2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2] (by decide)
  have hl : value φ [0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2] = value φ [0, 2] :=
    ((in_context (eq0 h) [0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0] [0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2]).trans ((in_context (eq1 h) [0, -2, 0, 2, -2, 2, -2, 2, 0, -2] [-2, 0, 2, -2, 2, -2, 2, 0, -2, 2]).trans ((in_context (eq0 h) [0, -2, 0, 2, -2, 2, -2, 2, 0] [0, 2, -2, 2, -2, 2, 0, -2, 2]).trans ((in_context (eq1 h) [0, -2, 0, 2, -2, 2, -2, 2] [2, -2, 2, -2, 2, 0, -2, 2]).trans ((in_context (eq2 h) [0, -2, 0, 2, -2, 2, -2] [-2, 2, -2, 2, 0, -2, 2]).trans ((in_context (eq0 h) [0, -2, 0, 2, -2, 2] [2, -2, 2, 0, -2, 2]).trans ((in_context (eq2 h) [0, -2, 0, 2, -2] [-2, 2, 0, -2, 2]).trans ((in_context (eq0 h) [0, -2, 0, 2] [2, 0, -2, 2]).trans ((in_context (eq2 h) [0, -2, 0] [0, -2, 2]).trans ((in_context (eq1 h) [0, -2] [-2, 2]).trans (in_context (eq0 h) [0] [2])))))))))))
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1624 (h : Relations φ) : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2] = value φ [0, -2] := by
  have h0 : value φ [0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2] :=
    overlap (eq1245 h) (eq300 h) [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2] (by decide)
  have hl : value φ [0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2] = value φ [0, -2] :=
    ((in_context (eq2 h) [0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0] [0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2]).trans ((in_context (eq1 h) [0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2] [-2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2]).trans ((in_context (eq0 h) [0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2] [2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2]).trans ((in_context (eq2 h) [0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0] [0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2]).trans ((in_context (eq1 h) [0, 2, 0, 2, -2, 2, -2, 2, 0, 2] [2, 0, 2, -2, 2, -2, 2, 0, 2, -2]).trans ((in_context (eq2 h) [0, 2, 0, 2, -2, 2, -2, 2, 0] [0, 2, -2, 2, -2, 2, 0, 2, -2]).trans ((in_context (eq1 h) [0, 2, 0, 2, -2, 2, -2, 2] [2, -2, 2, -2, 2, 0, 2, -2]).trans ((in_context (eq2 h) [0, 2, 0, 2, -2, 2, -2] [-2, 2, -2, 2, 0, 2, -2]).trans ((in_context (eq0 h) [0, 2, 0, 2, -2, 2] [2, -2, 2, 0, 2, -2]).trans ((in_context (eq2 h) [0, 2, 0, 2, -2] [-2, 2, 0, 2, -2]).trans ((in_context (eq0 h) [0, 2, 0, 2] [2, 0, 2, -2]).trans ((in_context (eq2 h) [0, 2, 0] [0, 2, -2]).trans ((in_context (eq1 h) [0, 2] [2, -2]).trans (in_context (eq2 h) [0] [-2]))))))))))))))
  have hr : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1627 (h : Relations φ) : value φ [-2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] = value φ [2, 0, 2] := by
  have h0 : value φ [2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2] = value φ [-2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] :=
    overlap (eq1255 h) (eq319 h) [-2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] [0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2] (by decide)
  have hl : value φ [2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2] = value φ [2, 0, 2] :=
    ((in_context (eq1 h) [2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2] [2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2]).trans ((in_context (eq2 h) [2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2] [-2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2]).trans ((in_context (eq0 h) [2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] [2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2]).trans ((in_context (eq2 h) [2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2] [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2]).trans ((in_context (eq0 h) [2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2] [2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2]).trans ((in_context (eq2 h) [2, -2, 0, 2, 0, -2, 2, 0, 2, 0] [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2]).trans ((in_context (eq1 h) [2, -2, 0, 2, 0, -2, 2, 0, 2] [2, 0, 2, -2, 0, 2, 0, -2, 0, 2]).trans ((in_context (eq2 h) [2, -2, 0, 2, 0, -2, 2, 0] [0, 2, -2, 0, 2, 0, -2, 0, 2]).trans ((in_context (eq1 h) [2, -2, 0, 2, 0, -2, 2] [2, -2, 0, 2, 0, -2, 0, 2]).trans ((in_context (eq2 h) [2, -2, 0, 2, 0, -2] [-2, 0, 2, 0, -2, 0, 2]).trans ((in_context (eq0 h) [2, -2, 0, 2, 0] [0, 2, 0, -2, 0, 2]).trans ((in_context (eq1 h) [2, -2, 0, 2] [2, 0, -2, 0, 2]).trans ((in_context (eq2 h) [2, -2, 0] [0, -2, 0, 2]).trans ((in_context (eq1 h) [2, -2] [-2, 0, 2]).trans (in_context (eq0 h) [2] [0, 2])))))))))))))))
  have hr : value φ [-2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] = value φ [-2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1628 (h : Relations φ) : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2] = value φ [2, 0, 2] := by
  have h0 : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2] :=
    overlap (eq296 h) (eq1270 h) [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2] [0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] (by decide)
  have hl : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] = value φ [2, 0, 2] :=
    ((in_context (eq1 h) [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2] [2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2]).trans ((in_context (eq2 h) [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2] [-2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2]).trans ((in_context (eq0 h) [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] [2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2]).trans ((in_context (eq2 h) [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2] [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2]).trans ((in_context (eq0 h) [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2] [2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2]).trans ((in_context (eq2 h) [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] [0, 2, 0, 2, -2, 0, 2, 0, -2, 2]).trans ((in_context (eq1 h) [2, 0, -2, 0, 2, 0, -2, 2, 0, 2] [2, 0, 2, -2, 0, 2, 0, -2, 2]).trans ((in_context (eq2 h) [2, 0, -2, 0, 2, 0, -2, 2, 0] [0, 2, -2, 0, 2, 0, -2, 2]).trans ((in_context (eq1 h) [2, 0, -2, 0, 2, 0, -2, 2] [2, -2, 0, 2, 0, -2, 2]).trans ((in_context (eq2 h) [2, 0, -2, 0, 2, 0, -2] [-2, 0, 2, 0, -2, 2]).trans ((in_context (eq0 h) [2, 0, -2, 0, 2, 0] [0, 2, 0, -2, 2]).trans ((in_context (eq1 h) [2, 0, -2, 0, 2] [2, 0, -2, 2]).trans ((in_context (eq2 h) [2, 0, -2, 0] [0, -2, 2]).trans ((in_context (eq1 h) [2, 0, -2] [-2, 2]).trans (in_context (eq0 h) [2, 0] [2])))))))))))))))
  have hr : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1629 (h : Relations φ) : value φ [2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [-2, 0, -2] := by
  have h0 : value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2] = value φ [2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] :=
    overlap (eq174 h) (eq1309 h) [2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2] [2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2] (by decide)
  have hl : value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2] = value φ [-2, 0, -2] :=
    ((in_context (eq2 h) [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2] [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2]).trans ((in_context (eq0 h) [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2] [2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2]).trans ((in_context (eq2 h) [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2] [-2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2]).trans ((in_context (eq0 h) [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2] [2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2]).trans ((in_context (eq2 h) [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] [0, -2, 0, -2, 2, 0, -2, 0, 2, -2]).trans ((in_context (eq1 h) [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2] [-2, 0, -2, 2, 0, -2, 0, 2, -2]).trans ((in_context (eq0 h) [-2, 0, 2, 0, -2, 0, 2, -2, 0] [0, -2, 2, 0, -2, 0, 2, -2]).trans ((in_context (eq1 h) [-2, 0, 2, 0, -2, 0, 2, -2] [-2, 2, 0, -2, 0, 2, -2]).trans ((in_context (eq0 h) [-2, 0, 2, 0, -2, 0, 2] [2, 0, -2, 0, 2, -2]).trans ((in_context (eq2 h) [-2, 0, 2, 0, -2, 0] [0, -2, 0, 2, -2]).trans ((in_context (eq1 h) [-2, 0, 2, 0, -2] [-2, 0, 2, -2]).trans ((in_context (eq0 h) [-2, 0, 2, 0] [0, 2, -2]).trans ((in_context (eq1 h) [-2, 0, 2] [2, -2]).trans (in_context (eq2 h) [-2, 0] [-2]))))))))))))))
  have hr : value φ [2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1630 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [2, -2, 0] := by
  have h0 : value φ [2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] :=
    overlap (eq276 h) (eq1396 h) [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0] [0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0] (by decide)
  have hl : value φ [2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0] = value φ [2, -2, 0] :=
    ((in_context (eq1 h) [2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2] [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0]).trans ((in_context (eq2 h) [2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0] [0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0]).trans ((in_context (eq1 h) [2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2] [-2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0]).trans ((in_context (eq0 h) [2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2] [2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0]).trans ((in_context (eq2 h) [2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0] [0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0]).trans ((in_context (eq1 h) [2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2] [2, 0, 2, -2, 2, -2, 2, 0, 2, 0]).trans ((in_context (eq2 h) [2, -2, 2, 0, 2, -2, 2, -2, 2, 0] [0, 2, -2, 2, -2, 2, 0, 2, 0]).trans ((in_context (eq1 h) [2, -2, 2, 0, 2, -2, 2, -2, 2] [2, -2, 2, -2, 2, 0, 2, 0]).trans ((in_context (eq2 h) [2, -2, 2, 0, 2, -2, 2, -2] [-2, 2, -2, 2, 0, 2, 0]).trans ((in_context (eq0 h) [2, -2, 2, 0, 2, -2, 2] [2, -2, 2, 0, 2, 0]).trans ((in_context (eq2 h) [2, -2, 2, 0, 2, -2] [-2, 2, 0, 2, 0]).trans ((in_context (eq0 h) [2, -2, 2, 0, 2] [2, 0, 2, 0]).trans ((in_context (eq2 h) [2, -2, 2, 0] [0, 2, 0]).trans ((in_context (eq1 h) [2, -2, 2] [2, 0]).trans (in_context (eq2 h) [2, -2] [0])))))))))))))))
  have hr : value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1632 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] = value φ [0, 2, -2, 2] := by
  have h0 : value φ [0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2, -2, 2] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] :=
    overlap (eq1060 h) (eq159 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0] [-2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2, -2, 2] (by decide)
  have hl : value φ [0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2, -2, 2] = value φ [0, 2, -2, 2] :=
    ((in_context (eq0 h) [0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0] [0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2, -2, 2]).trans ((in_context (eq1 h) [0, -2, 0, 2, -2, 2, -2, 2, 0, -2] [-2, 0, 2, -2, 2, -2, 2, 0, -2, 2, -2, 2]).trans ((in_context (eq0 h) [0, -2, 0, 2, -2, 2, -2, 2, 0] [0, 2, -2, 2, -2, 2, 0, -2, 2, -2, 2]).trans ((in_context (eq1 h) [0, -2, 0, 2, -2, 2, -2, 2] [2, -2, 2, -2, 2, 0, -2, 2, -2, 2]).trans ((in_context (eq2 h) [0, -2, 0, 2, -2, 2, -2] [-2, 2, -2, 2, 0, -2, 2, -2, 2]).trans ((in_context (eq0 h) [0, -2, 0, 2, -2, 2] [2, -2, 2, 0, -2, 2, -2, 2]).trans ((in_context (eq2 h) [0, -2, 0, 2, -2] [-2, 2, 0, -2, 2, -2, 2]).trans ((in_context (eq0 h) [0, -2, 0, 2] [2, 0, -2, 2, -2, 2]).trans ((in_context (eq2 h) [0, -2, 0] [0, -2, 2, -2, 2]).trans ((in_context (eq1 h) [0, -2] [-2, 2, -2, 2]).trans (in_context (eq0 h) [0] [2, -2, 2])))))))))))
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] :=
    ((in_context (eq1 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2] [2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0]).trans (in_context (eq2 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2] [0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1636 (h : Relations φ) : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0] = value φ [2, 0, 2, -2] := by
  have h0 : value φ [2, 0, 2, -2] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0] :=
    overlap (eq1628 h) (eq0 h) [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0] [-2] (by decide)
  have hl : value φ [2, 0, 2, -2] = value φ [2, 0, 2, -2] := rfl
  have hr : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1637 (h : Relations φ) : value φ [2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0] = value φ [-2, 0, -2, 2] := by
  have h0 : value φ [-2, 0, -2, 2] = value φ [2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0] :=
    overlap (eq1629 h) (eq2 h) [2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0] [2] (by decide)
  have hl : value φ [-2, 0, -2, 2] = value φ [-2, 0, -2, 2] := rfl
  have hr : value φ [2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0] = value φ [2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1638 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2] = value φ [2, -2, 0, 2] := by
  have h0 : value φ [2, -2, 0, 2] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2] :=
    overlap (eq1630 h) (eq2 h) [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2] [2] (by decide)
  have hl : value φ [2, -2, 0, 2] = value φ [2, -2, 0, 2] := rfl
  have hr : value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1646 (h : Relations φ) : value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [0, 2, -2, 0, -2] := by
  have h0 : value φ [0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2] = value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] :=
    overlap (eq150 h) (eq1309 h) [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2] [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2] (by decide)
  have hl : value φ [0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2] = value φ [0, 2, -2, 0, -2] :=
    ((in_context (eq0 h) [0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2] [2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2]).trans ((in_context (eq2 h) [0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2] [-2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2]).trans ((in_context (eq0 h) [0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2] [2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2]).trans ((in_context (eq2 h) [0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] [0, -2, 0, -2, 2, 0, -2, 0, 2, -2]).trans ((in_context (eq1 h) [0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2] [-2, 0, -2, 2, 0, -2, 0, 2, -2]).trans ((in_context (eq0 h) [0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0] [0, -2, 2, 0, -2, 0, 2, -2]).trans ((in_context (eq1 h) [0, 2, -2, 0, 2, 0, -2, 0, 2, -2] [-2, 2, 0, -2, 0, 2, -2]).trans ((in_context (eq0 h) [0, 2, -2, 0, 2, 0, -2, 0, 2] [2, 0, -2, 0, 2, -2]).trans ((in_context (eq2 h) [0, 2, -2, 0, 2, 0, -2, 0] [0, -2, 0, 2, -2]).trans ((in_context (eq1 h) [0, 2, -2, 0, 2, 0, -2] [-2, 0, 2, -2]).trans ((in_context (eq0 h) [0, 2, -2, 0, 2, 0] [0, 2, -2]).trans ((in_context (eq1 h) [0, 2, -2, 0, 2] [2, -2]).trans (in_context (eq2 h) [0, 2, -2, 0] [-2])))))))))))))
  have hr : value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1651 (h : Relations φ) : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2] = value φ [0, -2, 2, 0, 2] := by
  have h0 : value φ [0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] = value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2] :=
    overlap (eq1578 h) (eq1270 h) [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2] [2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] (by decide)
  have hl : value φ [0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2] = value φ [0, -2, 2, 0, 2] :=
    ((in_context (eq2 h) [0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2] [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2]).trans ((in_context (eq0 h) [0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2] [2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2]).trans ((in_context (eq2 h) [0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] [0, 2, 0, 2, -2, 0, 2, 0, -2, 2]).trans ((in_context (eq1 h) [0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2] [2, 0, 2, -2, 0, 2, 0, -2, 2]).trans ((in_context (eq2 h) [0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0] [0, 2, -2, 0, 2, 0, -2, 2]).trans ((in_context (eq1 h) [0, -2, 2, 0, -2, 0, 2, 0, -2, 2] [2, -2, 0, 2, 0, -2, 2]).trans ((in_context (eq2 h) [0, -2, 2, 0, -2, 0, 2, 0, -2] [-2, 0, 2, 0, -2, 2]).trans ((in_context (eq0 h) [0, -2, 2, 0, -2, 0, 2, 0] [0, 2, 0, -2, 2]).trans ((in_context (eq1 h) [0, -2, 2, 0, -2, 0, 2] [2, 0, -2, 2]).trans ((in_context (eq2 h) [0, -2, 2, 0, -2, 0] [0, -2, 2]).trans ((in_context (eq1 h) [0, -2, 2, 0, -2] [-2, 2]).trans (in_context (eq0 h) [0, -2, 2, 0] [2]))))))))))))
  have hr : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2] = value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1652 (h : Relations φ) : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2] = value φ [2, 0, 2, -2, 0] := by
  have h0 : value φ [2, 0, 2, -2, 0] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2] :=
    overlap (eq1636 h) (eq1 h) [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2] [0] (by decide)
  have hl : value φ [2, 0, 2, -2, 0] = value φ [2, 0, 2, -2, 0] := rfl
  have hr : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1654 (h : Relations φ) : value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] = value φ [-2, 0, 2, -2, 0, -2] := by
  have h0 : value φ [-2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] :=
    overlap (eq275 h) (eq664 h) [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0] [2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] (by decide)
  have hl : value φ [-2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [-2, 0, 2, -2, 0, -2] :=
    ((in_context (eq430 h) [-2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2] [2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2]).trans ((in_context (eq4 h) [-2, 2, 0, 2, -2, 2, -2] [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2]).trans ((in_context (eq430 h) [-2, 2, 0, 2, -2, 2] [2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2]).trans ((in_context (eq39 h) [-2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0, 2, 0, 2, 0, 2] [2, 0, 2, -2]).trans ((in_context (eq4 h) [-2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0] [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 2, 0, 2, -2]).trans ((in_context (eq1 h) [-2, 2, 0, 2, -2, 2, 0, -2, 0, -2] [2, 0, 2, 0, 2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 2, 0, 2, -2]).trans ((in_context (eq2 h) [-2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0] [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 2, 0, 2, -2]).trans ((in_context (eq1 h) [-2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2] [-2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 2, 0, 2, -2]).trans ((in_context (eq45 h) [-2] [-2, 0, -2, 0, -2, 2, -2, 2, 2, 0, 2, -2]).trans ((in_context (eq0 h) [-2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0] [0, -2, 0, -2, 2, -2, 2, 2, 0, 2, -2]).trans ((in_context (eq1 h) [-2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2] [-2, 0, -2, 2, -2, 2, 2, 0, 2, -2]).trans ((in_context (eq0 h) [-2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0] [0, -2, 2, -2, 2, 2, 0, 2, -2]).trans ((in_context (eq1 h) [-2, 0, 2, -2, 0, 2, 0, -2, 2, -2] [-2, 2, -2, 2, 2, 0, 2, -2]).trans ((in_context (eq0 h) [-2, 0, 2, -2, 0, 2, 0, -2, 2] [2, -2, 2, 2, 0, 2, -2]).trans ((in_context (eq2 h) [-2, 0, 2, -2, 0, 2, 0, -2] [-2, 2, 2, 0, 2, -2]).trans ((in_context (eq0 h) [-2, 0, 2, -2, 0, 2, 0] [2, 2, 0, 2, -2]).trans ((in_context (eq2 h) [-2, 0, 2, -2, 0, 2, 0] [0, 2, -2]).trans ((in_context (eq1 h) [-2, 0, 2, -2, 0, 2] [2, -2]).trans (in_context (eq2 h) [-2, 0, 2, -2, 0] [-2])))))))))))))))))))
  have hr : value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] = value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1664 (h : Relations φ) : value φ [0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2] = value φ [-2, 0, -2, 2, 0, -2] := by
  have h0 : value φ [-2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2] = value φ [0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2] :=
    overlap (eq1514 h) (eq300 h) [0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] [2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2] (by decide)
  have hl : value φ [-2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2] = value φ [-2, 0, -2, 2, 0, -2] :=
    ((in_context (eq2 h) [-2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0] [0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2]).trans ((in_context (eq1 h) [-2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2] [2, 0, 2, -2, 2, -2, 2, 0, 2, -2]).trans ((in_context (eq2 h) [-2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0] [0, 2, -2, 2, -2, 2, 0, 2, -2]).trans ((in_context (eq1 h) [-2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2] [2, -2, 2, -2, 2, 0, 2, -2]).trans ((in_context (eq2 h) [-2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2] [-2, 2, -2, 2, 0, 2, -2]).trans ((in_context (eq0 h) [-2, 0, -2, 2, 0, 2, 0, 2, -2, 2] [2, -2, 2, 0, 2, -2]).trans ((in_context (eq2 h) [-2, 0, -2, 2, 0, 2, 0, 2, -2] [-2, 2, 0, 2, -2]).trans ((in_context (eq0 h) [-2, 0, -2, 2, 0, 2, 0, 2] [2, 0, 2, -2]).trans ((in_context (eq2 h) [-2, 0, -2, 2, 0, 2, 0] [0, 2, -2]).trans ((in_context (eq1 h) [-2, 0, -2, 2, 0, 2] [2, -2]).trans (in_context (eq2 h) [-2, 0, -2, 2, 0] [-2])))))))))))
  have hr : value φ [0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2] = value φ [0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1667 (h : Relations φ) : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0] = value φ [0, -2, 2, 0, 2, -2] := by
  have h0 : value φ [0, -2, 2, 0, 2, -2] = value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0] :=
    overlap (eq1651 h) (eq0 h) [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0] [-2] (by decide)
  have hl : value φ [0, -2, 2, 0, 2, -2] = value φ [0, -2, 2, 0, 2, -2] := rfl
  have hr : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0] = value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1670 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] = value φ [2, -2, 0, 2, -2, 0, -2] := by
  have h0 : value φ [2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] :=
    overlap (eq276 h) (eq664 h) [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0] [2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] (by decide)
  have hl : value φ [2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [2, -2, 0, 2, -2, 0, -2] :=
    ((in_context (eq430 h) [2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2] [2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2]).trans ((in_context (eq4 h) [2, -2, 2, 0, 2, -2, 2, -2] [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2]).trans ((in_context (eq430 h) [2, -2, 2, 0, 2, -2, 2] [2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2]).trans ((in_context (eq39 h) [2, -2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0, 2, 0, 2, 0, 2] [2, 0, 2, -2]).trans ((in_context (eq4 h) [2, -2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0] [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 2, 0, 2, -2]).trans ((in_context (eq1 h) [2, -2, 2, 0, 2, -2, 2, 0, -2, 0, -2] [2, 0, 2, 0, 2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 2, 0, 2, -2]).trans ((in_context (eq2 h) [2, -2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0] [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 2, 0, 2, -2]).trans ((in_context (eq1 h) [2, -2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2] [-2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 2, 0, 2, -2]).trans ((in_context (eq45 h) [2, -2] [-2, 0, -2, 0, -2, 2, -2, 2, 2, 0, 2, -2]).trans ((in_context (eq0 h) [2, -2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0] [0, -2, 0, -2, 2, -2, 2, 2, 0, 2, -2]).trans ((in_context (eq1 h) [2, -2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2] [-2, 0, -2, 2, -2, 2, 2, 0, 2, -2]).trans ((in_context (eq0 h) [2, -2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0] [0, -2, 2, -2, 2, 2, 0, 2, -2]).trans ((in_context (eq1 h) [2, -2, 0, 2, -2, 0, 2, 0, -2, 2, -2] [-2, 2, -2, 2, 2, 0, 2, -2]).trans ((in_context (eq0 h) [2, -2, 0, 2, -2, 0, 2, 0, -2, 2] [2, -2, 2, 2, 0, 2, -2]).trans ((in_context (eq2 h) [2, -2, 0, 2, -2, 0, 2, 0, -2] [-2, 2, 2, 0, 2, -2]).trans ((in_context (eq0 h) [2, -2, 0, 2, -2, 0, 2, 0] [2, 2, 0, 2, -2]).trans ((in_context (eq2 h) [2, -2, 0, 2, -2, 0, 2, 0] [0, 2, -2]).trans ((in_context (eq1 h) [2, -2, 0, 2, -2, 0, 2] [2, -2]).trans (in_context (eq2 h) [2, -2, 0, 2, -2, 0] [-2])))))))))))))))))))
  have hr : value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1673 (h : Relations φ) : value φ [-2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0] = value φ [2, 0, -2, 2, -2, 0, 2] := by
  have h0 : value φ [2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2] = value φ [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0] :=
    overlap (eq1032 h) (eq306 h) [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0] [0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2] (by decide)
  have hl : value φ [2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2] = value φ [2, 0, -2, 2, -2, 0, 2] :=
    ((in_context (eq1 h) [2, 0, 2, 0, 2, -2, 2, -2, 2] [2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2]).trans ((in_context (eq2 h) [2, 0, 2, 0, 2, -2, 2, -2] [-2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2]).trans ((in_context (eq0 h) [2, 0, 2, 0, 2, -2, 2] [2, -2, 2, 0, 2, -2, 2, -2, 0, 2]).trans ((in_context (eq2 h) [2, 0, 2, 0, 2, -2] [-2, 2, 0, 2, -2, 2, -2, 0, 2]).trans ((in_context (eq0 h) [2, 0, 2, 0, 2] [2, 0, 2, -2, 2, -2, 0, 2]).trans ((in_context (eq2 h) [2, 0, 2, 0] [0, 2, -2, 2, -2, 0, 2]).trans ((in_context (eq1 h) [2, 0, 2] [2, -2, 2, -2, 0, 2]).trans (in_context (eq2 h) [2, 0] [-2, 2, -2, 0, 2]))))))))
  have hr : value φ [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0] = value φ [-2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0] :=
    ((in_context (eq1 h) [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2] [2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0]).trans ((in_context (eq998 h) [-2, 0] [0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0]).trans ((in_context (eq1 h) [-2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2] [-2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0]).trans (in_context (eq0 h) [-2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] [0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0]))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1683 (h : Relations φ) : value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2] = value φ [-2, 0, 2, -2, 0, -2, 0] := by
  have h0 : value φ [-2, 0, 2, -2, 0, -2, 0] = value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2] :=
    overlap (eq1654 h) (eq1 h) [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2] [0] (by decide)
  have hl : value φ [-2, 0, 2, -2, 0, -2, 0] = value φ [-2, 0, 2, -2, 0, -2, 0] := rfl
  have hr : value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2] = value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1686 (h : Relations φ) : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2] = value φ [0, -2, 2, 0, 2, -2, 0] := by
  have h0 : value φ [0, -2, 2, 0, 2, -2, 0] = value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2] :=
    overlap (eq1667 h) (eq1 h) [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2] [0] (by decide)
  have hl : value φ [0, -2, 2, 0, 2, -2, 0] = value φ [0, -2, 2, 0, 2, -2, 0] := rfl
  have hr : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2] = value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1690 (h : Relations φ) : value φ [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0] = value φ [0, -2, 0, 2, -2, 0, -2, 2] := by
  have h0 : value φ [0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2] = value φ [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2, 0] :=
    overlap (eq147 h) (eq893 h) [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0] [-2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2] (by decide)
  have hl : value φ [0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2] = value φ [0, -2, 0, 2, -2, 0, -2, 2] :=
    ((in_context (eq0 h) [0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2] [2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2]).trans ((in_context (eq2 h) [0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] [0, -2, 0, -2, 2, 0, -2, 0, 2, -2, 2]).trans ((in_context (eq1 h) [0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2] [-2, 0, -2, 2, 0, -2, 0, 2, -2, 2]).trans ((in_context (eq0 h) [0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0] [0, -2, 2, 0, -2, 0, 2, -2, 2]).trans ((in_context (eq1 h) [0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2] [-2, 2, 0, -2, 0, 2, -2, 2]).trans ((in_context (eq0 h) [0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2] [2, 0, -2, 0, 2, -2, 2]).trans ((in_context (eq2 h) [0, -2, 0, 2, -2, 0, 2, 0, -2, 0] [0, -2, 0, 2, -2, 2]).trans ((in_context (eq1 h) [0, -2, 0, 2, -2, 0, 2, 0, -2] [-2, 0, 2, -2, 2]).trans ((in_context (eq0 h) [0, -2, 0, 2, -2, 0, 2, 0] [0, 2, -2, 2]).trans ((in_context (eq1 h) [0, -2, 0, 2, -2, 0, 2] [2, -2, 2]).trans (in_context (eq2 h) [0, -2, 0, 2, -2, 0] [-2, 2])))))))))))
  have hr : value φ [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, 2, 0] = value φ [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0] :=
    ((in_context (eq12 h) [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2] [-2, 2, -2, 2, 0, 2, 0]).trans (in_context (eq0 h) [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0] [2, -2, 2, 0, 2, 0]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1692 (h : Relations φ) : value φ [2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 2] = value φ [-2, 2, 0, -2, 2, 0, 2, 0] := by
  have h0 : value φ [-2, 2, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0] = value φ [2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 2] :=
    overlap (eq132 h) (eq1047 h) [2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0] [-2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0] (by decide)
  have hl : value φ [-2, 2, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0] = value φ [-2, 2, 0, -2, 2, 0, 2, 0] :=
    ((in_context (eq0 h) [-2, 2, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0] [0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0]).trans ((in_context (eq1 h) [-2, 2, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2] [2, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0]).trans ((in_context (eq2 h) [-2, 2, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2] [-2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0]).trans ((in_context (eq0 h) [-2, 2, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0] [0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0]).trans ((in_context (eq1 h) [-2, 2, -2, 0, 2, -2, 2, -2, 2, 0, -2] [-2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0]).trans ((in_context (eq0 h) [-2, 2, -2, 0, 2, -2, 2, -2, 2, 0] [0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0]).trans ((in_context (eq1 h) [-2, 2, -2, 0, 2, -2, 2, -2, 2] [2, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0]).trans ((in_context (eq2 h) [-2, 2, -2, 0, 2, -2, 2, -2] [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0]).trans ((in_context (eq0 h) [-2, 2, -2, 0, 2, -2, 2] [2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0]).trans ((in_context (eq2 h) [-2, 2, -2, 0, 2, -2] [-2, 2, 0, -2, 0, -2, 2, 0, 2, 0]).trans ((in_context (eq0 h) [-2, 2, -2, 0, 2] [2, 0, -2, 0, -2, 2, 0, 2, 0]).trans ((in_context (eq2 h) [-2, 2, -2, 0] [0, -2, 0, -2, 2, 0, 2, 0]).trans ((in_context (eq1 h) [-2, 2, -2] [-2, 0, -2, 2, 0, 2, 0]).trans (in_context (eq0 h) [-2, 2] [0, -2, 2, 0, 2, 0]))))))))))))))
  have hr : value φ [2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 2] = value φ [2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1693 (h : Relations φ) : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] = value φ [-2, 2, -2, 0, 2, -2, 0, -2] := by
  have h0 : value φ [-2, 2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] :=
    overlap (eq278 h) (eq1051 h) [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0] [0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2] (by decide)
  have hl : value φ [-2, 2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [-2, 2, -2, 0, 2, -2, 0, -2] :=
    ((in_context (eq1 h) [-2, 2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2] [-2, 2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq0 h) [-2, 2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2] [2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq2 h) [-2, 2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0] [0, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq1 h) [-2, 2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2] [2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq2 h) [-2, 2, -2, 2, 0, 2, -2, 2, -2, 2, 0] [0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq1 h) [-2, 2, -2, 2, 0, 2, -2, 2, -2, 2] [2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq2 h) [-2, 2, -2, 2, 0, 2, -2, 2, -2] [-2, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq0 h) [-2, 2, -2, 2, 0, 2, -2, 2] [2, -2, 2, 0, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq2 h) [-2, 2, -2, 2, 0, 2, -2] [-2, 2, 0, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq0 h) [-2, 2, -2, 2, 0, 2] [2, 0, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq2 h) [-2, 2, -2, 2, 0] [0, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq1 h) [-2, 2, -2, 2] [2, 0, 2, -2, 0, -2]).trans (in_context (eq2 h) [-2, 2, -2] [0, 2, -2, 0, -2])))))))))))))
  have hr : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1702 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2] = value φ [2, -2, 0, 2, -2, 0, -2, 0] := by
  have h0 : value φ [2, -2, 0, 2, -2, 0, -2, 0] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2] :=
    overlap (eq1670 h) (eq1 h) [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2] [0] (by decide)
  have hl : value φ [2, -2, 0, 2, -2, 0, -2, 0] = value φ [2, -2, 0, 2, -2, 0, -2, 0] := rfl
  have hr : value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1705 (h : Relations φ) : value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2] := by
  have h0 : value φ [-2, 0, 2, -2, 0, -2, 0, -2] = value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] :=
    overlap (eq1683 h) (eq0 h) [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] [-2] (by decide)
  have hl : value φ [-2, 0, 2, -2, 0, -2, 0, -2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2] := rfl
  have hr : value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] = value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1706 (h : Relations φ) : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0] = value φ [0, -2, 2, 0, 2, -2, 0, -2] := by
  have h0 : value φ [0, -2, 2, 0, 2, -2, 0, -2] = value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0] :=
    overlap (eq1686 h) (eq0 h) [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0] [-2] (by decide)
  have hl : value φ [0, -2, 2, 0, 2, -2, 0, -2] = value φ [0, -2, 2, 0, 2, -2, 0, -2] := rfl
  have hr : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0] = value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1711 (h : Relations φ) : value φ [-2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] = value φ [2, 0, -2, 2, -2, 0, 2, 0, 2] := by
  have h0 : value φ [2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2] = value φ [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] :=
    overlap (eq1032 h) (eq308 h) [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2] [0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2] (by decide)
  have hl : value φ [2, 0, 2, 0, 2, -2, 2, -2, 2, 0, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2] = value φ [2, 0, -2, 2, -2, 0, 2, 0, 2] :=
    ((in_context (eq1 h) [2, 0, 2, 0, 2, -2, 2, -2, 2] [2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [2, 0, 2, 0, 2, -2, 2, -2] [-2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2]).trans ((in_context (eq0 h) [2, 0, 2, 0, 2, -2, 2] [2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [2, 0, 2, 0, 2, -2] [-2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2]).trans ((in_context (eq0 h) [2, 0, 2, 0, 2] [2, 0, 2, -2, 2, -2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [2, 0, 2, 0] [0, 2, -2, 2, -2, 0, 2, 0, 2]).trans ((in_context (eq1 h) [2, 0, 2] [2, -2, 2, -2, 0, 2, 0, 2]).trans (in_context (eq2 h) [2, 0] [-2, 2, -2, 0, 2, 0, 2]))))))))
  have hr : value φ [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] = value φ [-2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] :=
    ((in_context (eq0 h) [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0] [0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2]).trans ((in_context (eq1 h) [-2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2] [2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2]).trans ((in_context (eq998 h) [-2, 0] [0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2]).trans ((in_context (eq1 h) [-2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2] [-2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2]).trans (in_context (eq0 h) [-2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] [0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1719 (h : Relations φ) : value φ [-2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [0, 2, 0, -2, 0, 2, -2, 0, -2] := by
  have h0 : value φ [0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2] = value φ [-2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] :=
    overlap (eq144 h) (eq1309 h) [-2, 0, 2, -2, 0, -2, 0, 2, -2, 2] [0, -2, 0, -2, 2, 0, -2, 0, 2, -2] (by decide)
  have hl : value φ [0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2] = value φ [0, 2, 0, -2, 0, 2, -2, 0, -2] :=
    ((in_context (eq1 h) [0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2] [-2, 0, -2, 2, 0, -2, 0, 2, -2]).trans ((in_context (eq0 h) [0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0] [0, -2, 2, 0, -2, 0, 2, -2]).trans ((in_context (eq1 h) [0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2] [-2, 2, 0, -2, 0, 2, -2]).trans ((in_context (eq0 h) [0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2] [2, 0, -2, 0, 2, -2]).trans ((in_context (eq2 h) [0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0] [0, -2, 0, 2, -2]).trans ((in_context (eq1 h) [0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2] [-2, 0, 2, -2]).trans ((in_context (eq0 h) [0, 2, 0, -2, 0, 2, -2, 0, 2, 0] [0, 2, -2]).trans ((in_context (eq1 h) [0, 2, 0, -2, 0, 2, -2, 0, 2] [2, -2]).trans (in_context (eq2 h) [0, 2, 0, -2, 0, 2, -2, 0] [-2])))))))))
  have hr : value φ [-2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [-2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1725 (h : Relations φ) : value φ [2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2] = value φ [-2, 2, 0, -2, 2, 0, 2, 0, 2] := by
  have h0 : value φ [-2, 2, 0, -2, 2, 0, 2, 0, 2] = value φ [2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2] :=
    overlap (eq1692 h) (eq2 h) [2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2] [2] (by decide)
  have hl : value φ [-2, 2, 0, -2, 2, 0, 2, 0, 2] = value φ [-2, 2, 0, -2, 2, 0, 2, 0, 2] := rfl
  have hr : value φ [2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2] = value φ [2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1726 (h : Relations φ) : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2] = value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0] := by
  have h0 : value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2] :=
    overlap (eq1693 h) (eq1 h) [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2] [0] (by decide)
  have hl : value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0] = value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0] := rfl
  have hr : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1727 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] = value φ [2, -2, 0, 2, -2, 0, -2, 0, -2] := by
  have h0 : value φ [2, -2, 0, 2, -2, 0, -2, 0, -2] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] :=
    overlap (eq1702 h) (eq0 h) [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] [-2] (by decide)
  have hl : value φ [2, -2, 0, 2, -2, 0, -2, 0, -2] = value φ [2, -2, 0, 2, -2, 0, -2, 0, -2] := rfl
  have hr : value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1728 (h : Relations φ) : value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2] := by
  have h0 : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] :=
    overlap (eq1705 h) (eq2 h) [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] [2] (by decide)
  have hl : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2] := rfl
  have hr : value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] = value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1729 (h : Relations φ) : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2] = value φ [0, -2, 2, 0, 2, -2, 0, -2, 0] := by
  have h0 : value φ [0, -2, 2, 0, 2, -2, 0, -2, 0] = value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2] :=
    overlap (eq1706 h) (eq1 h) [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2] [0] (by decide)
  have hl : value φ [0, -2, 2, 0, 2, -2, 0, -2, 0] = value φ [0, -2, 2, 0, 2, -2, 0, -2, 0] := rfl
  have hr : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2] = value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1758 (h : Relations φ) : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] = value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2] := by
  have h0 : value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] :=
    overlap (eq1726 h) (eq0 h) [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] [-2] (by decide)
  have hl : value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2] = value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2] := rfl
  have hr : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1759 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] = value φ [2, -2, 0, 2, -2, 0, -2, 0, -2, 2] := by
  have h0 : value φ [2, -2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] :=
    overlap (eq1727 h) (eq2 h) [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] [2] (by decide)
  have hl : value φ [2, -2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [2, -2, 0, 2, -2, 0, -2, 0, -2, 2] := rfl
  have hr : value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1760 (h : Relations φ) : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2] = value φ [0, -2, 2, 0, 2, -2, 0, -2, 0, -2] := by
  have h0 : value φ [0, -2, 2, 0, 2, -2, 0, -2, 0, -2] = value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2] :=
    overlap (eq1729 h) (eq0 h) [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2] [-2] (by decide)
  have hl : value φ [0, -2, 2, 0, 2, -2, 0, -2, 0, -2] = value φ [0, -2, 2, 0, 2, -2, 0, -2, 0, -2] := rfl
  have hr : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2] = value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1763 (h : Relations φ) : value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] := by
  have h0 : value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2] :=
    overlap (eq17 h) (eq300 h) [2, -2, 0, -2, 0, -2, 2] [2, 0, 2, -2, 2, -2, 2, 0, 2, -2] (by decide)
  have hl : value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] :=
    ((in_context (eq2 h) [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0] [0, 2, -2, 2, -2, 2, 0, 2, -2]).trans ((in_context (eq1 h) [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2] [2, -2, 2, -2, 2, 0, 2, -2]).trans ((in_context (eq2 h) [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2] [-2, 2, -2, 2, 0, 2, -2]).trans ((in_context (eq0 h) [-2, 2, 0, 2, -2, 0, -2, 0, 2] [2, -2, 2, 0, 2, -2]).trans ((in_context (eq2 h) [-2, 2, 0, 2, -2, 0, -2, 0] [-2, 2, 0, 2, -2]).trans ((in_context (eq6 h) [-2] [2, -2]).trans (in_context (eq2 h) [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0] [-2])))))))
  have hr : value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1782 (h : Relations φ) : value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2] = value φ [0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0] := by
  have h0 : value φ [0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0] = value φ [-2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2] :=
    overlap (eq20 h) (eq1580 h) [-2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2] [2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0] (by decide)
  have hl : value φ [0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0] = value φ [0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0] :=
    ((in_context (eq2 h) [0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0] [0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0]).trans ((in_context (eq1 h) [0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2] [2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0]).trans ((in_context (eq2 h) [0, -2, 0, -2, 2, -2, 0, 2, 0, -2] [-2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0]).trans ((in_context (eq0 h) [0, -2, 0, -2, 2, -2, 0, 2, 0] [0, 2, 0, -2, 0, 2, -2, 0, 2, 0]).trans ((in_context (eq1 h) [0, -2, 0, -2, 2, -2, 0, 2] [2, 0, -2, 0, 2, -2, 0, 2, 0]).trans ((in_context (eq2 h) [0, -2, 0, -2, 2, -2, 0] [0, -2, 0, 2, -2, 0, 2, 0]).trans ((in_context (eq1 h) [0, -2, 0, -2, 2, -2] [-2, 0, 2, -2, 0, 2, 0]).trans (in_context (eq0 h) [0, -2, 0, -2, 2] [0, 2, -2, 0, 2, 0]))))))))
  have hr : value φ [-2, 2, -2, 2, 0, 2, -2, 0, -2, 0, 2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2] = value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2] :=
    ((in_context (eq2 h) [-2, 2, -2, 2, 0, 2, -2, 0, -2, 0] [-2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2]).trans ((in_context (eq6 h) [-2, 2, -2] [2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2]).trans (in_context (eq2 h) [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] [-2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1788 (h : Relations φ) : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] = value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] := by
  have h0 : value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] :=
    overlap (eq1758 h) (eq2 h) [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] [2] (by decide)
  have hl : value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] := rfl
  have hr : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1789 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] = value φ [2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] := by
  have h0 : value φ [2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] :=
    overlap (eq1759 h) (eq1 h) [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] [0] (by decide)
  have hl : value φ [2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] := rfl
  have hr : value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1790 (h : Relations φ) : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] = value φ [0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2] := by
  have h0 : value φ [0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] :=
    overlap (eq1760 h) (eq2 h) [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] [2] (by decide)
  have hl : value φ [0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2] := rfl
  have hr : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] = value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1794 (h : Relations φ) : value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0] = value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2] := by
  have h0 : value φ [0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2] = value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2, 2, -2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0] :=
    overlap (eq287 h) (eq50 h) [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2, 2, -2] [0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2] (by decide)
  have hl : value φ [0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2] = value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2] :=
    ((in_context (eq1 h) [0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2] [2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2]).trans ((in_context (eq2 h) [0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0] [0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2]).trans ((in_context (eq1 h) [0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2] [2, -2, 0, 2, 0, -2, 2, -2, 0, -2]).trans ((in_context (eq2 h) [0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2] [-2, 0, 2, 0, -2, 2, -2, 0, -2]).trans ((in_context (eq0 h) [0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0] [0, 2, 0, -2, 2, -2, 0, -2]).trans ((in_context (eq1 h) [0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2] [2, 0, -2, 2, -2, 0, -2]).trans ((in_context (eq2 h) [0, -2, 0, 2, 0, -2, 2, 0, -2, 0] [0, -2, 2, -2, 0, -2]).trans ((in_context (eq1 h) [0, -2, 0, 2, 0, -2, 2, 0, -2] [-2, 2, -2, 0, -2]).trans (in_context (eq0 h) [0, -2, 0, 2, 0, -2, 2, 0] [2, -2, 0, -2])))))))))
  have hr : value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2, 2, -2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0] = value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0] :=
    ((in_context (eq0 h) [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2, 2] [2, 0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0]).trans ((in_context (eq2 h) [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2] [0, -2, 0, -2, 2, 0, 2, -2, 2, -2, 0]).trans ((in_context (eq6 h) [2, 0, -2, 2, 0, 2, 0, -2, 2, -2] [2, -2, 2, -2, 0]).trans (in_context (eq2 h) [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] [-2, 2, -2, 0]))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1796 (h : Relations φ) : value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] = value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2] := by
  have h0 : value φ [2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 0, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] :=
    overlap (eq15 h) (eq302 h) [-2, 2, -2, 0, -2, 0, -2, 2, -2] [0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2] (by decide)
  have hl : value φ [2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 0, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2] = value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2] :=
    ((in_context (eq1 h) [2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2] [2, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2]).trans ((in_context (eq2 h) [2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0] [0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2]).trans ((in_context (eq1 h) [2, 0, 2, -2, 0, -2, 0, 2, -2, 2] [2, -2, 2, -2, 2, 0, 2, -2, 2, -2]).trans ((in_context (eq2 h) [2, 0, 2, -2, 0, -2, 0, 2, -2] [-2, 2, -2, 2, 0, 2, -2, 2, -2]).trans ((in_context (eq0 h) [2, 0, 2, -2, 0, -2, 0, 2] [2, -2, 2, 0, 2, -2, 2, -2]).trans ((in_context (eq2 h) [2, 0, 2, -2, 0, -2, 0] [-2, 2, 0, 2, -2, 2, -2]).trans ((in_context (eq6 h) [] [2, -2, 2, -2]).trans (in_context (eq2 h) [0, 2, -2, 0, -2, 0, -2, 2, 0] [-2, 2, -2]))))))))
  have hr : value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] :=
    (in_context (eq0 h) [-2, 2, -2, 0, -2, 0, -2, 2] [0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1832 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] = value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2] := by
  have h0 : value φ [2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, -2, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2, -2, 2] = value φ [-2, 2, 0, 2, 0, 2, -2, 2, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] :=
    overlap (eq100 h) (eq158 h) [-2, 2, 0, 2, 0, 2, -2, 2] [-2, 0, 2, -2, 2, -2, 2, 0, -2, 2, -2, 2] (by decide)
  have hl : value φ [2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, -2, -2, 0, 2, -2, 2, -2, 2, 0, -2, 2, -2, 2] = value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2] :=
    ((in_context (eq0 h) [2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0] [0, 2, -2, 2, -2, 2, 0, -2, 2, -2, 2]).trans ((in_context (eq1 h) [2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2] [2, -2, 2, -2, 2, 0, -2, 2, -2, 2]).trans ((in_context (eq3 h) [2, -2, 0, -2, 2, 0, 2, 0] [2, -2, 2, 0, -2, 2, -2, 2]).trans ((in_context (eq2 h) [2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2] [-2, 2, 0, -2, 2, -2, 2]).trans ((in_context (eq0 h) [2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2] [2, 0, -2, 2, -2, 2]).trans ((in_context (eq2 h) [2, -2, 0, -2, 2, 0, 2, 0, 2, -2] [0, -2, 2, -2, 2]).trans ((in_context (eq12 h) [2] [-2, 2, -2, 2]).trans (in_context (eq0 h) [2, 0, -2, 2, 0, 2, 0, 2, -2, 0] [2, -2, 2]))))))))
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 2, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] :=
    (in_context (eq2 h) [-2, 2, 0, 2, 0, 2, -2] [0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1836 (h : Relations φ) : value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2] := by
  have h0 : value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2] = value φ [2, -2, 0, -2, 0, -2, 2, -2, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] :=
    overlap (eq17 h) (eq302 h) [2, -2, 0, -2, 0, -2, 2, -2] [2, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2] (by decide)
  have hl : value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2] :=
    ((in_context (eq2 h) [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0] [0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2]).trans ((in_context (eq1 h) [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2] [2, -2, 2, -2, 2, 0, 2, -2, 2, -2]).trans ((in_context (eq2 h) [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2] [-2, 2, -2, 2, 0, 2, -2, 2, -2]).trans ((in_context (eq0 h) [-2, 2, 0, 2, -2, 0, -2, 0, 2] [2, -2, 2, 0, 2, -2, 2, -2]).trans ((in_context (eq2 h) [-2, 2, 0, 2, -2, 0, -2, 0] [-2, 2, 0, 2, -2, 2, -2]).trans ((in_context (eq6 h) [-2] [2, -2, 2, -2]).trans (in_context (eq2 h) [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0] [-2, 2, -2])))))))
  have hr : value φ [2, -2, 0, -2, 0, -2, 2, -2, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] :=
    (in_context (eq0 h) [2, -2, 0, -2, 0, -2, 2] [0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1869 (h : Relations φ) : value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2] = value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0] := by
  have h0 : value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0] = value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2] :=
    overlap (eq1794 h) (eq1 h) [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2] [0] (by decide)
  have hl : value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0] = value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0] := rfl
  have hr : value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2] = value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1931 (h : Relations φ) : value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0] := by
  have h0 : value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0] = value φ [2, 0, 2, -2, 0, -2, 0, 2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2] :=
    overlap (eq14 h) (eq1580 h) [2, 0, 2, -2, 0, -2, 0, 2] [-2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0] (by decide)
  have hl : value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0] :=
    ((in_context (eq0 h) [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] [0, 2, 0, -2, 0, 2, -2, 0, 2, 0]).trans ((in_context (eq1 h) [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] [2, 0, -2, 0, 2, -2, 0, 2, 0]).trans ((in_context (eq2 h) [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0] [0, -2, 0, 2, -2, 0, 2, 0]).trans ((in_context (eq1 h) [-2, 2, -2, 0, -2, 0, -2, 2, -2] [-2, 0, 2, -2, 0, 2, 0]).trans (in_context (eq0 h) [-2, 2, -2, 0, -2, 0, -2, 2] [0, 2, -2, 0, 2, 0])))))
  have hr : value φ [2, 0, 2, -2, 0, -2, 0, 2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2] = value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2] :=
    ((in_context (eq2 h) [2, 0, 2, -2, 0, -2, 0] [-2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2]).trans ((in_context (eq6 h) [] [2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2]).trans (in_context (eq2 h) [0, 2, -2, 0, -2, 0, -2, 2, 0] [-2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq1942 (h : Relations φ) : value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2] = value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2] := by
  have h0 : value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2] = value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2] :=
    overlap (eq1869 h) (eq0 h) [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2] [-2] (by decide)
  have hl : value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2] = value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2] := rfl
  have hr : value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2] = value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2007 (h : Relations φ) : value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0] := by
  have h0 : value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2, -2, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0] = value φ [2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2] :=
    overlap (eq101 h) (eq1524 h) [2, -2, 0, -2, 2, 0, 2, 0] [-2, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0] (by decide)
  have hl : value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2, -2, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0] :=
    ((in_context (eq0 h) [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2] [2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0]).trans ((in_context (eq2 h) [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0] [0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0]).trans ((in_context (eq1 h) [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2] [-2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0]).trans ((in_context (eq0 h) [-2, 2, 0, 2, 0, 2, -2, 2, 0] [0, 2, 0, -2, 2, 0, -2, 0, 2, 0]).trans ((in_context (eq1 h) [-2, 2, 0, 2, 0, 2, -2, 2] [2, 0, -2, 2, 0, -2, 0, 2, 0]).trans (in_context (eq2 h) [-2, 2, 0, 2, 0, 2, -2] [0, -2, 2, 0, -2, 0, 2, 0]))))))
  have hr : value φ [2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2] = value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2] :=
    ((in_context (eq12 h) [2] [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2]).trans (in_context (eq0 h) [2, 0, -2, 2, 0, 2, 0, 2, -2, 0] [2, -2, 2, 0, -2, 0, -2, 2, 0, -2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2026 (h : Relations φ) : value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2] := by
  have h0 : value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2] = value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0] :=
    overlap (eq1931 h) (eq0 h) [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0] [-2] (by decide)
  have hl : value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2] := rfl
  have hr : value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0] = value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2027 (h : Relations φ) : value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] = value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2] := by
  have h0 : value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] :=
    overlap (eq1942 h) (eq2 h) [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] [2] (by decide)
  have hl : value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2] := rfl
  have hr : value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] = value φ [2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2028 (h : Relations φ) : value φ [2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] := by
  have h0 : value φ [2, 0, 2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] = value φ [-2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2] :=
    overlap (eq1627 h) (eq2027 h) [-2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0] [2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] (by decide)
  have hl : value φ [2, 0, 2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] = value φ [0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] :=
    ((in_context (eq2 h) [2, 0] [0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2]).trans ((in_context (eq1 h) [2] [2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2]).trans (in_context (eq2 h) [] [0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2])))
  have hr : value φ [-2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2] :=
    ((in_context (eq1782 h) [-2, 0, -2, 0] [0, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq1 h) [-2, 0, -2] [-2, 0, -2, 2, 0, 2, -2, 0, 2, 0, 0, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq0 h) [-2, 0] [0, -2, 2, 0, 2, -2, 0, 2, 0, 0, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq1 h) [-2] [-2, 2, 0, 2, -2, 0, 2, 0, 0, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq0 h) [] [2, 0, 2, -2, 0, 2, 0, 0, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2]).trans (in_context (eq1 h) [2, 0, 2, -2, 0, 2] [0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2]))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2037 (h : Relations φ) : value φ [0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0] = value φ [2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2] := by
  have h0 : value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] = value φ [0, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0] :=
    overlap (eq79 h) (eq152 h) [0, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2] [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] (by decide)
  have hl : value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] = value φ [2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2] :=
    ((in_context (eq96 h) [2, -2, 0, -2, 0, -2, 2, -2] [2, -2, 2, -2, 2]).trans ((in_context (eq3 h) [2, -2, 0, -2, 0] [2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, -2, 2, -2, 2]).trans ((in_context (eq2 h) [2, -2, 0, -2, 0, 2, -2, 2, -2] [-2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, -2, 2, -2, 2]).trans ((in_context (eq0 h) [2, -2, 0, -2, 0, 2, -2, 2] [0, -2, 2, 0, 2, 0, -2, 2, -2, 2, -2, 2, -2, 2]).trans ((in_context (eq3 h) [2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0] [2, -2, 2]).trans ((in_context (eq2 h) [2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2] [-2, 2]).trans ((in_context (eq0 h) [2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] [2]).trans (in_context (eq2 h) [2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2] []))))))))
  have hr : value φ [0, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0] = value φ [0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0] :=
    ((in_context (eq10 h) [0, -2, 0, 2] [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0]).trans ((in_context (eq100 h) [0, -2, 0, 2, 0, -2, 0] [-2, 0, 2, -2, 2, -2, 0]).trans ((in_context (eq0 h) [0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0] [0, 2, -2, 2, -2, 0]).trans ((in_context (eq1 h) [0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2] [2, -2, 2, -2, 0]).trans ((in_context (eq3 h) [0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0] [2, -2, 0]).trans ((in_context (eq2 h) [0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2] [-2, 0]).trans (in_context (eq0 h) [0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2] [0])))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2042 (h : Relations φ) : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] = value φ [2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] := by
  have h0 : value φ [2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2] :=
    overlap (eq283 h) (eq41 h) [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2] [0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2] (by decide)
  have hl : value φ [2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2] = value φ [2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] :=
    ((in_context (eq1 h) [2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2, 2, -2, 2, 0, 2] [2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq2 h) [2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2, 2, -2, 2, 0] [0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq1 h) [2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2, 2, -2, 2] [2, -2, 2, 0, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq2 h) [2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2, 2, -2] [-2, 2, 0, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq0 h) [2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2, 2] [2, 0, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq2 h) [2, 0, 2, 0, -2, 2, -2, 2, 0, 2, -2] [0, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq6 h) [2, 0, 2, 0, -2, 2, -2] [2]).trans (in_context (eq2 h) [2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] []))))))))
  have hr : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0, -2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] :=
    ((in_context (eq0 h) [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2, 0] [0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2]).trans ((in_context (eq1 h) [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, 2] [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2]).trans ((in_context (eq2 h) [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0] [0, -2, 2, -2, 0, -2, 0, -2, 2, -2]).trans ((in_context (eq1 h) [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2] [-2, 2, -2, 0, -2, 0, -2, 2, -2]).trans (in_context (eq0 h) [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0] [2, -2, 0, -2, 0, -2, 2, -2])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2044 (h : Relations φ) : value φ [0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] = value φ [-2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] := by
  have h0 : value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2] = value φ [0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0] :=
    overlap (eq38 h) (eq295 h) [0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2] (by decide)
  have hl : value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 2] = value φ [-2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] :=
    ((in_context (eq21 h) [-2, 2, 0, 2, 0, 2, -2, 2] [2, -2, 2, -2, 2]).trans ((in_context (eq3 h) [-2, 2, 0, 2, 0, 2] [2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 2, -2, 2, -2, 2]).trans ((in_context (eq2 h) [-2, 2, 0, 2, 0] [-2, 2, -2, 2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 2, -2, 2, -2, 2]).trans ((in_context (eq2 h) [-2, 2, 0, 2, 0, -2, 2, -2] [0, 2, -2, 0, -2, 0, 2, -2, 2, 2, -2, 2, -2, 2]).trans ((in_context (eq2 h) [-2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, 2, -2] [-2, 2, -2, 2]).trans ((in_context (eq0 h) [-2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, 2] [2, -2, 2]).trans (in_context (eq2 h) [-2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0] [-2, 2])))))))
  have hr : value φ [0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0] = value φ [0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] :=
    ((in_context (eq8 h) [0, 2, 0, -2] [-2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0]).trans ((in_context (eq17 h) [0, 2, 0, -2, 0, 2, 0] [2, 0, -2, 2, -2, 2, 0]).trans ((in_context (eq2 h) [0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0] [0, -2, 2, -2, 2, 0]).trans ((in_context (eq1 h) [0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2] [-2, 2, -2, 2, 0]).trans ((in_context (eq3 h) [0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, 2] [2, 0]).trans ((in_context (eq2 h) [0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0] [-2, 2, -2, 2, 2, 0]).trans (in_context (eq2 h) [0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] [0])))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2048 (h : Relations φ) : value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] = value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2] := by
  have h0 : value φ [2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 0, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] :=
    overlap (eq15 h) (eq308 h) [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2] [0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2] (by decide)
  have hl : value φ [2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2, 0, 0, 2, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2] = value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2] :=
    ((in_context (eq1 h) [2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2] [2, 0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0] [0, 2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2]).trans ((in_context (eq1 h) [2, 0, 2, -2, 0, -2, 0, 2, -2, 2] [2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [2, 0, 2, -2, 0, -2, 0, 2, -2] [-2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2]).trans ((in_context (eq0 h) [2, 0, 2, -2, 0, -2, 0, 2] [2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [2, 0, 2, -2, 0, -2, 0] [-2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2]).trans ((in_context (eq6 h) [] [2, -2, 2, -2, 0, 2, 0, 2]).trans (in_context (eq2 h) [0, 2, -2, 0, -2, 0, -2, 2, 0] [-2, 2, -2, 0, 2, 0, 2]))))))))
  have hr : value φ [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] :=
    ((in_context (eq0 h) [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] [0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2]).trans ((in_context (eq1 h) [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] [2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2]).trans ((in_context (eq2 h) [-2, 2, -2, 0, -2, 0, -2, 2, -2, 0] [0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2]).trans ((in_context (eq1 h) [-2, 2, -2, 0, -2, 0, -2, 2, -2] [-2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2]).trans (in_context (eq0 h) [-2, 2, -2, 0, -2, 0, -2, 2] [0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2066 (h : Relations φ) : value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2] = value φ [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0] := by
  have h0 : value φ [-2, 0, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0] = value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 2, -2, 2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2] :=
    overlap (eq433 h) (eq171 h) [2, 0, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2] [0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0] (by decide)
  have hl : value φ [-2, 0, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0] = value φ [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0] :=
    ((in_context (eq103 h) [-2, 0] [2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0]).trans ((in_context (eq2 h) [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0] [0, -2, 0, 2, 0, -2, 2, 0, -2, 0]).trans ((in_context (eq1 h) [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2] [-2, 0, 2, 0, -2, 2, 0, -2, 0]).trans ((in_context (eq0 h) [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0] [0, 2, 0, -2, 2, 0, -2, 0]).trans ((in_context (eq1 h) [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2] [2, 0, -2, 2, 0, -2, 0]).trans (in_context (eq2 h) [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2] [0, -2, 2, 0, -2, 0]))))))
  have hr : value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 2, -2, 2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2] = value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2] :=
    ((in_context (eq2 h) [2, 0, 2, 0, 2, -2, 0, -2, 0, 2, -2] [-2, 2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2]).trans ((in_context (eq0 h) [2, 0, 2, 0, 2, -2, 0, -2, 0, 2] [2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2]).trans ((in_context (eq2 h) [2, 0, 2, 0, 2, -2, 0, -2, 0] [0, -2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2]).trans ((in_context (eq1 h) [2, 0, 2, 0, 2, -2, 0, -2] [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2]).trans (in_context (eq0 h) [2, 0, 2, 0, 2, -2, 0] [2, -2, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2069 (h : Relations φ) : value φ [2, 0, 2, 0, -2, 0, 2, 0, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [0, 2, 0, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0] := by
  have h0 : value φ [0, 2, 0, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0] = value φ [2, 0, 2, 0, -2, 0, 2, 0, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] :=
    overlap (eq494 h) (eq8 h) [2, 0, 2, 0, -2, 0, 2, 0, -2] [0, 2, 0] (by decide)
  have hl : value φ [0, 2, 0, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0] = value φ [0, 2, 0, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0] := rfl
  have hr : value φ [2, 0, 2, 0, -2, 0, 2, 0, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [2, 0, 2, 0, -2, 0, 2, 0, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2123 (h : Relations φ) : value φ [0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0] = value φ [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2] := by
  have h0 : value φ [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2] = value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0] :=
    overlap (eq1391 h) (eq1574 h) [0, -2, 0, -2, 2, 0, 2, 0, 2] [-2, 0, 2, 0, -2, 0, 2, -2, 0, 2] (by decide)
  have hl : value φ [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2] = value φ [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2] :=
    ((in_context (eq0 h) [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0] [0, 2, 0, -2, 0, 2, -2, 0, 2]).trans ((in_context (eq1 h) [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2] [2, 0, -2, 0, 2, -2, 0, 2]).trans ((in_context (eq2 h) [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0] [0, -2, 0, 2, -2, 0, 2]).trans ((in_context (eq1 h) [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2] [-2, 0, 2, -2, 0, 2]).trans (in_context (eq0 h) [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] [0, 2, -2, 0, 2])))))
  have hr : value φ [0, -2, 0, -2, 2, 0, 2, 0, 2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0] = value φ [0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0] :=
    ((in_context (eq2 h) [0, -2, 0, -2, 2, 0, 2, 0] [0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0]).trans ((in_context (eq1 h) [0, -2, 0, -2, 2, 0, 2] [2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0]).trans (in_context (eq2 h) [0, -2, 0, -2, 2, 0] [-2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2142 (h : Relations φ) : value φ [2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] := by
  have h0 : value φ [2, -2, 0, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2] :=
    overlap (eq1630 h) (eq2027 h) [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2] [0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] (by decide)
  have hl : value φ [2, -2, 0, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] = value φ [0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] :=
    ((in_context (eq1 h) [2, -2] [-2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2]).trans ((in_context (eq0 h) [2] [2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2]).trans (in_context (eq2 h) [] [0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2])))
  have hr : value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2] :=
    (in_context (eq1638 h) [] [0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2164 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2] = value φ [2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] := by
  have h0 : value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 0, -2, 2, 0] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2] :=
    overlap (eq261 h) (eq6 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0] [0, -2, 0, -2, 2, 0] (by decide)
  have hl : value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 0, -2, 2, 0] = value φ [2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] :=
    ((in_context (eq5 h) [2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2] [-2, 2, 0]).trans ((in_context (eq4 h) [2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] [-2, 0, -2, 0, -2, -2, 2, 0]).trans ((in_context (eq1 h) [2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2] [2, 0, 2, 0, 2, -2, 0, -2, 0, -2, -2, 2, 0]).trans ((in_context (eq12 h) [2, 0, 2, 0, 2, -2, 0, 2] [-2, 0, -2, -2, 2, 0]).trans ((in_context (eq0 h) [2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0] [0, -2, -2, 2, 0]).trans ((in_context (eq1 h) [2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2] [-2, -2, 2, 0]).trans ((in_context (eq0 h) [2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2] [-2, 2, 0]).trans (in_context (eq29 h) [2, 0, 2, 0] []))))))))
  have hr : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2] :=
    ((in_context (eq1 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2] [2, -2, 0, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq2 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0] [-2, 0, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq5 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0] [-2, 2, 0, 2]).trans ((in_context (eq1 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2] [-2, 0, -2, 0, -2, -2, 2, 0, 2]).trans (in_context (eq0 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0] [2, 0, 2])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2165 (h : Relations φ) : value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] = value φ [-2, 2, -2, 0, -2, 0, 2, 0, 2] := by
  have h0 : value φ [0, -2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2] = value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] :=
    overlap (eq420 h) (eq2164 h) [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0] [0, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2] (by decide)
  have hl : value φ [0, -2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2] = value φ [-2, 2, -2, 0, -2, 0, 2, 0, 2] :=
    ((in_context (eq4 h) [0, -2, 0] [2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2]).trans ((in_context (eq1 h) [0, -2] [2, 0, 2, 0, 2, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [0, -2, 2, 0, 2, 0] [0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2]).trans ((in_context (eq1 h) [0, -2, 2, 0, 2] [2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [0, -2, 2, 0] [0, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2]).trans ((in_context (eq1 h) [0, -2, 2] [2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [0, -2] [-2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2]).trans ((in_context (eq0 h) [0] [0, -2, 2, -2, 0, -2, 0, 2, 0, 2]).trans (in_context (eq1 h) [] [-2, 2, -2, 0, -2, 0, 2, 0, 2])))))))))
  have hr : value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] :=
    (in_context (eq423 h) [] [2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2166 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] = value φ [0, -2, 2, -2, 0, -2, 0, 2, 0, 2] := by
  have h0 : value φ [-2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2] = value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] :=
    overlap (eq419 h) (eq2164 h) [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0] [0, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2] (by decide)
  have hl : value φ [-2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2] = value φ [0, -2, 2, -2, 0, -2, 0, 2, 0, 2] :=
    ((in_context (eq4 h) [-2, 0] [2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2]).trans ((in_context (eq1 h) [-2] [2, 0, 2, 0, 2, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [-2, 2, 0, 2, 0] [0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2]).trans ((in_context (eq1 h) [-2, 2, 0, 2] [2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [-2, 2, 0] [0, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2]).trans ((in_context (eq1 h) [-2, 2] [2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [-2] [-2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2]).trans (in_context (eq0 h) [] [0, -2, 2, -2, 0, -2, 0, 2, 0, 2]))))))))
  have hr : value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] :=
    (in_context (eq421 h) [] [2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2167 (h : Relations φ) : value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0] = value φ [-2, 2, -2, 0, -2, 0, 2, 0, 2, -2] := by
  have h0 : value φ [-2, 2, -2, 0, -2, 0, 2, 0, 2, -2] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0] :=
    overlap (eq2165 h) (eq0 h) [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0] [-2] (by decide)
  have hl : value φ [-2, 2, -2, 0, -2, 0, 2, 0, 2, -2] = value φ [-2, 2, -2, 0, -2, 0, 2, 0, 2, -2] := rfl
  have hr : value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2178 (h : Relations φ) : value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2] = value φ [-2, 2, -2, 0, -2, 0, 2, 0, 2, -2, 0] := by
  have h0 : value φ [-2, 2, -2, 0, -2, 0, 2, 0, 2, -2, 0] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2] :=
    overlap (eq2167 h) (eq1 h) [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2] [0] (by decide)
  have hl : value φ [-2, 2, -2, 0, -2, 0, 2, 0, 2, -2, 0] = value φ [-2, 2, -2, 0, -2, 0, 2, 0, 2, -2, 0] := rfl
  have hr : value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2182 (h : Relations φ) : value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2] = value φ [-2, 2, -2, 0, -2, 0, 2, 0, 2, -2, 0, -2] := by
  have h0 : value φ [-2, 2, -2, 0, -2, 0, 2, 0, 2, -2, 0, -2] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2] :=
    overlap (eq2178 h) (eq0 h) [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2] [-2] (by decide)
  have hl : value φ [-2, 2, -2, 0, -2, 0, 2, 0, 2, -2, 0, -2] = value φ [-2, 2, -2, 0, -2, 0, 2, 0, 2, -2, 0, -2] := rfl
  have hr : value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2186 (h : Relations φ) : value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0] = value φ [-2, 2, -2, 0, -2, 0, 2, 0, 2, -2, 0, -2, 2] := by
  have h0 : value φ [-2, 2, -2, 0, -2, 0, 2, 0, 2, -2, 0, -2, 2] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0] :=
    overlap (eq2182 h) (eq2 h) [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0] [2] (by decide)
  have hl : value φ [-2, 2, -2, 0, -2, 0, 2, 0, 2, -2, 0, -2, 2] = value φ [-2, 2, -2, 0, -2, 0, 2, 0, 2, -2, 0, -2, 2] := rfl
  have hr : value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2189 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] = value φ [0, -2, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 2] := by
  have h0 : value φ [0, -2, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 2] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0] :=
    overlap (eq2166 h) (eq22 h) [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2] [0, 2, -2, 2] (by decide)
  have hl : value φ [0, -2, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 2] = value φ [0, -2, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 2] := rfl
  have hr : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0, -2, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0] = value φ [-2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] :=
    ((in_context (eq0 h) [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2, 0] [0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0]).trans ((in_context (eq1 h) [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, -2] [-2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0]).trans ((in_context (eq0 h) [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0] [2, -2, 0, 2, 0, -2, 2, 0, 2, 0]).trans ((in_context (eq56 h) [-2, 0, 2, 0, 2] [0, 2, 0]).trans (in_context (eq5 h) [-2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, -2, 2] [2, 0])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2192 (h : Relations φ) : value φ [0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] = value φ [2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2] := by
  have h0 : value φ [0, 2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] :=
    overlap (eq1623 h) (eq2164 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2] [0, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2] (by decide)
  have hl : value φ [0, 2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2] = value φ [2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2] :=
    ((in_context (eq4 h) [0] [2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2]).trans ((in_context (eq1 h) [] [2, 0, 2, 0, 2, 2, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2]).trans (in_context (eq2 h) [2, 0, 2, 0] [-2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2])))
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] = value φ [0, 2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] :=
    ((in_context (eq1632 h) [] [2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2]).trans (in_context (eq2 h) [0, 2, -2] [2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2193 (h : Relations φ) : value φ [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2] = value φ [-2, 2, 0, 2, -2, 2, 0] := by
  have h0 : value φ [-2, 0, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] = value φ [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2] :=
    overlap (eq588 h) (eq2192 h) [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2] [-2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] (by decide)
  have hl : value φ [-2, 0, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2] = value φ [-2, 2, 0, 2, -2, 2, 0] :=
    ((in_context (eq0 h) [-2, 0, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2] [2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq2 h) [-2, 0, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0] [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq1 h) [-2, 0, 2, -2, 0, 2, 0, -2, 2, 0, 2] [2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq2 h) [-2, 0, 2, -2, 0, 2, 0, -2, 2, 0] [0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq1 h) [-2, 0, 2, -2, 0, 2, 0, -2, 2] [-2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq44 h) [-2] [-2, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq0 h) [-2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2] [2, 0, 2, -2, 0, -2]).trans ((in_context (eq2 h) [-2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0] [0, 2, -2, 0, -2]).trans ((in_context (eq1 h) [-2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2] [2, -2, 0, -2]).trans ((in_context (eq2 h) [-2, 2, 0, 2, -2, 2, 0, -2, 0, -2] [-2, 0, -2]).trans ((in_context (eq0 h) [-2, 2, 0, 2, -2, 2, 0, -2, 0] [0, -2]).trans ((in_context (eq1 h) [-2, 2, 0, 2, -2, 2, 0, -2] [-2]).trans (in_context (eq0 h) [-2, 2, 0, 2, -2, 2, 0] [])))))))))))))
  have hr : value φ [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2] = value φ [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2194 (h : Relations φ) : value φ [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 2, 0, 2, 0, 2] = value φ [-2, 2, 0, 2, -2, 0] := by
  have h0 : value φ [-2, 2, 0, 2, -2, 2, 0, 0, 2, 0] = value φ [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0, 0, 2, 0, 2, 0, 2] :=
    overlap (eq2193 h) (eq4 h) [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0] [0, 2, 0] (by decide)
  have hl : value φ [-2, 2, 0, 2, -2, 2, 0, 0, 2, 0] = value φ [-2, 2, 0, 2, -2, 0] :=
    ((in_context (eq1 h) [-2, 2, 0, 2, -2, 2] [2, 0]).trans (in_context (eq2 h) [-2, 2, 0, 2, -2] [0]))
  have hr : value φ [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0, 0, 2, 0, 2, 0, 2] = value φ [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 2, 0, 2, 0, 2] :=
    (in_context (eq1 h) [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2] [2, 0, 2, 0, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2198 (h : Relations φ) : value φ [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0, 2] = value φ [-2, 2, 0, 2, -2, 2, 0, 2, 0] := by
  have h0 : value φ [-2, 2, 0, 2, -2, 0, 0, 2, 0, 2, 0] = value φ [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 2, 0, 2, 0, 0, 2, 0, 2, 0, 2] :=
    overlap (eq2194 h) (eq4 h) [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 2, 0, 2, 0] [0, 2, 0, 2, 0] (by decide)
  have hl : value φ [-2, 2, 0, 2, -2, 0, 0, 2, 0, 2, 0] = value φ [-2, 2, 0, 2, -2, 2, 0, 2, 0] :=
    (in_context (eq1 h) [-2, 2, 0, 2, -2] [2, 0, 2, 0])
  have hr : value φ [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 2, 0, 2, 0, 0, 2, 0, 2, 0, 2] = value φ [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0, 2] :=
    ((in_context (eq1 h) [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 2, 0, 2] [2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 2, 0] [0, 2, 0, 2]).trans ((in_context (eq1 h) [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 2] [2, 0, 2]).trans (in_context (eq2 h) [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2] [0, 2]))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2203 (h : Relations φ) : value φ [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0] = value φ [-2, 2, 0, 2, -2, 2, 0, 2, 0, 2] := by
  have h0 : value φ [-2, 2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0] :=
    overlap (eq2198 h) (eq2 h) [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0] [2] (by decide)
  have hl : value φ [-2, 2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [-2, 2, 0, 2, -2, 2, 0, 2, 0, 2] := rfl
  have hr : value φ [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0] = value φ [0, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2240 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2] = value φ [0, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0] := by
  have h0 : value φ [2, 0, -2, 0, -2, 2, 0, 2, -2, 2, 0, -2, 0, -2, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, 0, -2, -2, 2, 0, 2, -2, 2, 0, 2, 0, 2] :=
    overlap (eq594 h) (eq2203 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, 0, -2] [-2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0] (by decide)
  have hl : value φ [2, 0, -2, 0, -2, 2, 0, 2, -2, 2, 0, -2, 0, -2, -2, 0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0] = value φ [0, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0] :=
    ((in_context (eq0 h) [2, 0, -2, 0, -2, 2, 0, 2, -2, 2, 0, -2, 0] [0, -2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0]).trans ((in_context (eq1 h) [2, 0, -2, 0, -2, 2, 0, 2, -2, 2, 0, -2] [-2, 0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0]).trans ((in_context (eq0 h) [2, 0, -2, 0, -2, 2, 0, 2, -2, 2, 0] [0, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0]).trans ((in_context (eq1 h) [2, 0, -2, 0, -2, 2, 0, 2, -2, 2] [2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0]).trans ((in_context (eq2 h) [2, 0, -2, 0, -2, 2, 0, 2, -2] [-2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0]).trans ((in_context (eq0 h) [2, 0, -2, 0, -2, 2, 0, 2] [2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0]).trans ((in_context (eq2 h) [2, 0, -2, 0, -2, 2, 0] [0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0]).trans ((in_context (eq1 h) [2, 0, -2, 0, -2, 2] [2, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0]).trans ((in_context (eq2 h) [2, 0, -2, 0, -2] [-2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0]).trans ((in_context (eq0 h) [2, 0, -2, 0] [0, -2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0]).trans ((in_context (eq1 h) [2, 0, -2] [-2, 2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0]).trans ((in_context (eq0 h) [2, 0] [2, 0, 2, 0, -2, 0, -2, 2, -2, 0, -2, 0]).trans (in_context (eq4 h) [] [-2, 0, -2, 2, -2, 0, -2, 0])))))))))))))
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, 0, -2, -2, 2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [-2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2] :=
    ((in_context (eq0 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, 0] [2, 0, 2, -2, 2, 0, 2, 0, 2]).trans (in_context (eq29 h) [-2, 2, 0, 2, 0] [2, 0, 2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2241 (h : Relations φ) : value φ [0, 2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 2, 0, 2] := by
  have h0 : value φ [2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 0, 2, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2] = value φ [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0] :=
    overlap (eq370 h) (eq2240 h) [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0] [2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2] (by decide)
  have hl : value φ [2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 0, 2, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 2, 0, 2] :=
    ((in_context (eq2 h) [2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2, 0] [0, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq1 h) [2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0, -2] [-2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq0 h) [2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2, 0] [0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq1 h) [2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0, -2] [-2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq0 h) [2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 2, 0] [0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq1 h) [2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 2] [-2, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq3 h) [2, 0, -2, 0, -2, 0, 2] [2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq2 h) [2, 0, -2, 0, -2, 0] [-2, 2, -2, 2, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq2 h) [2, 0, -2, 0, -2, 0, -2, 2, -2] [-2, 2, 0, 2, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq0 h) [2, 0, -2, 0, -2, 0, -2, 2] [2, 0, 2, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq2 h) [2, 0, -2, 0, -2, 0, -2] [0, 2, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq5 h) [2, 0] [2, -2, 0, -2, 2, 0, 2]).trans (in_context (eq1 h) [2] [-2, 0, -2, 0, -2, 2, -2, 0, -2, 2, 0, 2])))))))))))))
  have hr : value φ [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2, 0, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0] = value φ [0, 2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] :=
    ((in_context (eq1 h) [0, 2, 0, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 0, -2] [2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 0, -2, 0]).trans ((in_context (eq432 h) [0, 2, 0, -2, 0, -2, 0] [0, -2, 2, -2, 0, -2, 0]).trans ((in_context (eq1 h) [0, 2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, -2] [-2, 2, -2, 0, -2, 0]).trans (in_context (eq0 h) [0, 2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0] [2, -2, 0, -2, 0]))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2242 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, -2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] = value φ [0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2] := by
  have h0 : value φ [-2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] = value φ [2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 2, 0, 2] :=
    overlap (eq319 h) (eq2241 h) [2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2] [0, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] (by decide)
  have hl : value φ [-2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 0, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] = value φ [-2, 2, 0, 2, 0, -2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] :=
    ((in_context (eq5 h) [-2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0] [2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0]).trans ((in_context (eq1 h) [-2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2] [-2, 0, -2, 0, -2, 2, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0]).trans ((in_context (eq3 h) [-2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0]).trans ((in_context (eq151 h) [-2, 2, -2, 0, 2] [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0]).trans ((in_context (eq149 h) [-2, 2] [-2, 0, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0]).trans ((in_context (eq0 h) [-2, 2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2] [0, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0]).trans ((in_context (eq1 h) [-2, 2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0, 2] [2, 0, 2, -2, 0, 2, -2, 0, -2, 0]).trans ((in_context (eq2 h) [-2, 2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 0] [0, 2, -2, 0, 2, -2, 0, -2, 0]).trans ((in_context (eq1 h) [-2, 2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2] [2, -2, 0, 2, -2, 0, -2, 0]).trans ((in_context (eq3 h) [-2, 2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2] [0, 2, -2, 0, -2, 0]).trans ((in_context (eq2 h) [-2, 2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] [-2, 2, -2, 2, 0, 2, -2, 0, -2, 0]).trans ((in_context (eq30 h) [-2, 2, 0, 2, 0, -2, 0] [0]).trans (in_context (eq1 h) [-2, 2, 0, 2, 0, -2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] [])))))))))))))
  have hr : value φ [2, 0, 2, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 2, 0, 2] = value φ [0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2] :=
    ((in_context (eq1270 h) [] [-2, 0, -2, 0, -2, 2, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq0 h) [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0] [0, -2, 0, -2, 2, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq1 h) [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2] [-2, 0, -2, 2, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq0 h) [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0] [0, -2, 2, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq1 h) [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2] [-2, 2, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq0 h) [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2] [2, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq2 h) [0, 2, -2, 0, -2, 0, -2, 2, 0, -2] [-2, 0, -2, 2, 0, 2]).trans ((in_context (eq0 h) [0, 2, -2, 0, -2, 0, -2, 2, 0] [0, -2, 2, 0, 2]).trans (in_context (eq1 h) [0, 2, -2, 0, -2, 0, -2, 2] [-2, 2, 0, 2])))))))))
  exact hl.symm.trans (h0.trans hr)

private theorem eq2243 (h : Relations φ) : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 0, 2, 0] = value φ [0, 2, 0, -2, 0, 2, 0, -2] := by
  have h0 : value φ [0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] = value φ [-2, 2, 0, 2, 0, -2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2] :=
    overlap (eq2242 h) (eq452 h) [-2, 2, 0, 2, 0, -2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2] [0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] (by decide)
  have hl : value φ [0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] = value φ [0, 2, 0, -2, 0, 2, 0, -2] :=
    ((in_context (eq695 h) [0, 2] [-2, 0, -2, 0, 2, -2, 2, -2, 2]).trans ((in_context (eq0 h) [0, 2, 0, -2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0] [0, -2, 0, 2, -2, 2, -2, 2]).trans ((in_context (eq1 h) [0, 2, 0, -2, 0, 2, 0, 2, -2, 2, -2, 0, -2] [-2, 0, 2, -2, 2, -2, 2]).trans ((in_context (eq0 h) [0, 2, 0, -2, 0, 2, 0, 2, -2, 2, -2, 0] [0, 2, -2, 2, -2, 2]).trans ((in_context (eq1 h) [0, 2, 0, -2, 0, 2, 0, 2, -2, 2, -2] [2, -2, 2, -2, 2]).trans ((in_context (eq3 h) [0, 2, 0, -2, 0, 2, 0, 2] [2, -2, 2]).trans ((in_context (eq2 h) [0, 2, 0, -2, 0, 2, 0] [-2, 2, -2, 2, 2, -2, 2]).trans ((in_context (eq2 h) [0, 2, 0, -2, 0, 2, 0, -2, 2, -2] [-2, 2]).trans ((in_context (eq0 h) [0, 2, 0, -2, 0, 2, 0, -2, 2] [2]).trans (in_context (eq2 h) [0, 2, 0, -2, 0, 2, 0, -2] []))))))))))
  have hr : value φ [-2, 2, 0, 2, 0, -2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, -2] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 0, 2, 0] :=
    ((in_context (eq2007 h) [-2, 2, 0, 2, 0, -2, 0, -2, 0] []).trans ((in_context (eq422 h) [-2] [2, -2, 0, -2, 2, 0, -2, 0, 2, 0]).trans ((in_context (eq2 h) [-2, 0, 2, 0, -2, 0, -2, 0, -2] [-2, 0, -2, 2, 0, -2, 0, 2, 0]).trans ((in_context (eq0 h) [-2, 0, 2, 0, -2, 0, -2, 0] [0, -2, 2, 0, -2, 0, 2, 0]).trans ((in_context (eq1 h) [-2, 0, 2, 0, -2, 0, -2] [-2, 2, 0, -2, 0, 2, 0]).trans (in_context (eq0 h) [-2, 0, 2, 0, -2, 0] [2, 0, -2, 0, 2, 0]))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2244 (h : Relations φ) : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 0, 2] = value φ [0, 2, 0, -2, 0, 2, 0, -2, 0] := by
  have h0 : value φ [0, 2, 0, -2, 0, 2, 0, -2, 0] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 0, 2] :=
    overlap (eq2243 h) (eq1 h) [-2, 0, 2, 0, -2, 0, 2, 0, -2, 0, 2] [0] (by decide)
  have hl : value φ [0, 2, 0, -2, 0, 2, 0, -2, 0] = value φ [0, 2, 0, -2, 0, 2, 0, -2, 0] := rfl
  have hr : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 0, 2] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2245 (h : Relations φ) : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 0] = value φ [0, 2, 0, -2, 0, 2, 0, -2, 0, 2] := by
  have h0 : value φ [0, 2, 0, -2, 0, 2, 0, -2, 0, 2] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 0] :=
    overlap (eq2244 h) (eq2 h) [-2, 0, 2, 0, -2, 0, 2, 0, -2, 0] [2] (by decide)
  have hl : value φ [0, 2, 0, -2, 0, 2, 0, -2, 0, 2] = value φ [0, 2, 0, -2, 0, 2, 0, -2, 0, 2] := rfl
  have hr : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 0] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2246 (h : Relations φ) : value φ [0, 2, 0, -2, 0, 2, 0, -2, 0, 2, 0] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2] := by
  have h0 : value φ [0, 2, 0, -2, 0, 2, 0, -2, 0, 2, 0] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2] :=
    overlap (eq0 h) (eq2243 h) [-2] [0, 2, 0, -2, 0, 2, 0, -2, 0, 2, 0] (by decide)
  have hl : value φ [0, 2, 0, -2, 0, 2, 0, -2, 0, 2, 0] = value φ [0, 2, 0, -2, 0, 2, 0, -2, 0, 2, 0] := rfl
  have hr : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq2247 (h : Relations φ) : value φ [2, 0, -2, 0, 2, 0, -2, 0, 2, 0] = value φ [0, -2, 0, 2, 0, -2, 0, 2, 0, -2] := by
  have h0 : value φ [2, 0, -2, 0, 2, 0, -2, 0, 2, 0] = value φ [0, -2, 0, 2, 0, -2, 0, 2, 0, -2] :=
    overlap (eq1 h) (eq2246 h) [0] [2, 0, -2, 0, 2, 0, -2, 0, 2, 0] (by decide)
  have hl : value φ [2, 0, -2, 0, 2, 0, -2, 0, 2, 0] = value φ [2, 0, -2, 0, 2, 0, -2, 0, 2, 0] := rfl
  have hr : value φ [0, -2, 0, 2, 0, -2, 0, 2, 0, -2] = value φ [0, -2, 0, 2, 0, -2, 0, 2, 0, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq2249 (h : Relations φ) : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2] = value φ [0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] := by
  have h0 : value φ [0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 0, 0, 2, 0, 2, 0, 2] :=
    overlap (eq2243 h) (eq4 h) [-2, 0, 2, 0, -2, 0, 2, 0, -2, 0] [2, 0, 2, 0] (by decide)
  have hl : value φ [0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] = value φ [0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] := rfl
  have hr : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 0, 0, 2, 0, 2, 0, 2] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2] :=
    (in_context (eq1 h) [-2, 0, 2, 0, -2, 0, 2, 0, -2] [2, 0, 2, 0, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2250 (h : Relations φ) : value φ [2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0] := by
  have h0 : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 0, -2, 0, 2, 0, -2, 0] = value φ [2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0, 2, 0, -2, 0, 2, 0, -2, 0, 2] :=
    overlap (eq314 h) (eq2245 h) [2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2] [0, -2, 0, 2, 0, -2, 0] (by decide)
  have hl : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 0, -2, 0, 2, 0, -2, 0] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0] :=
    ((in_context (eq1 h) [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0, -2] [-2, 0, 2, 0, -2, 0]).trans ((in_context (eq0 h) [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2, 0] [0, 2, 0, -2, 0]).trans ((in_context (eq1 h) [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, 2] [2, 0, -2, 0]).trans ((in_context (eq2 h) [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0] [0, -2, 0]).trans ((in_context (eq1 h) [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2] [-2, 0]).trans (in_context (eq0 h) [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2] [0]))))))
  have hr : value φ [2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0, 2, 0, -2, 0, 2, 0, -2, 0, 2] = value φ [2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] :=
    ((in_context (eq4 h) [2, -2, 2, -2, 2, 0, 2, -2, 2, -2, 0] [-2, 0, 2, 0, -2, 0, 2]).trans ((in_context (eq1 h) [2, -2, 2, -2, 2, 0, 2, -2, 2, -2] [2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2]).trans ((in_context (eq277 h) [2] [0, -2, 0, 2]).trans ((in_context (eq1 h) [2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, -2] [-2, 0, 2]).trans ((in_context (eq0 h) [2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0] [0, 2]).trans ((in_context (eq1 h) [2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2] [2]).trans (in_context (eq2 h) [2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2] [])))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2252 (h : Relations φ) : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] = value φ [0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2] := by
  have h0 : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] = value φ [0, 2, 0, -2, 0, 2, 0, -2, 0, 0, 2, 0, 2, 0, 2] :=
    overlap (eq2246 h) (eq4 h) [0, 2, 0, -2, 0, 2, 0, -2, 0] [2, 0, 2, 0] (by decide)
  have hl : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] := rfl
  have hr : value φ [0, 2, 0, -2, 0, 2, 0, -2, 0, 0, 2, 0, 2, 0, 2] = value φ [0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2] :=
    (in_context (eq1 h) [0, 2, 0, -2, 0, 2, 0, -2] [2, 0, 2, 0, 2])
  exact hl.symm.trans (h0.trans hr)

private theorem eq2253 (h : Relations φ) : value φ [0, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] = value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2] := by
  have h0 : value φ [0, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, 0, -2, 0, -2, 0, -2] :=
    overlap (eq2245 h) (eq5 h) [-2, 0, 2, 0, -2, 0, 2, 0] [-2, 0, -2, 0] (by decide)
  have hl : value φ [0, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] = value φ [0, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] := rfl
  have hr : value φ [-2, 0, 2, 0, -2, 0, 2, 0, 0, -2, 0, -2, 0, -2] = value φ [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2] :=
    (in_context (eq1 h) [-2, 0, 2, 0, -2, 0, 2] [-2, 0, -2, 0, -2])
  exact hl.symm.trans (h0.trans hr)

private theorem eq2254 (h : Relations φ) : value φ [2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] = value φ [0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2] := by
  have h0 : value φ [2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] = value φ [0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2] :=
    overlap (eq1 h) (eq2253 h) [0] [2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] (by decide)
  have hl : value φ [2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] = value φ [2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] := rfl
  have hr : value φ [0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2] = value φ [0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq2258 (h : Relations φ) : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] = value φ [0, -2] := by
  have h0 : value φ [0, -2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] :=
    inclusion (eq1624 h) (eq2252 h) [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2] [-2, 2] (by decide)
  have hl : value φ [0, -2] = value φ [0, -2] := rfl
  have hr : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] :=
    ((in_context (eq8 h) [2, -2, 0, -2, 0, -2, 2, 0, -2] [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2]).trans ((in_context (eq2 h) [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2] [0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2]).trans ((in_context (eq5 h) [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2] [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2]).trans ((in_context (eq0 h) [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 0] [0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2]).trans (in_context (eq1 h) [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2] [2, 0, -2, 2, 0, 2, 0, 2, -2, 2])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2259 (h : Relations φ) : value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2] = value φ [-2, 0, -2, 0, -2, 2, 0, 2] := by
  have h0 : value φ [0, -2, 0, -2, 0, -2, 0, 2, 0, 2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2, 0] :=
    overlap (eq2258 h) (eq1513 h) [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2] [0, -2, 0, -2, 0, 2, 0, 2] (by decide)
  have hl : value φ [0, -2, 0, -2, 0, -2, 0, 2, 0, 2] = value φ [-2, 0, -2, 0, -2, 2, 0, 2] :=
    ((in_context (eq5 h) [0] [2, 0, 2]).trans (in_context (eq1 h) [] [-2, 0, -2, 0, -2, 2, 0, 2]))
  have hr : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2] :=
    ((in_context (eq2 h) [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2] [0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, 2, 0]).trans ((in_context (eq1422 h) [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2] [2, 0]).trans ((in_context (eq118 h) [2, -2, 0, -2, 0, -2, 2, 0] [2, -2, 2, -2, 0, -2, 2, 2, 0]).trans ((in_context (eq6 h) [2, -2, 0, -2, 0, -2] [-2, 0, 2, -2, 2, 2, -2, 2, -2, 0, -2, 2, 2, 0]).trans ((in_context (eq5 h) [2] [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, -2, 2, 2, -2, 2, -2, 0, -2, 2, 2, 0]).trans ((in_context (eq2 h) [2, 0, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, -2] [-2, 2, -2, 0, -2, 2, 2, 0]).trans ((in_context (eq0 h) [2, 0, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2] [2, -2, 0, -2, 2, 2, 0]).trans ((in_context (eq2 h) [2, 0, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0] [-2, 0, -2, 2, 2, 0]).trans ((in_context (eq2 h) [2, 0, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2] [0]).trans ((in_context (eq5 h) [2, 0, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2] []).trans ((in_context (eq8 h) [2, 0, -2, 0, -2, 0, -2] [-2, 0, -2, 0, -2]).trans ((in_context (eq5 h) [2, 0] [2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2]).trans (in_context (eq1 h) [2] [-2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2])))))))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2260 (h : Relations φ) : value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] = value φ [-2, 0, -2, 0, -2] := by
  have h0 : value φ [-2, 0, -2, 0, -2, 2, 0, 2, 2, 0, 2] = value φ [2, -2, 0, -2, 0, -2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] :=
    overlap (eq2259 h) (eq1585 h) [2, -2, 0, -2, 0, -2] [2, 0, 2] (by decide)
  have hl : value φ [-2, 0, -2, 0, -2, 2, 0, 2, 2, 0, 2] = value φ [-2, 0, -2, 0, -2] :=
    ((in_context (eq2 h) [-2, 0, -2, 0, -2, 2, 0] [0, 2]).trans ((in_context (eq1 h) [-2, 0, -2, 0, -2, 2] [2]).trans (in_context (eq2 h) [-2, 0, -2, 0, -2] [])))
  have hr : value φ [2, -2, 0, -2, 0, -2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] = value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] :=
    (in_context (eq5 h) [2] [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2261 (h : Relations φ) : value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2] = value φ [0, -2, 0, -2, 0, -2] := by
  have h0 : value φ [-2, 0, -2, 0, -2, 2, 0, 2, 2, 0, 2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] :=
    overlap (eq2259 h) (eq8 h) [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2] [2, 0, 2, 0] (by decide)
  have hl : value φ [-2, 0, -2, 0, -2, 2, 0, 2, 2, 0, 2, 0] = value φ [0, -2, 0, -2, 0, -2] :=
    ((in_context (eq2 h) [-2, 0, -2, 0, -2, 2, 0] [0, 2, 0]).trans ((in_context (eq1 h) [-2, 0, -2, 0, -2, 2] [2, 0]).trans ((in_context (eq2 h) [-2, 0, -2, 0, -2] [0]).trans (in_context (eq5 h) [] []))))
  have hr : value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2] :=
    ((in_context (eq5 h) [2, -2, 0, -2, 0, -2, 2, 0, 2] [2, 0, 2, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq8 h) [] [-2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq1585 h) [0] [-2, 0, -2, 0, -2, 2]).trans (in_context (eq1 h) [] [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2]))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2262 (h : Relations φ) : value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2] = value φ [0, -2, 0, -2, 0, -2, 2] := by
  have h0 : value φ [-2, 0, -2, 0, -2, 2, 0, 2, 2, 0, 2, 0, 2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2] :=
    overlap (eq2259 h) (eq9 h) [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2] [2, 0, 2, 0, 2] (by decide)
  have hl : value φ [-2, 0, -2, 0, -2, 2, 0, 2, 2, 0, 2, 0, 2] = value φ [0, -2, 0, -2, 0, -2, 2] :=
    ((in_context (eq2 h) [-2, 0, -2, 0, -2, 2, 0] [0, 2, 0, 2]).trans ((in_context (eq1 h) [-2, 0, -2, 0, -2, 2] [2, 0, 2]).trans ((in_context (eq2 h) [-2, 0, -2, 0, -2] [0, 2]).trans (in_context (eq5 h) [] [2]))))
  have hr : value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2] = value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2] :=
    ((in_context (eq2 h) [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2] [0, 2, 0, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq5 h) [2, -2, 0, -2, 0, -2, 2, 0, 2] [2, 0, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq8 h) [] [-2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq1585 h) [0] [-2, 0, -2, 0, -2]).trans (in_context (eq1 h) [] [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2264 (h : Relations φ) : value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2] = value φ [0, -2, 0, -2, 0, -2, 2, 0] := by
  have h0 : value φ [0, -2, 0, -2, 0, -2, 2, 0] = value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, 0, -2, 0, -2, 0, -2] :=
    overlap (eq2262 h) (eq5 h) [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] [0] (by decide)
  have hl : value φ [0, -2, 0, -2, 0, -2, 2, 0] = value φ [0, -2, 0, -2, 0, -2, 2, 0] := rfl
  have hr : value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, 0, -2, 0, -2, 0, -2] = value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2] :=
    (in_context (eq1 h) [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2] [-2, 0, -2, 0, -2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2265 (h : Relations φ) : value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0] = value φ [-2, 0, -2, 0, -2, 2, 0, 2, -2] := by
  have h0 : value φ [-2, 0, -2, 0, -2, 2, 0, 2, -2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0] :=
    overlap (eq2259 h) (eq0 h) [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0] [-2] (by decide)
  have hl : value φ [-2, 0, -2, 0, -2, 2, 0, 2, -2] = value φ [-2, 0, -2, 0, -2, 2, 0, 2, -2] := rfl
  have hr : value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2267 (h : Relations φ) : value φ [0, -2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] = value φ [-2, 0, -2, 2, -2, 0, -2, 0, -2] := by
  have h0 : value φ [0, -2, 2, 0, 2, -2, 0, -2, 0, -2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2] = value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, -2, 0, -2, 0, -2, 2, 0, 2] :=
    overlap (eq1760 h) (eq2259 h) [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] [-2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2] (by decide)
  have hl : value φ [0, -2, 2, 0, 2, -2, 0, -2, 0, -2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2] = value φ [-2, 0, -2, 2, -2, 0, -2, 0, -2] :=
    ((in_context (eq0 h) [0, -2, 2, 0, 2, -2, 0, -2, 0] [0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq1 h) [0, -2, 2, 0, 2, -2, 0, -2] [-2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq0 h) [0, -2, 2, 0, 2, -2, 0] [0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq1 h) [0, -2, 2, 0, 2, -2] [-2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq0 h) [0, -2, 2, 0, 2] [2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq2 h) [0, -2, 2, 0] [0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq1 h) [0, -2, 2] [2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq2 h) [0, -2] [-2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq0 h) [0] [0, -2, 0, -2, 2, -2, 0, -2, 0, -2]).trans (in_context (eq1 h) [] [-2, 0, -2, 2, -2, 0, -2, 0, -2]))))))))))
  have hr : value φ [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, -2, 0, -2, 0, -2, 2, 0, 2] = value φ [0, -2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] :=
    ((in_context (eq1790 h) [] [-2, 0, -2, 0, -2, 2, 0, 2]).trans (in_context (eq1585 h) [0, -2] []))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2272 (h : Relations φ) : value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2] = value φ [-2, 0, -2, 0, -2, 2, 0, 2, -2, 0] := by
  have h0 : value φ [-2, 0, -2, 0, -2, 2, 0, 2, -2, 0] = value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2] :=
    overlap (eq2260 h) (eq12 h) [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0] [2, 0, 2, -2, 0] (by decide)
  have hl : value φ [-2, 0, -2, 0, -2, 2, 0, 2, -2, 0] = value φ [-2, 0, -2, 0, -2, 2, 0, 2, -2, 0] := rfl
  have hr : value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2] :=
    ((in_context (eq1 h) [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2] [-2, 2, 0, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq0 h) [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] [2, 0, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq1586 h) [] [0, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq1 h) [0, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] [2, 0, 2, -2, 0, -2]).trans ((in_context (eq2 h) [0, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2] [0, 2, -2, 0, -2]).trans ((in_context (eq5 h) [0, 2, 0, 2, -2, 0, -2, 0, -2, 2] [2, -2, 0, -2]).trans ((in_context (eq6 h) [0] [-2, 0, -2, 0, -2, 2, -2, 0, -2]).trans (in_context (eq1 h) [] [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2]))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2274 (h : Relations φ) : value φ [0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [-2, 0, -2, 2, -2, 0, -2, 0, -2, 2] := by
  have h0 : value φ [-2, 0, -2, 2, -2, 0, -2, 0, -2, 2] = value φ [0, -2, 0, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0] :=
    overlap (eq2267 h) (eq1586 h) [0, -2, 0] [2] (by decide)
  have hl : value φ [-2, 0, -2, 2, -2, 0, -2, 0, -2, 2] = value φ [-2, 0, -2, 2, -2, 0, -2, 0, -2, 2] := rfl
  have hr : value φ [0, -2, 0, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0] :=
    (in_context (eq1 h) [0, -2] [2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2275 (h : Relations φ) : value φ [-2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] = value φ [2, -2, 0, -2, 0, -2, 2, 0] := by
  have h0 : value φ [-2, 0, -2, 0, -2, 2, 0, 2, -2, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] :=
    overlap (eq2265 h) (eq2274 h) [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2] [-2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0] (by decide)
  have hl : value φ [-2, 0, -2, 0, -2, 2, 0, 2, -2, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, 0] :=
    ((in_context (eq0 h) [-2, 0, -2, 0, -2, 2, 0, 2] [2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq2 h) [-2, 0, -2, 0, -2, 2, 0] [0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq1 h) [-2, 0, -2, 0, -2, 2] [2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq2 h) [-2, 0, -2, 0, -2] [-2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq0 h) [-2, 0, -2, 0] [0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq1 h) [-2, 0, -2] [-2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq0 h) [-2, 0] [0, -2, 2, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq1 h) [-2] [-2, 2, -2, 0, -2, 0, -2, 2, 0]).trans (in_context (eq0 h) [] [2, -2, 0, -2, 0, -2, 2, 0])))))))))
  have hr : value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] = value φ [-2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] :=
    (in_context (eq2272 h) [] [-2, 0, -2, 2, -2, 0, -2, 0, -2, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2280 (h : Relations φ) : value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] = value φ [-2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2] := by
  have h0 : value φ [0, -2, 0, -2, 0, -2, 2, 0, 0, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, -2, 0, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0] :=
    overlap (eq2264 h) (eq426 h) [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, -2, 0] [0, 2, 0, 2, 0, 2, -2, 0, -2] (by decide)
  have hl : value φ [0, -2, 0, -2, 0, -2, 2, 0, 0, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [-2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2] :=
    ((in_context (eq1 h) [0, -2, 0, -2, 0, -2, 2] [2, 0, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq2 h) [0, -2, 0, -2, 0, -2] [0, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq5 h) [0] [2, 0, 2, -2, 0, -2]).trans (in_context (eq1 h) [] [-2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2]))))
  have hr : value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, -2, 0, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] :=
    ((in_context (eq1 h) [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, -2] [-2, 0, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq0 h) [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2] [0, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq1586 h) [] [0, 2, 0, 2, -2, 0]).trans ((in_context (eq1 h) [0, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] [2, 0, 2, -2, 0]).trans ((in_context (eq2 h) [0, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2] [0, 2, -2, 0]).trans ((in_context (eq5 h) [0, 2, 0, 2, -2, 0, -2, 0, -2, 2] [2, -2, 0]).trans ((in_context (eq6 h) [0] [-2, 0, -2, 0, -2, 2, -2, 0]).trans (in_context (eq1 h) [] [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0]))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2284 (h : Relations φ) : value φ [0, -2, 0, -2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2] = value φ [-2, 2, 0, -2, 0, -2, 0, -2, 2, -2, 0] := by
  have h0 : value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] = value φ [0, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2] :=
    overlap (eq11 h) (eq2280 h) [0, -2, 0, -2, 2, 0, 2, 0] [-2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] (by decide)
  have hl : value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] = value φ [-2, 2, 0, -2, 0, -2, 0, -2, 2, -2, 0] :=
    ((in_context (eq0 h) [-2, 2, 0, 2, 0, 2, -2, 0] [0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0]).trans ((in_context (eq1 h) [-2, 2, 0, 2, 0, 2, -2] [-2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0]).trans ((in_context (eq0 h) [-2, 2, 0, 2, 0, 2] [2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0]).trans ((in_context (eq2 h) [-2, 2, 0, 2, 0] [0, 2, -2, 0, -2, 0, -2, 2, -2, 0]).trans ((in_context (eq1 h) [-2, 2, 0, 2] [2, -2, 0, -2, 0, -2, 2, -2, 0]).trans (in_context (eq2 h) [-2, 2, 0] [-2, 0, -2, 0, -2, 2, -2, 0]))))))
  have hr : value φ [0, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2] = value φ [0, -2, 0, -2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2] :=
    (in_context (eq427 h) [0, -2, 0, -2] [-2, 0, -2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2285 (h : Relations φ) : value φ [0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2] := by
  have h0 : value φ [-2, 2, 0, -2, 0, -2, 0, -2, 2, -2, 0, 0, -2, 2, 0, 2, 0, 2] = value φ [0, -2, 0, -2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2] :=
    overlap (eq2284 h) (eq9 h) [0, -2, 0, -2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0] [0, -2, 2, 0, 2, 0, 2] (by decide)
  have hl : value φ [-2, 2, 0, -2, 0, -2, 0, -2, 2, -2, 0, 0, -2, 2, 0, 2, 0, 2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2] :=
    ((in_context (eq1 h) [-2, 2, 0, -2, 0, -2, 0, -2, 2, -2] [-2, 2, 0, 2, 0, 2]).trans ((in_context (eq0 h) [-2, 2, 0, -2, 0, -2, 0, -2, 2] [2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [-2, 2, 0, -2, 0, -2, 0, -2] [0, 2, 0, 2]).trans ((in_context (eq5 h) [-2, 2, 0] [2, 0, 2]).trans (in_context (eq1 h) [-2, 2] [-2, 0, -2, 0, -2, 2, 0, 2])))))
  have hr : value φ [0, -2, 0, -2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2] = value φ [0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2] :=
    ((in_context (eq429 h) [0, -2, 0, -2, 0] [2, 0, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq1 h) [0, -2, 0, -2] [2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 2, 0, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq2 h) [0, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 0, -2] [0, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq5 h) [0, -2, 0, -2, 2, 0, 2, 0] [2, -2, 0, -2, 0, -2]).trans (in_context (eq1 h) [0, -2, 0, -2, 2, 0, 2] [-2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2289 (h : Relations φ) : value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] = value φ [-2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0] := by
  have h0 : value φ [-2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0] = value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] :=
    overlap (eq2260 h) (eq10 h) [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0] [2, 0, 2, -2, 0, -2, 0] (by decide)
  have hl : value φ [-2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0] = value φ [-2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0] := rfl
  have hr : value φ [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] :=
    ((in_context (eq1 h) [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2] [-2, 0, -2, 2, 0, 2, 0, 2, -2]).trans ((in_context (eq0 h) [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0] [0, -2, 2, 0, 2, 0, 2, -2]).trans ((in_context (eq1 h) [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2] [-2, 2, 0, 2, 0, 2, -2]).trans ((in_context (eq0 h) [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] [2, 0, 2, 0, 2, -2]).trans ((in_context (eq1586 h) [] [0, 2, 0, 2, -2]).trans ((in_context (eq1 h) [0, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] [2, 0, 2, -2]).trans ((in_context (eq2 h) [0, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2] [0, 2, -2]).trans ((in_context (eq5 h) [0, 2, 0, 2, -2, 0, -2, 0, -2, 2] [2, -2]).trans ((in_context (eq6 h) [0] [-2, 0, -2, 0, -2, 2, -2]).trans (in_context (eq1 h) [] [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2]))))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2290 (h : Relations φ) : value φ [0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0] = value φ [-2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2] := by
  have h0 : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] = value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0] :=
    overlap (eq424 h) (eq2289 h) [0, -2, 0, -2, 0, 2, 0, 2, 0] [0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] (by decide)
  have hl : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] = value φ [-2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2] :=
    ((in_context (eq1 h) [-2, 0, 2, 0, 2, 0, 2, -2] [-2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2]).trans ((in_context (eq0 h) [-2, 0, 2, 0, 2, 0, 2] [2, 0, 2, -2, 0, -2, 0, -2, 2, -2]).trans ((in_context (eq2 h) [-2, 0, 2, 0, 2, 0] [0, 2, -2, 0, -2, 0, -2, 2, -2]).trans ((in_context (eq1 h) [-2, 0, 2, 0, 2] [2, -2, 0, -2, 0, -2, 2, -2]).trans (in_context (eq2 h) [-2, 0, 2, 0] [-2, 0, -2, 0, -2, 2, -2])))))
  have hr : value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0] = value φ [0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0] :=
    ((in_context (eq427 h) [0, -2, 0, -2, 0] [-2, 0, -2, 0]).trans (in_context (eq1 h) [0, -2, 0, -2] [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2313 (h : Relations φ) : value φ [2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] = value φ [-2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0] := by
  have h0 : value φ [2, 0, 2, -2, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] :=
    overlap (eq1636 h) (eq2274 h) [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2] [-2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0] (by decide)
  have hl : value φ [2, 0, 2, -2, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [-2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0] :=
    ((in_context (eq0 h) [2, 0, 2] [2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq2 h) [2, 0] [0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq1 h) [2] [2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0]).trans (in_context (eq2 h) [] [-2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0]))))
  have hr : value φ [-2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] = value φ [2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] :=
    (in_context (eq1652 h) [] [-2, 0, -2, 2, -2, 0, -2, 0, -2, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2335 (h : Relations φ) : value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0] = value φ [0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] := by
  have h0 : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0] = value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, -2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2] :=
    overlap (eq424 h) (eq2290 h) [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2] [0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0] (by decide)
  have hl : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0] :=
    ((in_context (eq1 h) [-2, 0, 2, 0, 2, 0, 2, -2] [-2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0]).trans ((in_context (eq0 h) [-2, 0, 2, 0, 2, 0, 2] [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0]).trans ((in_context (eq2 h) [-2, 0, 2, 0, 2, 0] [0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0]).trans ((in_context (eq1 h) [-2, 0, 2, 0, 2] [-2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0]).trans ((in_context (eq6 h) [-2, 0] [-2, 0, -2, 0]).trans (in_context (eq1 h) [-2] [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0]))))))
  have hr : value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, -2, 0, 2, 0, -2, 0, -2, 0, -2, 2, -2] = value φ [0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] :=
    ((in_context (eq0 h) [0, -2, 0, -2, 0, 2, 0, 2, 0, 2] [0, 2, 0, -2, 0, -2, 0, -2, 2, -2]).trans ((in_context (eq4 h) [0, -2, 0, -2, 0] [2, 0, -2, 0, -2, 0, -2, 2, -2]).trans ((in_context (eq1 h) [0, -2, 0, -2] [2, 0, 2, 0, 2, 2, 0, -2, 0, -2, 0, -2, 2, -2]).trans ((in_context (eq2 h) [0, -2, 0, -2, 2, 0, 2, 0] [0, -2, 0, -2, 0, -2, 2, -2]).trans (in_context (eq1 h) [0, -2, 0, -2, 2, 0, 2] [-2, 0, -2, 0, -2, 2, -2])))))
  exact hl.symm.trans (h0.trans hr)

private theorem eq2337 (h : Relations φ) : value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] := by
  have h0 : value φ [0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0] :=
    overlap (eq2 h) (eq2313 h) [2] [0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] (by decide)
  have hl : value φ [0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] = value φ [0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] := rfl
  have hr : value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2338 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2] = value φ [0, 2] := by
  have h0 : value φ [0, 2] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2] :=
    inclusion (eq1623 h) (eq2254 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2] [2, -2] (by decide)
  have hl : value φ [0, 2] = value φ [0, 2] := rfl
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2] :=
    ((in_context (eq10 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2] [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2]).trans ((in_context (eq0 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2] [0, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2]).trans ((in_context (eq4 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2] [2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2]).trans ((in_context (eq2 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, 0] [0, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2]).trans (in_context (eq1 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2] [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2339 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [2, 0, 2, 0, 2, -2, 0, -2] := by
  have h0 : value φ [0, 2, 0, 2, 0, 2, 0, -2, 0, -2] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0] :=
    overlap (eq2338 h) (eq1520 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2] [0, 2, 0, 2, 0, -2, 0, -2] (by decide)
  have hl : value φ [0, 2, 0, 2, 0, 2, 0, -2, 0, -2] = value φ [2, 0, 2, 0, 2, -2, 0, -2] :=
    ((in_context (eq4 h) [0] [-2, 0, -2]).trans (in_context (eq1 h) [] [2, 0, 2, 0, 2, -2, 0, -2]))
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2] :=
    ((in_context (eq0 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2] [0, 2, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0]).trans ((in_context (eq1398 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2] [-2, 0]).trans ((in_context (eq53 h) [-2, 2, 0, 2, 0, 2, -2, 0] [-2, 2, -2, 2, 0, 2, -2, -2, 0]).trans ((in_context (eq12 h) [-2, 2, 0, 2, 0, 2] [2, 0, -2, 2, -2, -2, 2, -2, 2, 0, 2, -2, -2, 0]).trans ((in_context (eq4 h) [-2] [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 2, -2, -2, 2, -2, 2, 0, 2, -2, -2, 0]).trans ((in_context (eq0 h) [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 2] [2, -2, 2, 0, 2, -2, -2, 0]).trans ((in_context (eq2 h) [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2] [-2, 2, 0, 2, -2, -2, 0]).trans ((in_context (eq0 h) [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0] [2, 0, 2, -2, -2, 0]).trans ((in_context (eq0 h) [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2] [0]).trans ((in_context (eq4 h) [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2] []).trans ((in_context (eq10 h) [-2, 0, 2, 0, 2, 0, 2] [2, 0, 2, 0, 2]).trans ((in_context (eq4 h) [-2, 0] [-2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2]).trans (in_context (eq1 h) [-2] [2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2])))))))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2340 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] = value φ [2, 0, 2, 0, 2] := by
  have h0 : value φ [2, 0, 2, 0, 2, -2, 0, -2, -2, 0, -2] = value φ [-2, 2, 0, 2, 0, 2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] :=
    overlap (eq2339 h) (eq1584 h) [-2, 2, 0, 2, 0, 2] [-2, 0, -2] (by decide)
  have hl : value φ [2, 0, 2, 0, 2, -2, 0, -2, -2, 0, -2] = value φ [2, 0, 2, 0, 2] :=
    ((in_context (eq0 h) [2, 0, 2, 0, 2, -2, 0] [0, -2]).trans ((in_context (eq1 h) [2, 0, 2, 0, 2, -2] [-2]).trans (in_context (eq0 h) [2, 0, 2, 0, 2] [])))
  have hr : value φ [-2, 2, 0, 2, 0, 2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] :=
    (in_context (eq4 h) [-2] [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2341 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2] = value φ [0, 2, 0, 2, 0, 2] := by
  have h0 : value φ [2, 0, 2, 0, 2, -2, 0, -2, -2, 0, -2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] :=
    overlap (eq2339 h) (eq10 h) [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2] [-2, 0, -2, 0] (by decide)
  have hl : value φ [2, 0, 2, 0, 2, -2, 0, -2, -2, 0, -2, 0] = value φ [0, 2, 0, 2, 0, 2] :=
    ((in_context (eq0 h) [2, 0, 2, 0, 2, -2, 0] [0, -2, 0]).trans ((in_context (eq1 h) [2, 0, 2, 0, 2, -2] [-2, 0]).trans ((in_context (eq0 h) [2, 0, 2, 0, 2] [0]).trans (in_context (eq4 h) [] []))))
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2] :=
    ((in_context (eq4 h) [-2, 2, 0, 2, 0, 2, -2, 0, -2] [-2, 0, -2, 2, 0, 2, 0, 2, -2]).trans ((in_context (eq10 h) [] [2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2]).trans (in_context (eq1553 h) [] [2, 0, 2, 0, 2, -2])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2342 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2] = value φ [0, 2, 0, 2, 0, 2, -2] := by
  have h0 : value φ [0, 2, 0, 2, 0, 2, -2] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2] :=
    overlap (eq2341 h) (eq0 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2] [-2] (by decide)
  have hl : value φ [0, 2, 0, 2, 0, 2, -2] = value φ [0, 2, 0, 2, 0, 2, -2] := rfl
  have hr : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2344 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [0, 2, 0, 2, 0, 2, -2, 0] := by
  have h0 : value φ [0, 2, 0, 2, 0, 2, -2, 0] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 0, 2, 0, 2, 0, 2] :=
    overlap (eq2342 h) (eq4 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] [0] (by decide)
  have hl : value φ [0, 2, 0, 2, 0, 2, -2, 0] = value φ [0, 2, 0, 2, 0, 2, -2, 0] := rfl
  have hr : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 0, 2, 0, 2, 0, 2] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2] :=
    (in_context (eq1 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2] [2, 0, 2, 0, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2345 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0] = value φ [2, 0, 2, 0, 2, -2, 0, -2, 2] := by
  have h0 : value φ [2, 0, 2, 0, 2, -2, 0, -2, 2] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0] :=
    overlap (eq2339 h) (eq2 h) [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0] [2] (by decide)
  have hl : value φ [2, 0, 2, 0, 2, -2, 0, -2, 2] = value φ [2, 0, 2, 0, 2, -2, 0, -2, 2] := rfl
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2347 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2] = value φ [0, 2, 0, 2, 0, 2, -2, 2, 0] := by
  have h0 : value φ [2, 0, 2, 0, 2, -2, 0, -2, -2, 0, -2, 0, -2, 2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2] :=
    overlap (eq2339 h) (eq6 h) [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0] [-2, 0, -2, 0, -2, 2, 0] (by decide)
  have hl : value φ [2, 0, 2, 0, 2, -2, 0, -2, -2, 0, -2, 0, -2, 2, 0] = value φ [0, 2, 0, 2, 0, 2, -2, 2, 0] :=
    ((in_context (eq0 h) [2, 0, 2, 0, 2, -2, 0] [0, -2, 0, -2, 2, 0]).trans ((in_context (eq1 h) [2, 0, 2, 0, 2, -2] [-2, 0, -2, 2, 0]).trans ((in_context (eq0 h) [2, 0, 2, 0, 2] [0, -2, 2, 0]).trans (in_context (eq4 h) [] [-2, 2, 0]))))
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2] :=
    ((in_context (eq1 h) [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2] [2, -2, 0, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq2 h) [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2] [-2, 0, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq0 h) [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2] [0, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq4 h) [-2, 2, 0, 2, 0, 2, -2, 0, -2] [-2, 0, -2, 2, 0, 2]).trans ((in_context (eq10 h) [] [2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2]).trans (in_context (eq1553 h) [] [2, 0, 2]))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2350 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2] = value φ [0, 2, 0, 2, 0, 2, -2, 0, 2, 0] := by
  have h0 : value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 0, -2, 0, -2, 2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2] :=
    overlap (eq2339 h) (eq428 h) [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0] [0, -2, 0, -2, 0, -2, 2, 0] (by decide)
  have hl : value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 0, -2, 0, -2, 2, 0] = value φ [0, 2, 0, 2, 0, 2, -2, 0, 2, 0] :=
    ((in_context (eq5 h) [2, 0, 2, 0, 2] [-2, 0, -2, 2, 0]).trans ((in_context (eq4 h) [] [-2, 0, -2, 0, -2, -2, 0, -2, 2, 0]).trans ((in_context (eq0 h) [0, 2, 0, 2, 0, 2, -2, 0, -2, 0] [0, -2, 2, 0]).trans ((in_context (eq1 h) [0, 2, 0, 2, 0, 2, -2, 0, -2] [-2, 2, 0]).trans (in_context (eq0 h) [0, 2, 0, 2, 0, 2, -2, 0] [2, 0])))))
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 0, 2, 0, -2, 0, -2, 0, -2, 2, 0, 2] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2] :=
    ((in_context (eq1 h) [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2] [2, 0, -2, 0, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq2 h) [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2] [0, -2, 0, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq12 h) [-2, 2, 0, 2, 0, 2] [-2, 0, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq4 h) [-2] [-2, 2, 0, 2, 0, 2, -2, 0, -2, -2, 0, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq0 h) [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0] [0, -2, 0, -2, 2, 0, 2]).trans ((in_context (eq1 h) [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2] [-2, 0, -2, 2, 0, 2]).trans ((in_context (eq0 h) [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2] [0, -2, 2, 0, 2]).trans (in_context (eq4 h) [-2, 0, 2, 0, 2, 0, 2, -2] [-2, 2, 0, 2]))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2367 (h : Relations φ) : value φ [0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2] := by
  have h0 : value φ [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0] :=
    overlap (eq2341 h) (eq2350 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2] [0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2] (by decide)
  have hl : value φ [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2] :=
    ((in_context (eq4 h) [0] [2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2]).trans ((in_context (eq1 h) [] [2, 0, 2, 0, 2, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2]).trans ((in_context (eq2 h) [2, 0, 2, 0] [0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2]).trans ((in_context (eq1 h) [2, 0, 2] [2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2]).trans ((in_context (eq2 h) [2, 0] [0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2]).trans ((in_context (eq1 h) [2] [2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2]).trans (in_context (eq2 h) [] [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2])))))))
  have hr : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0] = value φ [0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0] :=
    (in_context (eq2342 h) [] [0, 2, 0, 2, 0, 2, -2, 0, 2, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2370 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2] = value φ [2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0] := by
  have h0 : value φ [2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] :=
    overlap (eq2340 h) (eq8 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0] [-2, 0, -2, 2, 0, 2, 0] (by decide)
  have hl : value φ [2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0] = value φ [2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0] := rfl
  have hr : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2] :=
    ((in_context (eq1 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2] [2, 0, 2, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq2 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0] [0, 2, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq1 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2] [2, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq2 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] [-2, 0, -2, 0, -2, 2]).trans ((in_context (eq1583 h) [] [0, -2, 0, -2, 2]).trans ((in_context (eq1 h) [0, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2] [-2, 0, -2, 2]).trans ((in_context (eq0 h) [0, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2] [0, -2, 2]).trans ((in_context (eq4 h) [0, -2, 0, -2, 2, 0, 2, 0, 2, -2] [-2, 2]).trans (in_context (eq11 h) [] [2, 0, 2, 0, 2, -2, 2])))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2388 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2] = value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2] := by
  have h0 : value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, 0, 2, 0, 2, 0, 2, -2, 0] :=
    overlap (eq425 h) (eq2344 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0] [0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2] (by decide)
  have hl : value φ [0, -2, 0, -2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2] :=
    ((in_context (eq4 h) [0, -2, 0, -2, 0] [2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq1 h) [0, -2, 0, -2] [2, 0, 2, 0, 2, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [0, -2, 0, -2, 2, 0, 2, 0] [0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq1 h) [0, -2, 0, -2, 2, 0, 2] [2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [0, -2, 0, -2, 2, 0] [0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq1 h) [0, -2, 0, -2, 2] [2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [0, -2, 0, -2] [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq0 h) [0, -2, 0] [0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2]).trans (in_context (eq1 h) [0, -2] [2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2])))))))))
  have hr : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, 0, 2, 0, 2, 0, 2, -2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2] :=
    ((in_context (eq430 h) [] [0, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq431 h) [0] [2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq1 h) [] [-2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq12 h) [-2, 0, 2, 0, 2, 0, 2] []).trans ((in_context (eq4 h) [-2, 0] [-2, 2, 0, 2, 0, 2, -2, 0, -2]).trans (in_context (eq1 h) [-2] [2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2]))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2400 (h : Relations φ) : value φ [2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2] := by
  have h0 : value φ [0, -2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] = value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2] :=
    overlap (eq420 h) (eq2340 h) [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0] [0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] (by decide)
  have hl : value φ [0, -2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] = value φ [2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] :=
    ((in_context (eq4 h) [0, -2, 0] [2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq1 h) [0, -2] [2, 0, 2, 0, 2, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq2 h) [0, -2, 2, 0, 2, 0] [0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq1 h) [0, -2, 2, 0, 2] [2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq2 h) [0, -2, 2, 0] [0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq1 h) [0, -2, 2] [2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq2 h) [0, -2] [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq0 h) [0] [0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0]).trans (in_context (eq1 h) [] [2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0])))))))))
  have hr : value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2] :=
    (in_context (eq423 h) [] [2, 0, 2, 0, 2])
  exact hl.symm.trans (h0.trans hr)

private theorem eq2402 (h : Relations φ) : value φ [2, 0, 2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2] = value φ [0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0] := by
  have h0 : value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, 2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0] = value φ [2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2] :=
    overlap (eq6 h) (eq2345 h) [2, 0, 2, -2, 0, -2, 0] [2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0] (by decide)
  have hl : value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, 2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0] = value φ [0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0] :=
    ((in_context (eq2 h) [0, 2, -2, 0, -2, 0, -2, 2, 0] [0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0]).trans ((in_context (eq1 h) [0, 2, -2, 0, -2, 0, -2, 2] [2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0]).trans ((in_context (eq2 h) [0, 2, -2, 0, -2, 0, -2] [-2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0]).trans ((in_context (eq0 h) [0, 2, -2, 0, -2, 0] [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0]).trans ((in_context (eq1 h) [0, 2, -2, 0, -2] [-2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0]).trans (in_context (eq0 h) [0, 2, -2, 0] [2, 0, 2, 0, 2, -2, 2, 0, 2, 0]))))))
  have hr : value φ [2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2] = value φ [2, 0, 2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2] :=
    (in_context (eq426 h) [2, 0, 2] [2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2412 (h : Relations φ) : value φ [2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0] := by
  have h0 : value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, -2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2] = value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0] :=
    overlap (eq9 h) (eq2370 h) [-2, 0, -2, 0] [-2, 0, -2, 2, 0, 2, 0, 2, -2, 2] (by decide)
  have hl : value φ [2, 0, 2, 0, 2, -2, 0, -2, 0, -2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2] = value φ [2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2] :=
    ((in_context (eq0 h) [2, 0, 2, 0, 2, -2, 0, -2, 0] [0, -2, 2, 0, 2, 0, 2, -2, 2]).trans ((in_context (eq1 h) [2, 0, 2, 0, 2, -2, 0, -2] [-2, 2, 0, 2, 0, 2, -2, 2]).trans (in_context (eq0 h) [2, 0, 2, 0, 2, -2, 0] [2, 0, 2, 0, 2, -2, 2])))
  have hr : value φ [-2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0] = value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0] :=
    (in_context (eq426 h) [] [2, 0, 2, 0])
  exact hl.symm.trans (h0.trans hr)

private theorem eq2415 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0] = value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2] := by
  have h0 : value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2] = value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0] :=
    overlap (eq2388 h) (eq0 h) [-2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0] [-2] (by decide)
  have hl : value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2] = value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2] := rfl
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2421 (h : Relations φ) : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [0, -2, 2] := by
  have h0 : value φ [0, -2, 2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2] :=
    overlap (eq2258 h) (eq2 h) [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2] [2] (by decide)
  have hl : value φ [0, -2, 2] = value φ [0, -2, 2] := rfl
  have hr : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2443 (h : Relations φ) : value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0] = value φ [-2, 0, 2, 0, -2, 0, -2] := by
  have h0 : value φ [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2] = value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] :=
    overlap (eq2066 h) (eq2249 h) [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0] [0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2] (by decide)
  have hl : value φ [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2] = value φ [-2, 0, 2, 0, -2, 0, -2] :=
    ((in_context (eq1 h) [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2] [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq0 h) [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0] [0, 2, 0, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq1 h) [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2] [2, 0, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [-2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2] [0, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq10 h) [-2, 0, 2] [-2, 2, 0, 2, 0, 2]).trans ((in_context (eq0 h) [-2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2] [2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [-2, 0, 2, 0, -2, 0, -2, 2, 0, 2, 0] [0, 2, 0, 2]).trans ((in_context (eq1 h) [-2, 0, 2, 0, -2, 0, -2, 2, 0, 2] [2, 0, 2]).trans ((in_context (eq2 h) [-2, 0, 2, 0, -2, 0, -2, 2, 0] [0, 2]).trans ((in_context (eq1 h) [-2, 0, 2, 0, -2, 0, -2, 2] [2]).trans (in_context (eq2 h) [-2, 0, 2, 0, -2, 0, -2] [])))))))))))
  have hr : value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] = value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0] :=
    ((in_context (eq1 h) [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, -2, 0, -2, 2] [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0]).trans ((in_context (eq2 h) [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, -2, 0, -2] [0, -2, 0, 2, 0, -2, 2, 0, 2, 0]).trans ((in_context (eq5 h) [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0] [2, 0, -2, 2, 0, 2, 0]).trans (in_context (eq1 h) [2, 0, 2, 0, 2, -2, 0, 2, -2, 2] [-2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0]))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2457 (h : Relations φ) : value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2] = value φ [-2, 0, 2, 0, -2, 0, -2, 0] := by
  have h0 : value φ [-2, 0, 2, 0, -2, 0, -2, 0] = value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2] :=
    overlap (eq2443 h) (eq1 h) [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2] [0] (by decide)
  have hl : value φ [-2, 0, 2, 0, -2, 0, -2, 0] = value φ [-2, 0, 2, 0, -2, 0, -2, 0] := rfl
  have hr : value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2] = value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2466 (h : Relations φ) : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2] = value φ [0, -2, 2, -2, 2, 0, 2, 0, 2] := by
  have h0 : value φ [0, -2, 2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2] :=
    overlap (eq2421 h) (eq2340 h) [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2] [0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] (by decide)
  have hl : value φ [0, -2, 2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0] = value φ [0, -2, 2, -2, 2, 0, 2, 0, 2] :=
    ((in_context (eq4 h) [0, -2] [2, -2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq2 h) [0, -2, 0, 2, 0, 2, 0] [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq2402 h) [0, -2, 0] [0, 2, 0, 2, -2, 0]).trans ((in_context (eq1 h) [0, -2] [2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq1 h) [0, -2, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2] [2, 0, 2, -2, 0]).trans ((in_context (eq2 h) [0, -2, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0] [0, 2, -2, 0]).trans ((in_context (eq1 h) [0, -2, 2, -2, 0, 2, 0, 2, 0, 2, -2, 2] [2, -2, 0]).trans ((in_context (eq2 h) [0, -2, 2, -2, 0, 2, 0, 2, 0, 2, -2] [-2, 0]).trans ((in_context (eq0 h) [0, -2, 2, -2, 0, 2, 0, 2, 0, 2] [0]).trans ((in_context (eq4 h) [0, -2, 2, -2, 0] []).trans (in_context (eq1 h) [0, -2, 2, -2] [2, 0, 2, 0, 2])))))))))))
  have hr : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2] :=
    ((in_context (eq2 h) [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0] [0, 2, 0, 2]).trans ((in_context (eq1 h) [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2] [2, 0, 2]).trans ((in_context (eq2 h) [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 2, 0] [0, 2]).trans ((in_context (eq1 h) [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 2] [2]).trans (in_context (eq2 h) [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2] [])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2472 (h : Relations φ) : value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0] = value φ [-2, 0, 2, 0, -2, 0, -2, 0, 2] := by
  have h0 : value φ [-2, 0, 2, 0, -2, 0, -2, 0, 2] = value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0] :=
    overlap (eq2457 h) (eq2 h) [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0] [2] (by decide)
  have hl : value φ [-2, 0, 2, 0, -2, 0, -2, 0, 2] = value φ [-2, 0, 2, 0, -2, 0, -2, 0, 2] := rfl
  have hr : value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0] = value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2473 (h : Relations φ) : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [2, 0, 2, 0, -2, 0, -2, 0, 2, 0] := by
  have h0 : value φ [0, 2, 0, -2, 0, 2, 0, -2, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0] = value φ [-2, 0, 2, 0, -2, 0, 2, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2] :=
    overlap (eq2243 h) (eq2037 h) [-2, 0, 2, 0, -2, 0, 2] [-2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0] (by decide)
  have hl : value φ [0, 2, 0, -2, 0, 2, 0, -2, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0] = value φ [2, 0, 2, 0, -2, 0, -2, 0, 2, 0] :=
    ((in_context (eq0 h) [0, 2, 0, -2, 0, 2, 0] [0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0]).trans ((in_context (eq1 h) [0, 2, 0, -2, 0, 2] [2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0]).trans ((in_context (eq2 h) [0, 2, 0, -2, 0] [-2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0]).trans ((in_context (eq429 h) [0] [2, -2, 2, 0]).trans ((in_context (eq1 h) [] [2, 0, 2, 0, -2, 0, -2, 0, -2, 2, 2, -2, 2, 0]).trans ((in_context (eq2 h) [2, 0, 2, 0, -2, 0, -2, 0, -2] [-2, 2, 0]).trans (in_context (eq0 h) [2, 0, 2, 0, -2, 0, -2, 0] [2, 0])))))))
  have hr : value φ [-2, 0, 2, 0, -2, 0, 2, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2] :=
    ((in_context (eq2 h) [-2, 0, 2, 0, -2, 0] [-2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2]).trans ((in_context (eq5 h) [-2, 0, 2, 0] [2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2]).trans (in_context (eq1 h) [-2, 0, 2] [-2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2475 (h : Relations φ) : value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0] = value φ [-2, 0, 2, 0, 2, 0, -2, 0, -2, 2] := by
  have h0 : value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, 0, 2, 0, -2, 0, 2, 0, -2, 0, 2] = value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, 0, 2, 0, -2, 0, 2, 0, -2, 0] :=
    overlap (eq1931 h) (eq2244 h) [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0] [0, 2, 0, -2, 0, 2, 0, -2, 0, 2] (by decide)
  have hl : value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, 0, 2, 0, -2, 0, 2, 0, -2, 0, 2] = value φ [-2, 0, 2, 0, 2, 0, -2, 0, -2, 2] :=
    ((in_context (eq1 h) [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2] [2, 0, -2, 0, 2, 0, -2, 0, 2]).trans ((in_context (eq2 h) [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0] [0, -2, 0, 2, 0, -2, 0, 2]).trans ((in_context (eq1 h) [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2] [-2, 0, 2, 0, -2, 0, 2]).trans ((in_context (eq0 h) [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2] [0, 2, 0, -2, 0, 2]).trans ((in_context (eq8 h) [-2] [2, 0, -2, 0, 2]).trans ((in_context (eq2 h) [-2, 0, 2, 0, 2, -2, 0, -2, 0, -2] [0, -2, 0, 2]).trans ((in_context (eq5 h) [-2, 0, 2, 0, 2] [-2, 0, 2]).trans ((in_context (eq0 h) [-2, 0, 2, 0, 2, 0, -2, 0, -2, 0] [0, 2]).trans (in_context (eq1 h) [-2, 0, 2, 0, 2, 0, -2, 0, -2] [2])))))))))
  have hr : value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, 0, 2, 0, -2, 0, 2, 0, -2, 0] = value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0] :=
    ((in_context (eq2026 h) [] [0, 2, 0, -2, 0, 2, 0, -2, 0]).trans ((in_context (eq2048 h) [] [0, 2, 0, -2, 0]).trans ((in_context (eq4 h) [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0] [-2, 0]).trans (in_context (eq1 h) [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2] [2, 0, 2, 0, 2, -2, 0]))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2476 (h : Relations φ) : value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2] = value φ [2, 0, 2, 0, 2, -2, 0] := by
  have h0 : value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0] = value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2] :=
    overlap (eq1788 h) (eq2475 h) [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0] (by decide)
  have hl : value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0] = value φ [2, 0, 2, 0, 2, -2, 0] :=
    ((in_context (eq2 h) [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2] [-2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq0 h) [-2, 2, -2, 0, 2, -2, 0, -2, 0] [0, -2, 0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq1 h) [-2, 2, -2, 0, 2, -2, 0, -2] [-2, 0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq0 h) [-2, 2, -2, 0, 2, -2, 0] [0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq1 h) [-2, 2, -2, 0, 2, -2] [-2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq0 h) [-2, 2, -2, 0, 2] [2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq2 h) [-2, 2, -2, 0] [0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq1 h) [-2, 2, -2] [-2, 2, -2, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq0 h) [-2, 2] [2, -2, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq2 h) [-2] [-2, 2, 0, 2, 0, 2, -2, 0]).trans (in_context (eq0 h) [] [2, 0, 2, 0, 2, -2, 0])))))))))))
  have hr : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2] = value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2] :=
    ((in_context (eq2028 h) [0] [-2, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2]).trans ((in_context (eq1 h) [] [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, -2, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2]).trans (in_context (eq0 h) [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] [-2, 0, 2, 0, 2, 0, -2, 0, -2, 2])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2477 (h : Relations φ) : value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2] = value φ [2, 0, 2, 0, 2, -2, 0, 2] := by
  have h0 : value φ [2, 0, 2, 0, 2, -2, 0, 2] = value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2] :=
    overlap (eq2476 h) (eq2 h) [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2] [2] (by decide)
  have hl : value φ [2, 0, 2, 0, 2, -2, 0, 2] = value φ [2, 0, 2, 0, 2, -2, 0, 2] := rfl
  have hr : value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2] = value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2478 (h : Relations φ) : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2] = value φ [2, -2, 2, 0, 2, 0, 2, -2, 0] := by
  have h0 : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0] = value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2] :=
    overlap (eq1728 h) (eq2475 h) [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0] (by decide)
  have hl : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0] = value φ [2, -2, 2, 0, 2, 0, 2, -2, 0] :=
    ((in_context (eq2 h) [-2, 0, 2, -2, 0, -2, 0, -2] [-2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq0 h) [-2, 0, 2, -2, 0, -2, 0] [0, -2, 0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq1 h) [-2, 0, 2, -2, 0, -2] [-2, 0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq0 h) [-2, 0, 2, -2, 0] [0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq1 h) [-2, 0, 2, -2] [-2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq0 h) [-2, 0, 2] [2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq2 h) [-2, 0] [0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0]).trans ((in_context (eq1 h) [-2] [-2, 2, -2, 2, 0, 2, 0, 2, -2, 0]).trans (in_context (eq0 h) [] [2, -2, 2, 0, 2, 0, 2, -2, 0])))))))))
  have hr : value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2] :=
    ((in_context (eq1789 h) [2] [-2, 0, 2, 0, 2, 0, -2, 0, -2, 2]).trans (in_context (eq2 h) [] [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2481 (h : Relations φ) : value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [-2, 0, -2, 0, 2, 0, 2, 0, -2, 0] := by
  have h0 : value φ [0, -2, 0, 2, 0, -2, 0, 2, 0, -2, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] = value φ [2, 0, -2, 0, 2, 0, -2, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] :=
    overlap (eq2247 h) (eq2044 h) [2, 0, -2, 0, 2, 0, -2] [-2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] (by decide)
  have hl : value φ [0, -2, 0, 2, 0, -2, 0, 2, 0, -2, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] = value φ [-2, 0, -2, 0, 2, 0, 2, 0, -2, 0] :=
    ((in_context (eq0 h) [0, -2, 0, 2, 0, -2, 0, 2, 0] [0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0]).trans ((in_context (eq1 h) [0, -2, 0, 2, 0, -2, 0, 2] [2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0]).trans ((in_context (eq2 h) [0, -2, 0, 2, 0, -2, 0] [0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0]).trans ((in_context (eq1 h) [0, -2, 0, 2, 0, -2] [-2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0]).trans ((in_context (eq0 h) [0, -2, 0, 2, 0] [2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0]).trans ((in_context (eq425 h) [0] [2, -2, 0]).trans ((in_context (eq1 h) [] [-2, 0, -2, 0, 2, 0, 2, 0, 2, 2, -2, 0]).trans (in_context (eq2 h) [-2, 0, -2, 0, 2, 0, 2, 0] [-2, 0]))))))))
  have hr : value φ [2, 0, -2, 0, 2, 0, -2, -2, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] :=
    ((in_context (eq0 h) [2, 0, -2, 0, 2, 0] [2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq4 h) [2, 0, -2, 0] [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2]).trans (in_context (eq1 h) [2, 0, -2] [2, 0, 2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2487 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 2] = value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, 0] := by
  have h0 : value φ [0, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] = value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 2] :=
    overlap (eq2347 h) (eq2189 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2] [-2, 0, -2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] (by decide)
  have hl : value φ [0, 2, 0, 2, 0, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] = value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, 0] :=
    ((in_context (eq41 h) [0] [-2, 2, 0, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq0 h) [0, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] [2, 0, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq2 h) [0, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2] [0, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq5 h) [0, -2, 0, 2, 0, -2, 2] [-2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq0 h) [0, -2, 0, 2, 0, -2, 2, 0, -2, 0, -2, 0] [0, -2, 0, -2, 2, 0]).trans ((in_context (eq1 h) [0, -2, 0, 2, 0, -2, 2, 0, -2, 0, -2] [-2, 0, -2, 2, 0]).trans ((in_context (eq0 h) [0, -2, 0, 2, 0, -2, 2, 0, -2, 0] [0, -2, 2, 0]).trans ((in_context (eq1 h) [0, -2, 0, 2, 0, -2, 2, 0, -2] [-2, 2, 0]).trans (in_context (eq0 h) [0, -2, 0, 2, 0, -2, 2, 0] [2, 0])))))))))
  have hr : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 2] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 2] :=
    ((in_context (eq4 h) [-2, 0, 2, 0, 2, 0, 2, -2, 0] [-2, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 2]).trans ((in_context (eq1 h) [-2, 0, 2, 0, 2, 0, 2, -2] [2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 2]).trans (in_context (eq675 h) [-2, 0, 2, 0, 2] [-2, 2])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2494 (h : Relations φ) : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0] = value φ [0, -2, 2, -2, 2, 0, 2, 0, 2, -2] := by
  have h0 : value φ [0, -2, 2, -2, 2, 0, 2, 0, 2, -2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0] :=
    overlap (eq2466 h) (eq0 h) [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0] [-2] (by decide)
  have hl : value φ [0, -2, 2, -2, 2, 0, 2, 0, 2, -2] = value φ [0, -2, 2, -2, 2, 0, 2, 0, 2, -2] := rfl
  have hr : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2498 (h : Relations φ) : value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2] = value φ [-2, 0, 2, 0, -2, 0, -2, 0, 2, 0] := by
  have h0 : value φ [-2, 0, 2, 0, -2, 0, -2, 0, 2, 0] = value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2] :=
    overlap (eq2472 h) (eq1 h) [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2] [0] (by decide)
  have hl : value φ [-2, 0, 2, 0, -2, 0, -2, 0, 2, 0] = value φ [-2, 0, 2, 0, -2, 0, -2, 0, 2, 0] := rfl
  have hr : value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2] = value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2502 (h : Relations φ) : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2] = value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 2] := by
  have h0 : value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2] :=
    overlap (eq2478 h) (eq2 h) [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2] [2] (by decide)
  have hl : value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 2] = value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 2] := rfl
  have hr : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2505 (h : Relations φ) : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2] = value φ [0, 2, 0, 2, 0, -2, 0, -2, 2, 0] := by
  have h0 : value φ [-2, 0, 2, -2, 0, -2, 0, -2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0] = value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2] :=
    overlap (eq1705 h) (eq2494 h) [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0] [-2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0] (by decide)
  have hl : value φ [-2, 0, 2, -2, 0, -2, 0, -2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0] = value φ [0, 2, 0, 2, 0, -2, 0, -2, 2, 0] :=
    ((in_context (eq0 h) [-2, 0, 2, -2, 0, -2, 0] [0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq1 h) [-2, 0, 2, -2, 0, -2] [-2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq0 h) [-2, 0, 2, -2, 0] [0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq1 h) [-2, 0, 2, -2] [-2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq0 h) [-2, 0, 2] [2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq2 h) [-2, 0] [0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq1 h) [-2] [-2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0]).trans (in_context (eq0 h) [] [0, 2, 0, 2, 0, -2, 0, -2, 2, 0]))))))))
  have hr : value φ [2, -2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2] :=
    (in_context (eq1728 h) [] [0, -2, 2, -2, 2, 0, 2, 0, 2, -2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2506 (h : Relations φ) : value φ [-2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2] := by
  have h0 : value φ [-2, 2, 0, -2, 2, 0, 2, 0, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2] = value φ [2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0] :=
    overlap (eq1692 h) (eq2498 h) [2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2] [0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2] (by decide)
  have hl : value φ [-2, 2, 0, -2, 2, 0, 2, 0, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2] :=
    ((in_context (eq1 h) [-2, 2, 0, -2, 2, 0, 2] [2, 0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2]).trans ((in_context (eq2 h) [-2, 2, 0, -2, 2, 0] [0, 2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2]).trans ((in_context (eq1 h) [-2, 2, 0, -2, 2] [2, -2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2]).trans ((in_context (eq2 h) [-2, 2, 0, -2] [-2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2]).trans ((in_context (eq0 h) [-2, 2, 0] [0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2]).trans ((in_context (eq1 h) [-2, 2] [2, -2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2]).trans ((in_context (eq2 h) [-2] [-2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2]).trans (in_context (eq0 h) [] [2, -2, 0, -2, 0, -2, 2, 0, -2, 2]))))))))
  have hr : value φ [2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, -2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0] = value φ [-2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0] :=
    (in_context (eq1725 h) [] [-2, 0, 2, 0, -2, 0, -2, 0, 2, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2510 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [0, 2, -2, 0, -2, 0, 2, 0, 2, 0, -2] := by
  have h0 : value φ [0, 2, 0, -2, 0, 2, 0, -2, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] = value φ [-2, 0, 2, 0, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] :=
    overlap (eq2243 h) (eq2042 h) [-2, 0, 2, 0] [-2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] (by decide)
  have hl : value φ [0, 2, 0, -2, 0, 2, 0, -2, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] = value φ [0, 2, -2, 0, -2, 0, 2, 0, 2, 0, -2] :=
    ((in_context (eq0 h) [0, 2, 0, -2, 0, 2, 0] [2, 0, 2, -2, 0, -2, 0, -2, 2, -2]).trans ((in_context (eq425 h) [0, 2, 0] [2, -2]).trans ((in_context (eq1 h) [0, 2] [-2, 0, -2, 0, 2, 0, 2, 0, 2, 2, -2]).trans (in_context (eq2 h) [0, 2, -2, 0, -2, 0, 2, 0, 2, 0] [-2]))))
  have hr : value φ [-2, 0, 2, 0, 2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] :=
    ((in_context (eq4 h) [-2, 0] [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0]).trans (in_context (eq1 h) [-2] [2, 0, 2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2511 (h : Relations φ) : value φ [0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, -2] = value φ [2, -2, 0, -2, 0, -2, 2, 0] := by
  have h0 : value φ [0, -2, 2, -2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, -2] :=
    overlap (eq2466 h) (eq2510 h) [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0] [2, 0, 2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] (by decide)
  have hl : value φ [0, -2, 2, -2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, 0] :=
    ((in_context (eq2 h) [0, -2, 2, -2, 2, 0, 2, 0] [0, 2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq1 h) [0, -2, 2, -2, 2, 0, 2] [2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq2 h) [0, -2, 2, -2, 2, 0] [0, 2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq1 h) [0, -2, 2, -2, 2] [2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq2 h) [0, -2, 2, -2] [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq0 h) [0, -2, 2] [2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq2 h) [0, -2] [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq0 h) [0] [0, 2, -2, 0, -2, 0, -2, 2, 0]).trans (in_context (eq1 h) [] [2, -2, 0, -2, 0, -2, 2, 0])))))))))
  have hr : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, -2] = value φ [0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, -2] :=
    (in_context (eq2494 h) [] [0, 2, -2, 0, -2, 0, 2, 0, 2, 0, -2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2512 (h : Relations φ) : value φ [0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2] := by
  have h0 : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2] = value φ [0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0] :=
    overlap (eq2511 h) (eq0 h) [0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0] [-2] (by decide)
  have hl : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2] := rfl
  have hr : value φ [0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0] = value φ [0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2526 (h : Relations φ) : value φ [0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] := by
  have h0 : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] :=
    inclusion (eq1763 h) (eq2252 h) [2, -2, 0, -2, 0, -2, 2, 0, 2] [-2, 2] (by decide)
  have hl : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] := rfl
  have hr : value φ [2, -2, 0, -2, 0, -2, 2, 0, 2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] = value φ [0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2] :=
    ((in_context (eq8 h) [] [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2]).trans ((in_context (eq2 h) [0, 2, 0, 2, -2, 0, -2, 0, -2] [0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2]).trans ((in_context (eq5 h) [0, 2, 0, 2] [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2]).trans ((in_context (eq0 h) [0, 2, 0, 2, 0, -2, 0, -2, 0] [0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2]).trans (in_context (eq1 h) [0, 2, 0, 2, 0, -2, 0, -2] [2, 0, -2, 2, 0, 2, 0, 2, -2, 2])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2532 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2] = value φ [0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0] := by
  have h0 : value φ [0, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 2, -2, 0, -2, 0, -2, 2, 0] :=
    overlap (eq2338 h) (eq2275 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] [0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] (by decide)
  have hl : value φ [0, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] = value φ [0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0] :=
    ((in_context (eq2285 h) [0, 2] [2]).trans (in_context (eq2 h) [0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0] []))
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2] :=
    ((in_context (eq2 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2] [-2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq0 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] [0, -2, 0, -2, 2, 0]).trans ((in_context (eq1 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2] [-2, 0, -2, 2, 0]).trans ((in_context (eq0 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0] [0, -2, 2, 0]).trans ((in_context (eq1 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2, 0, 2, -2] [-2, 2, 0]).trans ((in_context (eq0 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2, 0, 2] [2, 0]).trans ((in_context (eq2 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2, 0] [0]).trans (in_context (eq1 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2] []))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2535 (h : Relations φ) : value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 2] = value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] := by
  have h0 : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 2, -2, 0, -2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] = value φ [0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 2] :=
    overlap (eq2367 h) (eq2189 h) [0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2] [2, -2, 0, -2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] (by decide)
  have hl : value φ [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 2, -2, 0, -2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0] = value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] :=
    ((in_context (eq2 h) [-2, 0, 2, 0, 2, 0, 2, -2, 2, 0] [-2, 0, -2, 2, 0, 2, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq41 h) [-2, 0] [-2, 2, 0, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq0 h) [-2, 0, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2] [2, 0, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq2 h) [-2, 0, -2, 0, 2, 0, -2, 2, -2, 0, -2, 0, -2] [0, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq5 h) [-2, 0, -2, 0, 2, 0, -2, 2] [-2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq0 h) [-2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, -2, 0] [0, -2, 0, -2, 2, 0]).trans ((in_context (eq1 h) [-2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0, -2] [-2, 0, -2, 2, 0]).trans ((in_context (eq0 h) [-2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 0] [0, -2, 2, 0]).trans ((in_context (eq1 h) [-2, 0, -2, 0, 2, 0, -2, 2, 0, -2] [-2, 2, 0]).trans (in_context (eq0 h) [-2, 0, -2, 0, 2, 0, -2, 2, 0] [2, 0]))))))))))
  have hr : value φ [0, 2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, 0, -2, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 2] = value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 2] :=
    ((in_context (eq4 h) [0, 2, 0, 2, 0, 2, -2, 0] [-2, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 2]).trans ((in_context (eq1 h) [0, 2, 0, 2, 0, 2, -2] [2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 2]).trans (in_context (eq675 h) [0, 2, 0, 2] [-2, 2])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2542 (h : Relations φ) : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2] = value φ [2, 0, 2, 0, -2, 0, -2, 0, 2, 0, -2] := by
  have h0 : value φ [2, 0, 2, 0, -2, 0, -2, 0, 2, 0, -2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2] :=
    overlap (eq2473 h) (eq0 h) [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2] [-2] (by decide)
  have hl : value φ [2, 0, 2, 0, -2, 0, -2, 0, 2, 0, -2] = value φ [2, 0, 2, 0, -2, 0, -2, 0, 2, 0, -2] := rfl
  have hr : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2543 (h : Relations φ) : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 0, 2, 0, -2] = value φ [-2, 2, 0, -2, 2, 0, 2, 0, 2] := by
  have h0 : value φ [2, -2, 0, -2, 0, -2, 2, 0, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2] = value φ [0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, 0, 2, 0, -2, 0, -2, 0, 2, 0, -2] :=
    overlap (eq2511 h) (eq2542 h) [0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0] [0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2] (by decide)
  have hl : value φ [2, -2, 0, -2, 0, -2, 2, 0, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2] = value φ [-2, 2, 0, -2, 2, 0, 2, 0, 2] :=
    ((in_context (eq1 h) [2, -2, 0, -2, 0, -2, 2] [2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [2, -2, 0, -2, 0, -2] [-2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq0 h) [2, -2, 0, -2, 0] [0, -2, 0, -2, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq1 h) [2, -2, 0, -2] [-2, 0, -2, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq0 h) [2, -2, 0] [0, -2, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq1 h) [2, -2] [-2, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq0 h) [2] [2, -2, 2, 0, -2, 2, 0, 2, 0, 2]).trans (in_context (eq2 h) [] [-2, 2, 0, -2, 2, 0, 2, 0, 2]))))))))
  have hr : value φ [0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, 2, 0, 2, 0, -2, 0, -2, 0, 2, 0, -2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 0, 2, 0, -2] :=
    (in_context (eq2512 h) [] [2, 0, 2, 0, -2, 0, -2, 0, 2, 0, -2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2544 (h : Relations φ) : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 0, 2, 0] = value φ [-2, 2, 0, -2, 2, 0, 2, 0, 2, -2] := by
  have h0 : value φ [-2, 2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 0, 2, 0] :=
    overlap (eq2543 h) (eq0 h) [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 0, 2, 0] [-2] (by decide)
  have hl : value φ [-2, 2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [-2, 2, 0, -2, 2, 0, 2, 0, 2, -2] := rfl
  have hr : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 0, 2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 0, 2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2548 (h : Relations φ) : value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, -2, 0] = value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] := by
  have h0 : value φ [2, 0, 2, 0, 2, -2, 0, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, -2, 0, -2, 0, 2, 0, 2, 0, -2, 0] :=
    overlap (eq2476 h) (eq2481 h) [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2] [0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] (by decide)
  have hl : value φ [2, 0, 2, 0, 2, -2, 0, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] :=
    ((in_context (eq1 h) [2, 0, 2, 0, 2, -2] [-2, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq0 h) [2, 0, 2, 0, 2] [2, 0, 2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq2 h) [2, 0, 2, 0] [0, 2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq1 h) [2, 0, 2] [2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq2 h) [2, 0] [0, 2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq1 h) [2] [2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2]).trans (in_context (eq2 h) [] [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2])))))))
  have hr : value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, -2, 0, -2, 0, 2, 0, 2, 0, -2, 0] = value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0, -2, 0] :=
    (in_context (eq2477 h) [] [-2, 0, -2, 0, 2, 0, 2, 0, -2, 0])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2555 (h : Relations φ) : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0] = value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2] := by
  have h0 : value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0] :=
    overlap (eq2502 h) (eq0 h) [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0] [-2] (by decide)
  have hl : value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2] = value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2] := rfl
  have hr : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2574 (h : Relations φ) : value φ [0, -2, 0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2] = value φ [-2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2] := by
  have h0 : value φ [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 2, 0, -2, 0, 2, 0, -2, 0] = value φ [0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, 0, 2, 0, -2, 0, 2, 0, -2, 0, 2] :=
    overlap (eq2123 h) (eq2245 h) [0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0] [2, 0, -2, 0, 2, 0, -2, 0] (by decide)
  have hl : value φ [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 2, 0, -2, 0, 2, 0, -2, 0] = value φ [-2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2] :=
    ((in_context (eq2 h) [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0] [0, -2, 0, 2, 0, -2, 0]).trans ((in_context (eq1 h) [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2] [-2, 0, 2, 0, -2, 0]).trans ((in_context (eq0 h) [-2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2] [0, 2, 0, -2, 0]).trans ((in_context (eq8 h) [-2, 2, 0, -2] [2, 0, -2, 0]).trans ((in_context (eq2 h) [-2, 2, 0, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2] [0, -2, 0]).trans ((in_context (eq5 h) [-2, 2, 0, -2, 0, 2, 0, 2] [-2, 0]).trans ((in_context (eq0 h) [-2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, 0] [0]).trans (in_context (eq1 h) [-2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2] []))))))))
  have hr : value φ [0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2, 0, 0, 2, 0, -2, 0, 2, 0, -2, 0, 2] = value φ [0, -2, 0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2] :=
    ((in_context (eq1 h) [0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0, 2] [2, 0, -2, 0, 2, 0, -2, 0, 2]).trans ((in_context (eq2 h) [0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2, 0] [0, -2, 0, 2, 0, -2, 0, 2]).trans ((in_context (eq1 h) [0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2, -2] [-2, 0, 2, 0, -2, 0, 2]).trans ((in_context (eq0 h) [0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, 2] [0, 2, 0, -2, 0, 2]).trans ((in_context (eq4 h) [0, -2, 0, -2, 2, 0, -2, 2, -2, 0] [-2, 0, 2]).trans (in_context (eq1 h) [0, -2, 0, -2, 2, 0, -2, 2, -2] [2, 0, 2, 0, 2, -2, 0, 2]))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2578 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2] = value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2] := by
  have h0 : value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2] :=
    inclusion (eq1796 h) (eq2252 h) [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2] [] (by decide)
  have hl : value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2] = value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2] := rfl
  have hr : value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2] = value φ [-2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2] :=
    ((in_context (eq8 h) [-2] [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [-2, 0, 2, 0, 2, -2, 0, -2, 0, -2] [0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq5 h) [-2, 0, 2, 0, 2] [-2, 0, 2, 0, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq0 h) [-2, 0, 2, 0, 2, 0, -2, 0, -2, 0] [0, 2, 0, -2, 2, 0, 2, 0, 2]).trans (in_context (eq1 h) [-2, 0, 2, 0, 2, 0, -2, 0, -2] [2, 0, -2, 2, 0, 2, 0, 2])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2595 (h : Relations φ) : value φ [-2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2] = value φ [0, -2, 0, 2, 0, 2, 0, -2, 0, 2, -2, 0] := by
  have h0 : value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2, -2, 0] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, -2] :=
    overlap (eq2487 h) (eq100 h) [-2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0] [0, 2, 0, 2, -2, 2, 0, -2, 0, 2, -2, 0] (by decide)
  have hl : value φ [0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 0, 2, 0, 2, -2, 2, 0, -2, 0, 2, -2, 0] = value φ [0, -2, 0, 2, 0, 2, 0, -2, 0, 2, -2, 0] :=
    ((in_context (eq1 h) [0, -2, 0, 2, 0, -2, 2, 0, 2] [2, 0, 2, -2, 2, 0, -2, 0, 2, -2, 0]).trans ((in_context (eq2 h) [0, -2, 0, 2, 0, -2, 2, 0] [0, 2, -2, 2, 0, -2, 0, 2, -2, 0]).trans ((in_context (eq1 h) [0, -2, 0, 2, 0, -2, 2] [2, -2, 2, 0, -2, 0, 2, -2, 0]).trans ((in_context (eq2 h) [0, -2, 0, 2, 0, -2] [-2, 2, 0, -2, 0, 2, -2, 0]).trans (in_context (eq0 h) [0, -2, 0, 2, 0] [2, 0, -2, 0, 2, -2, 0])))))
  have hr : value φ [-2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, 2, -2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 0, -2] = value φ [-2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2] :=
    ((in_context (eq30 h) [-2, 0, 2, 0, 2, -2, 0] [2, 0, 2, 0, -2, 2, -2, 0, -2]).trans ((in_context (eq4 h) [-2, 0, 2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2] [-2, 2, -2, 0, -2]).trans ((in_context (eq2412 h) [-2, 0, 2, 0, 2, -2, 0, -2, 0, 2, 0, -2] [-2, 0, -2]).trans ((in_context (eq1225 h) [-2, 0] [-2, 0, 2, 0, 2, 0, -2, 0, -2]).trans ((in_context (eq1258 h) [-2] [0, 2, 0, 2, 0, -2, 0, -2]).trans ((in_context (eq4 h) [-2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2] [2, 0, 2, 0, -2, 0, -2]).trans ((in_context (eq2 h) [-2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2, 0] [0, 2, 0, -2, 0, -2]).trans ((in_context (eq1 h) [-2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0, 2] [2, 0, -2, 0, -2]).trans ((in_context (eq2 h) [-2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2, 0] [0, -2, 0, -2]).trans (in_context (eq1 h) [-2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, 2] [-2, 0, -2]))))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2643 (h : Relations φ) : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0] = value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2] := by
  have h0 : value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, -2, 0, -2] :=
    overlap (eq2478 h) (eq1629 h) [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2] [0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] (by decide)
  have hl : value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2] :=
    ((in_context (eq1 h) [2, -2, 2, 0, 2, 0, 2, -2] [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq0 h) [2, -2, 2, 0, 2, 0, 2] [0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq4 h) [2, -2] [2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq2 h) [2, -2, 0, 2, 0, 2, 0] [0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq1 h) [2, -2, 0, 2, 0, 2] [-2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2]).trans ((in_context (eq1719 h) [2, -2, 0, 2, 0, 2] []).trans ((in_context (eq4 h) [2, -2, 0] [-2, 0, 2, -2, 0, -2]).trans (in_context (eq1 h) [2, -2] [2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2]))))))))
  have hr : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2, -2, 0, -2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0] :=
    ((in_context (eq0 h) [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0] [0, -2]).trans ((in_context (eq1 h) [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2] [-2]).trans (in_context (eq0 h) [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0] [])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2660 (h : Relations φ) : value φ [-2, 0, 2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [0, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2] := by
  have h0 : value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2] = value φ [-2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0] :=
    overlap (eq2578 h) (eq2532 h) [-2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0] [-2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2] (by decide)
  have hl : value φ [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, -2, 0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2] = value φ [0, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2] :=
    ((in_context (eq0 h) [0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2] [0, 2, 0, -2, 0, -2, 0, 2, 0, 2, -2]).trans (in_context (eq2544 h) [0] [2, -2]))
  have hr : value φ [-2, 0, 2, 0, 2, 0, -2, 0, -2, 2, 0, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [-2, 0, 2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] :=
    ((in_context (eq1 h) [-2, 0, 2, 0, 2, 0, -2, 0, -2, 2] [2, -2, 2, -2, 0, -2, 0, -2, 2, 0]).trans ((in_context (eq2 h) [-2, 0, 2, 0, 2, 0, -2, 0, -2] [-2, 2, -2, 0, -2, 0, -2, 2, 0]).trans (in_context (eq0 h) [-2, 0, 2, 0, 2, 0, -2, 0] [2, -2, 0, -2, 0, -2, 2, 0])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2664 (h : Relations φ) : value φ [0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0] = value φ [-2, 0, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2] := by
  have h0 : value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 0, 2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2] = value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, 2, -2, 0] :=
    overlap (eq2535 h) (eq2595 h) [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] [0, 2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2] (by decide)
  have hl : value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 0, 2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2] = value φ [-2, 0, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2] :=
    ((in_context (eq1 h) [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2] [2, 0, 2, -2, 2, -2, 0, 2, -2, 0, -2]).trans ((in_context (eq2 h) [-2, 0, -2, 0, 2, 0, -2, 2, 0] [0, 2, -2, 2, -2, 0, 2, -2, 0, -2]).trans ((in_context (eq1 h) [-2, 0, -2, 0, 2, 0, -2, 2] [2, -2, 2, -2, 0, 2, -2, 0, -2]).trans ((in_context (eq2 h) [-2, 0, -2, 0, 2, 0, -2] [-2, 2, -2, 0, 2, -2, 0, -2]).trans (in_context (eq0 h) [-2, 0, -2, 0, 2, 0] [2, -2, 0, 2, -2, 0, -2])))))
  have hr : value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, 2, -2, 0] = value φ [0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0] :=
    ((in_context (eq2555 h) [0, 2, 0, 2] [2, -2, 0]).trans (in_context (eq2 h) [0, 2, 0] [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, 0]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2685 (h : Relations φ) : value φ [-2, 0, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2] = value φ [0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2] := by
  have h0 : value φ [0, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] = value φ [-2, 0, -2, 2, 0, 2, 0, 2, -2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2] :=
    overlap (eq12 h) (eq2253 h) [-2, 0, -2, 2, 0, 2, 0, 2, -2] [2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] (by decide)
  have hl : value φ [0, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0] = value φ [0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2] :=
    (in_context (eq1832 h) [0] [])
  have hr : value φ [-2, 0, -2, 2, 0, 2, 0, 2, -2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2] = value φ [-2, 0, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2] :=
    ((in_context (eq0 h) [-2, 0, -2, 2, 0, 2, 0, 2] [0, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq4 h) [-2, 0, -2] [2, 0, -2, 0, 2, -2, 0, -2, 0, -2]).trans ((in_context (eq2 h) [-2, 0, -2, 0, 2, 0, 2, 0] [0, -2, 0, 2, -2, 0, -2, 0, -2]).trans (in_context (eq1 h) [-2, 0, -2, 0, 2, 0, 2] [-2, 0, 2, -2, 0, -2, 0, -2]))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2686 (h : Relations φ) : value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2] = value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] := by
  have h0 : value φ [0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0] = value φ [-2, 0, -2, 0, 2, 0, 2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2] :=
    overlap (eq2685 h) (eq2555 h) [-2, 0, -2, 0, 2, 0, 2] [2, 0, -2, 0, 2, 0, 2, 0, -2, 0] (by decide)
  have hl : value φ [0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0] = value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] :=
    ((in_context (eq2 h) [0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2] [0, -2, 0, 2, 0, 2, 0, -2, 0]).trans ((in_context (eq2548 h) [0, 2, 0, -2] []).trans (in_context (eq0 h) [0, 2, 0] [2, -2, 0, 2, -2, 0, -2, 0, -2, 2])))
  have hr : value φ [-2, 0, -2, 0, 2, 0, 2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2] = value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2] :=
    (in_context (eq2 h) [-2, 0, -2, 0, 2, 0] [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2714 (h : Relations φ) : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2] = value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] := by
  have h0 : value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2] :=
    overlap (eq2643 h) (eq1 h) [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2] [0] (by decide)
  have hl : value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] = value φ [2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] := rfl
  have hr : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2] = value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2736 (h : Relations φ) : value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0] = value φ [2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] := by
  have h0 : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [2, 0, 2, 0, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] :=
    overlap (eq2250 h) (eq2142 h) [2, 0, 2, 0] [2, 0, 2, -2, 0, -2, 0, -2, 2] (by decide)
  have hl : value φ [0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0] :=
    ((in_context (eq425 h) [0, 2, 0, 2, -2, 0, 2, 0] [2]).trans ((in_context (eq1 h) [0, 2, 0, 2, -2, 0, 2] [-2, 0, -2, 0, 2, 0, 2, 0, 2, 2]).trans (in_context (eq2 h) [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0, 2, 0] [])))
  have hr : value φ [2, 0, 2, 0, 0, 2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] = value φ [2, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] :=
    ((in_context (eq1 h) [2, 0, 2] [2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2]).trans ((in_context (eq2 h) [2, 0] [0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2]).trans (in_context (eq1 h) [2] [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2])))
  exact hl.symm.trans (h0.trans hr)

private theorem eq2746 (h : Relations φ) : value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2] = value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0] := by
  have h0 : value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, -2, 0, -2, 0, 2, 0] :=
    overlap (eq2400 h) (eq2473 h) [2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2] [2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2] (by decide)
  have hl : value φ [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2] = value φ [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2] :=
    ((in_context (eq2 h) [0, -2, 0, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0] [-2, 0, -2, 0, -2, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2]).trans ((in_context (eq2186 h) [] [-2, 2, 0, 2, 0, 2, -2]).trans ((in_context (eq118 h) [-2, 2, -2, 0] [2, -2]).trans ((in_context (eq2 h) [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, -2] [-2]).trans (in_context (eq0 h) [-2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2] [])))))
  have hr : value φ [2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, -2, 0, -2, 0, 2, 0] = value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0] :=
    ((in_context (eq2 h) [2, 0, 2, 0, 2, -2, 0, 2, 0, 2, 0] [0, 2, 0, -2, 0, -2, 0, 2, 0]).trans ((in_context (eq1 h) [2, 0, 2, 0, 2, -2, 0, 2, 0, 2] [2, 0, -2, 0, -2, 0, 2, 0]).trans ((in_context (eq2 h) [2, 0, 2, 0, 2, -2, 0, 2, 0] [0, -2, 0, -2, 0, 2, 0]).trans (in_context (eq1 h) [2, 0, 2, 0, 2, -2, 0, 2] [-2, 0, -2, 0, 2, 0]))))
  exact hl.symm.trans (h0.trans hr)

private theorem eq2747 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0] = value φ [2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2] := by
  have h0 : value φ [2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0] :=
    overlap (eq0 h) (eq2746 h) [-2] [2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2] (by decide)
  have hl : value φ [2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2] = value φ [2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2] := rfl
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 0] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2778 (h : Relations φ) : value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2] = value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2] := by
  have h0 : value φ [-2, 0, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, -2, 0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2] = value φ [0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2] :=
    overlap (eq2664 h) (eq2574 h) [0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2] [-2, 0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2] (by decide)
  have hl : value φ [-2, 0, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, -2, 0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2] = value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2] :=
    ((in_context (eq0 h) [-2, 0, -2, 0, 2, 0, 2, -2, 0, 2, -2, 0] [0, -2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2]).trans ((in_context (eq1 h) [-2, 0, -2, 0, 2, 0, 2, -2, 0, 2, -2] [-2, 2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2]).trans ((in_context (eq0 h) [-2, 0, -2, 0, 2, 0, 2, -2, 0, 2] [2, 0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2]).trans ((in_context (eq2 h) [-2, 0, -2, 0, 2, 0, 2, -2, 0] [0, -2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2]).trans ((in_context (eq1 h) [-2, 0, -2, 0, 2, 0, 2, -2] [-2, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2]).trans ((in_context (eq0 h) [-2, 0, -2, 0, 2, 0, 2] [2, -2, 2, 0, 2, 0, 2, -2, 0, 2]).trans (in_context (eq2 h) [-2, 0, -2, 0, 2, 0] [-2, 2, 0, 2, 0, 2, -2, 0, 2])))))))
  have hr : value φ [0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, -2, -2, 2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2] = value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2] :=
    ((in_context (eq0 h) [0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2] [2, 0, -2, 0, 2, 0, 2, 0, -2, 0, -2]).trans ((in_context (eq2 h) [0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2] [0, -2, 0, 2, 0, 2, 0, -2, 0, -2]).trans ((in_context (eq2548 h) [0, 2, 0, -2] [-2]).trans (in_context (eq0 h) [0, 2, 0] [2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2]))))
  exact hl.symm.trans (h0.trans hr)

private theorem eq2784 (h : Relations φ) : value φ [2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2] := by
  have h0 : value φ [2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2] :=
    overlap (eq2747 h) (eq1 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2] [0] (by decide)
  have hl : value φ [2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0] = value φ [2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0] := rfl
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2] := rfl
  exact hl.symm.trans (h0.trans hr)

private theorem eq2790 (h : Relations φ) : value φ [0, -2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0] = value φ [-2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2] := by
  have h0 : value φ [-2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, -2] = value φ [0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2] :=
    overlap (eq2274 h) (eq293 h) [0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2] [-2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, -2] (by decide)
  have hl : value φ [-2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2, 0, -2] = value φ [-2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2] :=
    ((in_context (eq15 h) [-2, 0] [0, 2, 0, -2, 2, -2, 2, 0, -2]).trans ((in_context (eq1 h) [-2, 0, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, 2] [2, 0, -2, 2, -2, 2, 0, -2]).trans ((in_context (eq2 h) [-2, 0, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0] [0, -2, 2, -2, 2, 0, -2]).trans ((in_context (eq1 h) [-2, 0, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2] [-2, 2, -2, 2, 0, -2]).trans ((in_context (eq3 h) [-2, 0, 2, 0, 2, -2, 0, -2, 0, 2] [2, 0, -2]).trans ((in_context (eq2 h) [-2, 0, 2, 0, 2, -2, 0, -2, 0] [-2, 2, -2, 2, 2, 0, -2]).trans (in_context (eq2 h) [-2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] [0, -2])))))))
  have hr : value φ [0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2] = value φ [0, -2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0] :=
    ((in_context (eq5 h) [0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2] [-2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2]).trans ((in_context (eq6 h) [0, -2] [-2, 0, -2, 0, -2, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2]).trans ((in_context (eq0 h) [0, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0] [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2, -2, 2]).trans ((in_context (eq296 h) [0, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0] []).trans ((in_context (eq1836 h) [0, -2, 0] [2, -2, 2, -2, 2, 0]).trans ((in_context (eq3 h) [0, -2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] [2, -2, 2, 0]).trans ((in_context (eq2 h) [0, -2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 2, -2] [-2, 2, 0]).trans ((in_context (eq0 h) [0, -2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 2] [2, 0]).trans (in_context (eq2 h) [0, -2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2] [0])))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq2970 (h : Relations φ) : value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2] = value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, -2] := by
  have h0 : value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 2, -2, 2, -2] = value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, 2, -2, 2, -2, 2] :=
    overlap (eq2686 h) (eq3 h) [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2] [2, -2, 2, -2] (by decide)
  have hl : value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 2, -2, 2, -2] = value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, -2] :=
    ((in_context (eq2 h) [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2] [-2, 2, -2]).trans (in_context (eq0 h) [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] [2, -2]))
  have hr : value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, 2, -2, 2, -2, 2] = value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, 2] :=
    (in_context (eq2 h) [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0] [-2, 2, -2, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq3051 (h : Relations φ) : value φ [2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 2, 0] := by
  have h0 : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 2, 0, 2, 0] = value φ [2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 0, 2, 0, 2, 0, 2] :=
    overlap (eq2784 h) (eq4 h) [2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0] [2, 0, 2, 0] (by decide)
  have hl : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, 2, 0, 2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 2, 0] :=
    ((in_context (eq2 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] [0, 2, 0]).trans (in_context (eq1 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2] [2, 0]))
  have hr : value φ [2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 0, 2, 0, 2, 0, 2] = value φ [2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2] :=
    (in_context (eq1 h) [2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2] [2, 0, 2, 0, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq3094 (h : Relations φ) : value φ [-2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, -2, 0, -2] := by
  have h0 : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [-2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, -2, 0, -2] :=
    overlap (eq2506 h) (eq1629 h) [-2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0] [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] (by decide)
  have hl : value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, -2, 0, -2] :=
    (in_context (eq1646 h) [2, -2, 0, -2, 0, -2, 2, 0, -2, 2] [])
  have hr : value φ [-2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, -2, 0, -2, 0, -2] = value φ [-2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] :=
    ((in_context (eq5 h) [-2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, 0] [-2]).trans ((in_context (eq1 h) [-2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2] [-2, 0, -2, 0, -2, -2]).trans (in_context (eq0 h) [-2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] [])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq3106 (h : Relations φ) : value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] = value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2] := by
  have h0 : value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, -2, 0, -2] :=
    overlap (eq2535 h) (eq1629 h) [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2] [0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] (by decide)
  have hl : value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2] = value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2] :=
    ((in_context (eq1 h) [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2] [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2]).trans (in_context (eq1646 h) [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2] []))
  have hr : value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, -2, 0, -2] = value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2, 2] :=
    ((in_context (eq0 h) [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0] [0, -2]).trans ((in_context (eq1 h) [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2] [-2]).trans (in_context (eq3 h) [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] [])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq3140 (h : Relations φ) : value φ [0, 2, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2] = value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] := by
  have h0 : value φ [0, 2, 0, 2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2] :=
    overlap (eq1623 h) (eq2660 h) [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2] [0, 2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] (by decide)
  have hl : value φ [0, 2, 0, 2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] = value φ [2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0] :=
    ((in_context (eq4 h) [0] [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0]).trans (in_context (eq1 h) [] [2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0]))
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2] = value φ [0, 2, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2] :=
    ((in_context (eq1632 h) [] [2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2]).trans (in_context (eq2 h) [0, 2, -2] [0, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq3174 (h : Relations φ) : value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, -2, 0, -2] = value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] := by
  have h0 : value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, -2, 0, -2] :=
    overlap (eq0 h) (eq3094 h) [-2] [2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] (by decide)
  have hl : value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] = value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] := rfl
  have hr : value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, -2, 0, -2] = value φ [-2, 2, -2, 0, -2, 0, -2, 2, 0, -2, 2, 0, 2, -2, 0, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq3219 (h : Relations φ) : value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2] = value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2] := by
  have h0 : value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0] = value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, -2, 0, -2, 2] :=
    overlap (eq2535 h) (eq1637 h) [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2] [0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0] (by decide)
  have hl : value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0] = value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2] :=
    ((in_context (eq1 h) [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2] [-2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 2, 0, 2, 0]).trans ((in_context (eq1690 h) [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0] []).trans ((in_context (eq1 h) [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2] [-2, 0, 2, -2, 0, -2, 2]).trans (in_context (eq0 h) [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2] [0, 2, -2, 0, -2, 2]))))
  have hr : value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0, -2, -2, 0, -2, 2] = value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2] :=
    ((in_context (eq0 h) [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2, 0] [0, -2, 2]).trans ((in_context (eq1 h) [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 2] [-2, 2]).trans ((in_context (eq3 h) [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] [2]).trans (in_context (eq2 h) [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2, -2] []))))
  exact hl.symm.trans (h0.trans hr)

private theorem eq3342 (h : Relations φ) : value φ [0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 0, 2, 0, 2, -2, 2, 0, 2, 0] = value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2] := by
  have h0 : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, -2, 2, 0, 2, -2, 2, -2] = value φ [0, 2, 0, 2, 0, -2, 0, -2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] :=
    overlap (eq2526 h) (eq303 h) [0, 2, 0, 2, 0, -2, 0, -2] [-2, 2, 0, 2, -2, 2, -2] (by decide)
  have hl : value φ [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, -2, 2, 0, 2, -2, 2, -2] = value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2] :=
    ((in_context (eq0 h) [-2, 0, 2, -2, 0, -2, 0, -2, 2, 0] [2, 0, 2, -2, 2, -2]).trans ((in_context (eq7 h) [-2] [2, -2, 2, -2]).trans ((in_context (eq2 h) [-2, 2, 0, 2, -2, 0, -2, 0, -2] [-2, 2, -2]).trans (in_context (eq0 h) [-2, 2, 0, 2, -2, 0, -2, 0] [2, -2]))))
  have hr : value φ [0, 2, 0, 2, 0, -2, 0, -2, 0, -2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0] = value φ [0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 0, 2, 0, 2, -2, 2, 0, 2, 0] :=
    ((in_context (eq5 h) [0, 2, 0, 2, 0] [2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0]).trans ((in_context (eq1 h) [0, 2, 0, 2] [-2, 0, -2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0]).trans (in_context (eq584 h) [0, 2, 0] [-2, 2, 0, 2, 0])))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq3496 (h : Relations φ) : value φ [0, 2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0] = value φ [-2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2, -2] := by
  have h0 : value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 0, 2, 0, 2, -2, 2, 0, 0, 2, 0, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0] :=
    overlap (eq3342 h) (eq2069 h) [0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 0, 2, 0, 2, -2, 2, 0] [2, 0, -2, 0, 2, 0, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] (by decide)
  have hl : value φ [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2] = value φ [-2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2, -2] :=
    ((in_context (eq2247 h) [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2] [2, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq610 h) [-2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 0, -2] []).trans ((in_context (eq1426 h) [-2] [0, -2, 0, -2, 2, 0, 2, -2]).trans ((in_context (eq5 h) [-2, 0, 2, -2, 0, -2, 0, 2, 0, -2, 0, 2] [-2, 0, -2, 2, 0, 2, -2]).trans ((in_context (eq2245 h) [-2, 0, 2, -2, 0] [-2, 0, -2, -2, 0, -2, 2, 0, 2, -2]).trans ((in_context (eq1 h) [-2, 0, 2, -2] [2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, -2, 0, -2, 2, 0, 2, -2]).trans ((in_context (eq0 h) [-2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2, 0] [0, -2, 2, 0, 2, -2]).trans ((in_context (eq1 h) [-2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2] [-2, 2, 0, 2, -2]).trans ((in_context (eq0 h) [-2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 0, 2] [2, 0, 2, -2]).trans ((in_context (eq2 h) [-2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 0] [0, 2, -2]).trans (in_context (eq1 h) [-2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2] [2, -2])))))))))))
  have hr : value φ [0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 0, 2, 0, 2, -2, 2, 0, 0, 2, 0, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0] = value φ [0, 2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0] :=
    ((in_context (eq1 h) [0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 0, 2, 0, 2, -2, 2] [2, 0, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0]).trans ((in_context (eq2 h) [0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, 2, -2, 0, 2, 0, 2, -2] [0, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0]).trans ((in_context (eq1311 h) [0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0] [-2, 0, 2, 0]).trans ((in_context (eq5 h) [0, 2, 0, -2, 2, 0, 2] [-2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0]).trans ((in_context (eq0 h) [0, 2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 0] [0, -2, 2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0]).trans ((in_context (eq1 h) [0, 2, 0, -2, 2, 0, 2, 0, -2, 0, -2] [-2, 2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0]).trans ((in_context (eq0 h) [0, 2, 0, -2, 2, 0, 2, 0, -2, 0] [2, 0, -2, 0, 2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0]).trans ((in_context (eq2246 h) [0, 2, 0, -2, 2] [-2, 0, -2, 2, 0, -2, 0, 2, 0]).trans ((in_context (eq0 h) [0, 2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, 0] [0, -2, 2, 0, -2, 0, 2, 0]).trans (in_context (eq1 h) [0, 2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2] [-2, 2, 0, -2, 0, 2, 0]))))))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq3497 (h : Relations φ) : value φ [2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2, -2] = value φ [0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0] := by
  have h0 : value φ [2, 0, -2, 2, -2, 0, 2, 2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0] = value φ [-2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2, -2] :=
    overlap (eq1673 h) (eq3496 h) [-2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2] [2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0] (by decide)
  have hl : value φ [2, 0, -2, 2, -2, 0, 2, 2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0] = value φ [0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0] :=
    ((in_context (eq2 h) [2, 0, -2, 2, -2, 0] [0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0]).trans ((in_context (eq1 h) [2, 0, -2, 2, -2] [-2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0]).trans ((in_context (eq0 h) [2, 0, -2, 2] [2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0]).trans ((in_context (eq2 h) [2, 0, -2] [-2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0]).trans ((in_context (eq0 h) [2, 0] [0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0]).trans ((in_context (eq1 h) [2] [2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0]).trans (in_context (eq2 h) [] [0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0])))))))
  have hr : value φ [-2, 0, -2, 0, -2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2, -2] = value φ [2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2, -2] :=
    ((in_context (eq1711 h) [] [2, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2, -2]).trans (in_context (eq2 h) [2, 0, -2, 2, -2, 0, 2, 0] [-2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2, -2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq3499 (h : Relations φ) : value φ [2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2] = value φ [0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2] := by
  have h0 : value φ [0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2] = value φ [2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2] :=
    overlap (eq3497 h) (eq0 h) [2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2] [-2] (by decide)
  have hl : value φ [0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2] = value φ [0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2] := rfl
  have hr : value φ [2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2] = value φ [2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq3527 (h : Relations φ) : value φ [2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2] = value φ [0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2] := by
  have h0 : value φ [0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2] = value φ [2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2] :=
    overlap (eq3499 h) (eq2 h) [2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2] [2] (by decide)
  have hl : value φ [0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2] = value φ [0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2] := rfl
  have hr : value φ [2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2] = value φ [2, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2] := rfl
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq3682 (h : Relations φ) : value φ [2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2] = value φ [-2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2] := by
  have h0 : value φ [2, -2, 0, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2] = value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2] :=
    overlap (eq1630 h) (eq3527 h) [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2] [0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2] (by decide)
  have hl : value φ [2, -2, 0, 0, -2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2] = value φ [-2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2] :=
    ((in_context (eq1 h) [2, -2] [-2, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2]).trans ((in_context (eq0 h) [2] [2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2]).trans (in_context (eq2 h) [] [-2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2])))
  have hr : value φ [-2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, 2, -2, 0, -2, 0, -2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2] = value φ [2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2] :=
    (in_context (eq1638 h) [] [0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq3703 (h : Relations φ) : value φ [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2] = value φ [2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2] := by
  have h0 : value φ [2, -2, 2, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2] = value φ [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0, 0, -2, 0, -2, 0, -2] :=
    overlap (eq435 h) (eq2261 h) [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0] [0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2] (by decide)
  have hl : value φ [2, -2, 2, -2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2] = value φ [2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2] :=
    ((in_context (eq5 h) [2, -2, 2, -2, 0, 2, 0, 2] [-2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq0 h) [2, -2, 2, -2, 0, 2, 0, 2, 0, -2, 0, -2, 0] [0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq1 h) [2, -2, 2, -2, 0, 2, 0, 2, 0, -2, 0, -2] [-2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq0 h) [2, -2, 2, -2, 0, 2, 0, 2, 0, -2, 0] [0, -2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq1 h) [2, -2, 2, -2, 0, 2, 0, 2, 0, -2] [-2, 2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq0 h) [2, -2, 2, -2, 0, 2, 0, 2, 0] [2, 0, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq4 h) [2, -2, 2, -2, 0] [-2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq1 h) [2, -2, 2, -2] [2, 0, 2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq10 h) [2, -2, 2] [-2, 2, 0, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq0 h) [2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0, 2] [2, 0, -2, 0, -2, 0, -2, 2]).trans ((in_context (eq2 h) [2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0] [0, -2, 0, -2, 0, -2, 2]).trans (in_context (eq1 h) [2, -2, 2, 0, -2, 0, -2, 2, 0, 2] [-2, 0, -2, 0, -2, 2]))))))))))))
  have hr : value φ [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0, 0, -2, 0, -2, 0, -2] = value φ [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2] :=
    (in_context (eq1 h) [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2] [-2, 0, -2, 0, -2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq3704 (h : Relations φ) : value φ [2, -2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] = value φ [-2, 2, -2, 2, 0, -2, 0, -2, 2, -2] := by
  have h0 : value φ [2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2] = value φ [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, -2, 0, -2, 2, 0, -2] :=
    overlap (eq3703 h) (eq1664 h) [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2] [2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2] (by decide)
  have hl : value φ [2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, 2, 0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2] = value φ [2, -2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] :=
    ((in_context (eq2 h) [2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2] [0, -2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2]).trans ((in_context (eq5 h) [2, -2, 2, 0, -2, 0, -2, 2, 0, 2] [-2, 2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2]).trans ((in_context (eq0 h) [2, -2, 2, 0, -2, 0, -2, 2, 0, 2, 0, -2, 0, -2, 0] [2, -2, 0, -2, 0, -2, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2]).trans ((in_context (eq2790 h) [2, -2, 2, 0, -2, 0, -2, 2, 0, 2] [2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2]).trans ((in_context (eq1054 h) [] [-2, 0, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2]).trans ((in_context (eq2245 h) [0, 2, 0, 2] [-2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2]).trans ((in_context (eq4 h) [0] [-2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2]).trans ((in_context (eq1 h) [] [2, 0, 2, 0, 2, -2, 0, 2, 0, -2, 0, 2, -2, 2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, -2, 2]).trans ((in_context (eq3682 h) [2, 0, 2, 0] [0, 2, 0, -2, 2]).trans ((in_context (eq2247 h) [2, 0, 2, 0, -2, 0, 2, 0, -2, 0, 2, -2] [-2, 2]).trans ((in_context (eq2253 h) [2] [2, 0, -2, 0, 2, 0, -2, -2, 2]).trans ((in_context (eq0 h) [2, -2, 0, 2, 0, -2, 0, 2, -2, 0, -2, 0, -2, 2, 0, -2, 0, 2, 0] [2]).trans (in_context (eq2714 h) [2, -2, 0, 2, 0] [])))))))))))))
  have hr : value φ [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, -2, 0, -2, 2, 0, -2] = value φ [-2, 2, -2, 2, 0, -2, 0, -2, 2, -2] :=
    ((in_context (eq0 h) [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2, 0] [0, -2, 2, 0, -2]).trans ((in_context (eq1 h) [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2, -2] [-2, 2, 0, -2]).trans ((in_context (eq0 h) [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0, 2] [2, 0, -2]).trans ((in_context (eq2 h) [-2, 2, -2, 2, 0, -2, 0, -2, 2, 0] [0, -2]).trans (in_context (eq1 h) [-2, 2, -2, 2, 0, -2, 0, -2, 2] [-2])))))
  exact hl.symm.trans (h0.trans hr)

private theorem eq3705 (h : Relations φ) : value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2] = value φ [2, -2, 2, 0, 2, 0, 2] := by
  have h0 : value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, -2, -2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] = value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, -2, 2, -2, 2, 0, -2, 0, -2, 2, -2] :=
    overlap (eq2970 h) (eq3704 h) [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2] [-2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] (by decide)
  have hl : value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, -2, -2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] = value φ [2, -2, 2, 0, 2, 0, 2] :=
    ((in_context (eq0 h) [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2] [0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0]).trans ((in_context (eq2736 h) [] [2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0]).trans ((in_context (eq2505 h) [2, -2, 2] [0, 2, -2, 0, -2, 0]).trans ((in_context (eq4 h) [2, -2] [-2, 0, -2, 2, 0, 0, 2, -2, 0, -2, 0]).trans ((in_context (eq1 h) [2, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2, 2] [2, -2, 0, -2, 0]).trans ((in_context (eq2 h) [2, -2, 0, 2, 0, 2, 0, 2, -2, 0, -2] [-2, 0, -2, 0]).trans ((in_context (eq0 h) [2, -2, 0, 2, 0, 2, 0, 2, -2, 0] [0, -2, 0]).trans ((in_context (eq1 h) [2, -2, 0, 2, 0, 2, 0, 2, -2] [-2, 0]).trans ((in_context (eq0 h) [2, -2, 0, 2, 0, 2, 0, 2] [0]).trans ((in_context (eq4 h) [2, -2, 0] []).trans (in_context (eq1 h) [2, -2] [2, 0, 2, 0, 2])))))))))))
  have hr : value φ [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, -2, 2, -2, -2, 2, -2, 2, 0, -2, 0, -2, 2, -2] = value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2, -2] :=
    ((in_context (eq3219 h) [] [-2, -2, 2, -2, 2, 0, -2, 0, -2, 2, -2]).trans ((in_context (eq0 h) [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, 2, -2, 2] [-2, 2, -2, 2, 0, -2, 0, -2, 2, -2]).trans ((in_context (eq3106 h) [] [-2, 2, 0, -2, 0, -2, 2, -2]).trans ((in_context (eq0 h) [-2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0] [2, 0, -2, 0, -2, 2, -2]).trans (in_context (eq2778 h) [] [0, -2, 0, -2, 2, -2])))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq3706 (h : Relations φ) : value φ [0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2] = value φ [2, -2, 2, -2, 0] := by
  have h0 : value φ [2, -2, 2, 0, 2, 0, 2, 2, 0, 2, 0, -2, 0] = value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2] :=
    overlap (eq3705 h) (eq862 h) [0, 2, 0, 2, -2, 0, 2, -2, 0, -2] [2, 0, 2, 0, -2, 0] (by decide)
  have hl : value φ [2, -2, 2, 0, 2, 0, 2, 2, 0, 2, 0, -2, 0] = value φ [2, -2, 2, -2, 0] :=
    ((in_context (eq2 h) [2, -2, 2, 0, 2, 0] [0, 2, 0, -2, 0]).trans ((in_context (eq1 h) [2, -2, 2, 0, 2] [2, 0, -2, 0]).trans ((in_context (eq2 h) [2, -2, 2, 0] [0, -2, 0]).trans (in_context (eq1 h) [2, -2, 2] [-2, 0]))))
  have hr : value φ [0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 2, 0, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2] = value φ [0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2] :=
    ((in_context (eq3140 h) [0, 2, 0, 2, -2] [0, -2, 0, -2]).trans (in_context (eq1 h) [0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] [-2, 0, -2]))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq3707 (h : Relations φ) : value φ [0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] = value φ [2, -2, 0] := by
  have h0 : value φ [2, -2, 2, -2, 0, 0, -2, 2, 0] = value φ [0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] :=
    overlap (eq3706 h) (eq2337 h) [0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0] [0, -2, 2, 0] (by decide)
  have hl : value φ [2, -2, 2, -2, 0, 0, -2, 2, 0] = value φ [2, -2, 0] :=
    ((in_context (eq1 h) [2, -2, 2, -2] [-2, 2, 0]).trans ((in_context (eq0 h) [2, -2, 2] [2, 0]).trans (in_context (eq2 h) [2, -2] [0])))
  have hr : value φ [0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 0, 0, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] = value φ [0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2] :=
    (in_context (eq1 h) [0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2] [2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2, 2])
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq3711 (h : Relations φ) : value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0] = value φ [0, 2, -2, 0, -2] := by
  have h0 : value φ [2, -2, 0, 0, -2, 2, 0, 2, -2, 0, -2] = value φ [0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] :=
    overlap (eq3707 h) (eq3174 h) [0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0] [0, -2, 2, 0, 2, -2, 0, -2] (by decide)
  have hl : value φ [2, -2, 0, 0, -2, 2, 0, 2, -2, 0, -2] = value φ [0, 2, -2, 0, -2] :=
    ((in_context (eq1 h) [2, -2] [-2, 2, 0, 2, -2, 0, -2]).trans ((in_context (eq0 h) [2] [2, 0, 2, -2, 0, -2]).trans (in_context (eq2 h) [] [0, 2, -2, 0, -2])))
  have hr : value φ [0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, 2, 0, -2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0] :=
    ((in_context (eq880 h) [0, 2] [-2, 2, 0, 2, 0, 2, -2, 0, 2, -2, 0, -2, 0]).trans ((in_context (eq2415 h) [0, 2, -2, 0, 2, -2, 0, -2, 0, -2, 2] [2, -2, 0, -2, 0]).trans ((in_context (eq3051 h) [0] [-2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0]).trans ((in_context (eq3140 h) [0, -2, 2, 0, 2, 0, 2, -2] [0, -2, 0]).trans ((in_context (eq2415 h) [0] [2, -2, 0, -2, 0, -2, 2, 0, 0, -2, 0]).trans ((in_context (eq1 h) [] [-2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, 0, 0, -2, 0]).trans (in_context (eq1 h) [-2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2] [-2, 0])))))))
  exact (hl.symm.trans (h0.trans hr)).symm

private theorem eq3713 (h : Relations φ) : value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, -2] = value φ [2, -2, 0, -2, 0] := by
  have h0 : value φ [0, 2, -2, 0, -2, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0] = value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] :=
    overlap (eq3711 h) (eq2335 h) [-2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0] [-2, 0, -2, 2, 0, 2, -2, 0, -2, 0] (by decide)
  have hl : value φ [0, 2, -2, 0, -2, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0] = value φ [2, -2, 0, -2, 0] :=
    ((in_context (eq0 h) [0, 2, -2, 0] [0, -2, 2, 0, 2, -2, 0, -2, 0]).trans ((in_context (eq1 h) [0, 2, -2] [-2, 2, 0, 2, -2, 0, -2, 0]).trans ((in_context (eq0 h) [0, 2] [2, 0, 2, -2, 0, -2, 0]).trans ((in_context (eq2 h) [0] [0, 2, -2, 0, -2, 0]).trans (in_context (eq1 h) [] [2, -2, 0, -2, 0])))))
  have hr : value φ [-2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, 0, -2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2] = value φ [0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, -2] :=
    ((in_context (eq1 h) [-2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2] [-2, 0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2]).trans ((in_context (eq0 h) [-2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0] [0, -2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2]).trans ((in_context (eq1 h) [-2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2] [-2, 2, 0, 2, -2, 0, -2, 0, -2, 2, -2]).trans ((in_context (eq0 h) [-2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2] [2, 0, 2, -2, 0, -2, 0, -2, 2, -2]).trans ((in_context (eq2 h) [-2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2] [0, 2, -2, 0, -2, 0, -2, 2, -2]).trans (in_context (eq2415 h) [] [2, -2, 0, -2, 0, -2, 2, -2]))))))
  exact (hl.symm.trans (h0.trans hr)).symm

theorem ninth_of_relations (h : Relations φ) : value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2] = 1 := by
  have hfinal : value φ [2, 0, -2, 2, 0, 2, 0, 2, -2, 2, 0, 2, 0, 2, -2, 2, -2, 0, -2, 0, -2, 2, -2, 0, -2, 0, -2] = value φ [] :=
    ((in_context (eq3713 h) [2] [0, -2, 0, -2]).trans ((in_context (eq2 h) [] [-2, 0, -2, 0, 0, -2, 0, -2]).trans ((in_context (eq1 h) [-2, 0, -2] [-2, 0, -2]).trans ((in_context (eq0 h) [-2, 0] [0, -2]).trans ((in_context (eq1 h) [-2] [-2]).trans (in_context (eq0 h) [] []))))))
  exact hfinal



private def mapFamily (h : Presentation →* E) : InvolutionFamily E where
  val n := h (RelatorLifts.conjugate n)
  inv_eq n := inv_eq_of_mul_eq_one_left (by
    simpa only [map_pow, map_one, pow_two, map_mul] using
      congrArg h (RelatorLifts.conjugate_sq n))

variable {h : Presentation →* E}

private theorem value_eq_map (w : List ℤ) : value (mapFamily h) w = h (RelatorLifts.value w) := by
  simp only [value, mapFamily, RelatorLifts.value, map_list_prod, List.map_map, Function.comp_def]

private theorem target_value (i : Fin 12)
    (htarget : h (Subgroup.CosetWordCertificate.eval liftedGenerator (relationLetters i)) = 1) :
    value (mapFamily h) ((relationIndices i).map RelatorLifts.markedIndex) = 1 := by
  simpa only [value_eq_map, ← RelatorLifts.relation_eq_value] using htarget

private theorem mapped_initial (i : Fin 12) (hi : i.val < 4) :
    h (Subgroup.CosetWordCertificate.eval liftedGenerator (relationLetters i)) = 1 := by
  rw [initial_relations i hi, map_one]

private theorem value_neg_eq_one (f : PerfectCentralCovering.Cover E He)
    (ht : f.toMonoidHom.comp h = presentationMap)
    (w : List ℤ) (hw : value (mapFamily h) w = 1) : value (mapFamily h) (w.map (fun n => -n)) = 1 := by
  rw [value_eq_map] at hw ⊢
  exact image_value_neg_eq_one f h ht w hw

private theorem relations_of_even_and_seven (f : PerfectCentralCovering.Cover E He)
    (ht : f.toMonoidHom.comp h = presentationMap)
    (heven : EvenImageRelations h)
    (hseven : h (Subgroup.CosetWordCertificate.eval liftedGenerator (relationLetters 7)) = 1) :
    Relations (mapFamily h) := by
  intro i
  fin_cases i
  · exact target_value 0 (mapped_initial 0 (by decide))
  · exact target_value 1 (mapped_initial 1 (by decide))
  · exact target_value 2 (mapped_initial 2 (by decide))
  · exact target_value 3 (mapped_initial 3 (by decide))
  · exact target_value 4 (heven 4 (Or.inl rfl))
  · exact target_value 5 (image_five_of_four h (heven 4 (Or.inl rfl)))
  · exact target_value 6 (heven 6 (Or.inr (Or.inl rfl)))
  · exact target_value 7 hseven
  · exact target_value 8 (image_eight_of_seven f h ht hseven)
  · exact target_value 10 (heven 10 (Or.inr (Or.inr (Or.inl rfl))))
  · exact target_value 11 (heven 11 (Or.inr (Or.inr (Or.inr rfl))))
  · exact value_neg_eq_one f ht _ (target_value 6 (heven 6 (Or.inr (Or.inl rfl))))
  · exact value_neg_eq_one f ht _ (target_value 10 (heven 10 (Or.inr (Or.inr (Or.inl rfl)))))
  · exact value_neg_eq_one f ht _ (target_value 11 (heven 11 (Or.inr (Or.inr (Or.inr rfl)))))

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd.MappedConsequences

namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd

/-- The ninth equation follows in the actual marked covering image from the
four even equations and the seventh; reflected compatibility is discharged. -/
theorem image_nine_of_even_and_seven {E : Type*} [Group E]
    (f : PerfectCentralCovering.Cover E He) (h : Presentation →* E)
    (ht : f.toMonoidHom.comp h = presentationMap)
    (heven : EvenImageRelations h)
    (hseven : h (Subgroup.CosetWordCertificate.eval liftedGenerator (relationLetters 7)) = 1) :
    h (Subgroup.CosetWordCertificate.eval liftedGenerator (relationLetters 9)) = 1 := by
  rw [RelatorLifts.relation_eq_value, ← MappedConsequences.value_eq_map]
  exact MappedConsequences.ninth_of_relations
    (MappedConsequences.relations_of_even_and_seven f ht heven hseven)

/-- All three mapped odd equations reduce to the single seventh equation.
This is a conditional reduction, not a proof of that remaining equation. -/
theorem image_odd_of_even_and_seven {E : Type*} [Group E]
    (f : PerfectCentralCovering.Cover E He) (h : Presentation →* E)
    (ht : f.toMonoidHom.comp h = presentationMap)
    (heven : EvenImageRelations h)
    (hseven : h (Subgroup.CosetWordCertificate.eval liftedGenerator (relationLetters 7)) = 1) :
    OddImageRelations h := by
  intro i hi
  rcases hi with rfl | rfl | rfl
  · exact hseven
  · exact image_eight_of_seven f h ht hseven
  · exact image_nine_of_even_and_seven f h ht heven hseven

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd
