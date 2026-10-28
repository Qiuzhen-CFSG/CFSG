module
public import Glauberman.FixedNormalPairRows
public import Theory.GroupTheory.SubgroupTransport.IntersectionRectangle

/-!
# Recursive pairs in the actual intersection rectangle

Every row of the fixed-normal pair recursion is a literal restriction of
the original subgroup isomorphism. Its left and right members are the
first two cells on the corresponding diagonal of the intersection rectangle.
Thus the elementary maximum-abelian row constructed by finite descent is an
actual cell of the original diagram.

Source: Niles, *Pushing-up in finite groups* (1979), the intersection diagram
in Section 2 and Propositions 4.4–4.6. The final theorem applies the rectangle
identities to the already proved maximum-abelian descent.
-/

public section
open Subgroup Theory.GroupTheory.SubgroupTransport
namespace Glauberman.IntersectionPair
variable {G : Type*} [Group G]

theorem row_succ_next (P : IntersectionPair G) (n : ℕ) :
    P.row (n + 1) = (P.row n).next := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih => exact ih P.next

theorem row_left_le (P : IntersectionPair G) (n : ℕ) : (P.row n).left ≤ P.left := by
  induction n generalizing P with
  | zero => exact le_rfl
  | succ n ih => exact (ih P.next).trans P.next_left_le

theorem row_right_le (P : IntersectionPair G) (n : ℕ) : (P.row n).right ≤ P.right := by
  induction n generalizing P with
  | zero => exact le_rfl
  | succ n ih => exact (ih P.next).trans inf_le_right

theorem row_equiv_apply (P : IntersectionPair G) (n : ℕ) (x : (P.row n).left) :
    ((P.row n).equiv x : G) = (P.equiv ⟨x, row_left_le P n x.property⟩ : G) := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    calc
      ((P.next.row n).equiv x : G) =
          (P.next.equiv ⟨x, row_left_le P.next n x.property⟩ : G) := ih P.next x
      _ = _ := rfl

theorem row_equiv_symm_apply (P : IntersectionPair G) (n : ℕ)
    (x : (P.row n).right) :
    ((P.row n).equiv.symm x : G) =
      (P.equiv.symm ⟨x, row_right_le P n x.property⟩ : G) := by
  have he := row_equiv_apply P n ((P.row n).equiv.symm x)
  rw [MulEquiv.apply_symm_apply] at he
  have hh : P.equiv ⟨(P.row n).equiv.symm x,
      row_left_le P n ((P.row n).equiv.symm x).property⟩ =
      ⟨x, row_right_le P n x.property⟩ := Subtype.ext he.symm
  have hh' := congrArg P.equiv.symm hh
  rw [MulEquiv.symm_apply_apply] at hh'
  exact congrArg Subtype.val hh'

private theorem image_restriction {S T R Q : Subgroup G} (φ : S ≃* T) (ψ : R ≃* Q)
    (hRS : R ≤ S) (hφ : ∀ x : R, (ψ x : G) = (φ ⟨x, hRS x.property⟩ : G))
    (A : Subgroup G) : image ψ A = image φ (A ⊓ R) := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact ⟨⟨y, hRS y.property⟩, ⟨hy, y.property⟩, (hφ y).symm⟩
  · rintro x ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy.2⟩, hy.1, hφ ⟨y, hy.2⟩⟩

theorem image_row_equiv (P : IntersectionPair G) (n : ℕ) (A : Subgroup G) :
    image (P.row n).equiv A = image P.equiv (A ⊓ (P.row n).left) :=
  image_restriction P.equiv (P.row n).equiv (row_left_le P n) (row_equiv_apply P n) A

theorem image_row_equiv_symm (P : IntersectionPair G) (n : ℕ) (A : Subgroup G) :
    image (P.row n).equiv.symm A = image P.equiv.symm (A ⊓ (P.row n).right) :=
  image_restriction P.equiv.symm (P.row n).equiv.symm
    (row_right_le P n) (row_equiv_symm_apply P n) A

theorem row_left_right_cells (P : IntersectionPair G) (n : ℕ) :
    (P.row n).left = intervalCell P.equiv 0 (n + 1) ∧
      (P.row n).right = intervalCell P.equiv 1 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi : (P.row n).left ⊓ (P.row n).right = intervalCell P.equiv 1 (n + 1) := by
      rw [ih.1, ih.2, intervalCell_adjacent_inf]
    have himg : image (P.row n).equiv.symm ((P.row n).left ⊓ (P.row n).right) =
        image P.equiv.symm (intervalCell P.equiv 1 (n + 1)) := by
      rw [image_row_equiv_symm, inf_assoc, inf_idem, hi]
    rw [row_succ_next]
    constructor
    · change image (P.row n).equiv.symm ((P.row n).left ⊓ (P.row n).right) = _
      rw [himg]
      change image P.equiv.symm (forwardChain P.equiv 1 ⊓ forwardChain P.equiv.symm (n + 1)) = _
      rw [forwardChain_one, inf_comm, image_domain_inf, ← forwardChain_succ]
      exact (intervalCell_zero_left _ _).symm
    · exact hi

theorem row_intersection_cell (P : IntersectionPair G) (n : ℕ) :
    (P.row n).left ⊓ (P.row n).right = intervalCell P.equiv 1 (n + 1) := by
  rw [(row_left_right_cells P n).1, (row_left_right_cells P n).2,
    intervalCell_adjacent_inf]

/-- The actual terminal maximum-abelian intersection is a cell of the
original partial isomorphism, without changing the subgroup or its embedding. -/
theorem exists_elementary_maximum_cell [Finite G] (P : IntersectionPair G)
    (h : NumericalPair P.left P.right P.equiv) :
    ∃ n, IsElementaryAbelian 2 ↥(intervalCell P.equiv 1 (n + 1)) ∧
      intervalCell P.equiv 1 (n + 1) ∈ thompsonAbelianSubgroups P.left ∧
      intervalCell P.equiv 1 (n + 1) ∈ thompsonAbelianSubgroups P.right := by
  obtain ⟨n, hE, hL, hR⟩ := exists_elementary_maximum_row P h
  rw [row_intersection_cell] at hE hL hR
  exact ⟨n, hE, hL, hR⟩

end Glauberman.IntersectionPair
