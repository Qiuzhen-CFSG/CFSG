module

public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Tactic.Linarith

/-!
# Factoring a centralizer from a conjugate abelian subgroup

Let Q=C_R(V), and suppose B is an abelian subgroup of R whose centralizer
has the same order as Q and lies in BQ. If the image of B modulo Q and
the action of B on V have the same index, then Q=V C_Q(B).
The proof compares the orders of the two normalized products B C_Q(B)
and V C_Q(B). This is the counting step in Aschbacher--Smith 3.3.28,
printed p.601, for the binary G₂ local core.
-/

public section
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Equal image and fixed-space indices force the centralizer factorization
used by the conjugate-module argument. -/
theorem eq_sup_centralizer_of_equal_indices
    (R Q V B : Subgroup G) (n : ℕ)
    (hQR : Q ≤ R) (hVQ : V ≤ Q) (hBR : B ≤ R)
    (hQV : Q ≤ centralizer (V : Set G))
    (hBB : B ≤ centralizer (B : Set G))
    (hBQ : B ≤ normalizer (Q : Set G))
    (hcover : R ⊓ centralizer (B : Set G) ≤ B ⊔ Q)
    (hcard : Nat.card (R ⊓ centralizer (B : Set G) : Subgroup G) = Nat.card Q)
    (himage : Nat.card B = n * Nat.card (B ⊓ Q : Subgroup G))
    (hfixed : Nat.card V = n * Nat.card (V ⊓ centralizer (B : Set G) : Subgroup G)) :
    Q = V ⊔ (Q ⊓ centralizer (B : Set G)) := by
  let C := Q ⊓ centralizer (B : Set G)
  let F := V ⊓ centralizer (B : Set G)
  have hCB : C ≤ centralizer (B : Set G) := inf_le_right
  have hBC : B ≤ normalizer (C : Set G) :=
    (le_centralizer_iff.mp hCB).trans (centralizer_le_normalizer _)
  have hcentral : R ⊓ centralizer (B : Set G) = B ⊔ C := by
    apply le_antisymm
    · intro x hx
      have hxprod : x ∈ (Q : Set G) * (B : Set G) := by
        rw [← coe_mul_of_right_le_normalizer_left Q B hBQ]
        change x ∈ Q ⊔ B
        rw [sup_comm]
        exact hcover hx
      obtain ⟨q, hq, b, hb, rfl⟩ := hxprod
      have hqC : q ∈ centralizer (B : Set G) := by
        have hh := (centralizer (B : Set G)).mul_mem hx.2
          ((centralizer (B : Set G)).inv_mem (hBB hb))
        simpa only [mul_inv_cancel_right] using hh
      exact mul_mem (mem_sup_right ⟨hq, hqC⟩) (mem_sup_left hb)
    · exact sup_le (le_inf hBR hBB) (le_inf (inf_le_left.trans hQR) hCB)
  have hBCinf : B ⊓ C = B ⊓ Q := by
    apply le_antisymm (inf_le_inf_left _ inf_le_left)
    exact fun _ hx => ⟨hx.1, hx.2, hBB hx.1⟩
  have hVCinf : V ⊓ C = F := by
    apply le_antisymm
    · exact fun _ hx => ⟨hx.1, hx.2.2⟩
    · exact fun _ hx => ⟨hx.1, hVQ hx.1, hx.2⟩
  have hpB := card_mul_eq_card_inf_mul_card_sup_of_normalizes C B hBC
  rw [inf_comm C B, hBCinf, sup_comm C B, ← hcentral, hcard, himage] at hpB
  have hc : n * Nat.card C = Nat.card Q := by
    have hp : 0 < Nat.card (B ⊓ Q : Subgroup G) := Nat.card_pos
    nlinarith [hpB]
  have hpV := card_mul_eq_card_inf_mul_card_sup_of_normalizes V C
    ((inf_le_left.trans hQV).trans (centralizer_le_normalizer _))
  rw [hVCinf, hfixed] at hpV
  have hj : Nat.card (V ⊔ C : Subgroup G) = Nat.card Q := by
    have hp : 0 < Nat.card F := Nat.card_pos
    nlinarith [hpV, hc]
  exact (eq_of_le_of_card_ge (sup_le hVQ inf_le_left) hj.ge).symm

end Subgroup
