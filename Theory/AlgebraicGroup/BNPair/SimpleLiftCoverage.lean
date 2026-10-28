module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.Group

/-!
A generation criterion for Bruhat coverage, extracted from the BN-pair argument
of GLS3, §1.11 (Definition 1.11.1 and Theorem 1.11.3), and Borel, §14.15.

Assume `B` and `N` generate the group, and chosen lifts in `N` generate `N`
together with `B`. If each lift has square in `B` and satisfies the local
two-cell exchange law, every element belongs to `B N B`. The proof inducts on
words in `B` and the lifts. Borel factors are absorbed on the left, exchange
handles a lift, and its square handles an inverse lift.

This criterion needs neither a quotient by `B ∩ N` nor the nontriviality and
finiteness conditions of a full Tits system. It does not construct the lifts
or prove the geometric hypotheses for an algebraic group.
-/

namespace Theory.AlgebraicGroup.BruhatGeneration

variable {X : Type*} [Group X]

/-- Multiplication by a simple lift moves a normalizer cell into one of two cells.
This is the local exchange law, not a global coverage hypothesis. -/
@[expose]
public def SimpleLiftExchange (B N : Subgroup X) (S : Set X) : Prop :=
  ∀ s ∈ S, ∀ b ∈ B, ∀ n ∈ N,
    ∃ a c : X, a ∈ B ∧ c ∈ B ∧
      (s * b * n = a * (s * n) * c ∨ s * b * n = a * n * c)

/-- Generation and local two-cell exchange imply B–N–B coverage.
Lift squares in `B` allow the closure induction to include inverse generators. -/
public theorem exists_factorization_of_simpleLiftExchange
    (B N : Subgroup X) (S : Set X)
    (hBN : Subgroup.closure ((B : Set X) ∪ (N : Set X)) = ⊤)
    (hN : N ≤ Subgroup.closure ((B : Set X) ∪ S))
    (hSN : S ⊆ (N : Set X))
    (hsquare : ∀ s ∈ S, s * s ∈ B)
    (hexchange : SimpleLiftExchange B N S) (g : X) :
    ∃ b n c : X, b ∈ B ∧ n ∈ N ∧ c ∈ B ∧ g = b * n * c := by
  let F : X → Prop := fun x =>
    ∃ b n c : X, b ∈ B ∧ n ∈ N ∧ c ∈ B ∧ x = b * n * c
  have hleft (b : X) (hb : b ∈ B) (x : X) (hx : F x) : F (b * x) := by
    obtain ⟨a, n, c, ha, hn, hc, rfl⟩ := hx
    exact ⟨b * a, n, c, B.mul_mem hb ha, hn, hc, by simp only [mul_assoc]⟩
  have hsimple (s : X) (hs : s ∈ S) (x : X) (hx : F x) : F (s * x) := by
    obtain ⟨b, n, c, hb, hn, hc, rfl⟩ := hx
    obtain ⟨a, d, ha, hd, h | h⟩ := hexchange s hs b hb n hn
    · refine ⟨a, s * n, d * c, ha, N.mul_mem (hSN hs) hn, B.mul_mem hd hc, ?_⟩
      calc
        s * (b * n * c) = (s * b * n) * c := by simp only [mul_assoc]
        _ = a * (s * n) * (d * c) := by rw [h, mul_assoc]
    · refine ⟨a, n, d * c, ha, hn, B.mul_mem hd hc, ?_⟩
      calc
        s * (b * n * c) = (s * b * n) * c := by simp only [mul_assoc]
        _ = a * n * (d * c) := by rw [h, mul_assoc]
  have hgen : Subgroup.closure ((B : Set X) ∪ S) = ⊤ := by
    apply top_unique
    rw [← hBN]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with hx | hx
    · exact Subgroup.subset_closure (Or.inl hx)
    · exact hN hx
  have hg : g ∈ Subgroup.closure ((B : Set X) ∪ S) := by
    rw [hgen]
    exact Subgroup.mem_top g
  change F g
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨1, 1, 1, B.one_mem, N.one_mem, B.one_mem, by simp⟩
  | mul_left x hx y _ ih =>
      rcases hx with hx | hx
      · exact hleft x hx y ih
      · exact hsimple x hx y ih
  | inv_mul_cancel x hx y _ ih =>
      rcases hx with hx | hx
      · exact hleft x⁻¹ (B.inv_mem hx) y ih
      · have h := hleft (x * x)⁻¹ (B.inv_mem (hsquare x hx))
          (x * y) (hsimple x hx y ih)
        have heq : (x * x)⁻¹ * (x * y) = x⁻¹ * y := by group
        rwa [heq] at h

end Theory.AlgebraicGroup.BruhatGeneration
