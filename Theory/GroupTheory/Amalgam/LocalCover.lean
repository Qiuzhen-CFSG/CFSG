module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.PGroup

/-!
# Local coverage and faithful overlap normalizers

If a subgroup covers both local groups modulo their common overlap, it covers
the whole generated group modulo that overlap. A word induction gives the
factorization. A subgroup of the overlap normalized by such a covering group
then lies in the ambient normal core of the overlap.

For finite cubic local groups, every subgroup of order three supplies the
required local coverage. This is the algebraic form of Goldschmidt's local
edge-transitivity argument, used in Sections 4--6 of *Automorphisms of
trivalent graphs* (1980), following (2.3), printed p.380.
-/

@[expose] public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- Local coset coverage at two generating subgroups yields global coset coverage. -/
theorem local_pair_factor (A B H : Subgroup G) (hgen : A ⊔ B = ⊤)
    (hA : ∀ a ∈ A, ∃ h ∈ H, ∃ t ∈ A ⊓ B, a = h * t)
    (hB : ∀ b ∈ B, ∃ h ∈ H, ∃ t ∈ A ⊓ B, b = h * t)
    (g : G) : ∃ h ∈ H, ∃ t ∈ A ⊓ B, g = h * t := by
  have hstep (x y : G) (hy : y ∈ (A : Set G) ∪ B)
      (hx : ∃ h ∈ H, ∃ t ∈ A ⊓ B, x = h * t) :
      ∃ h ∈ H, ∃ t ∈ A ⊓ B, x * y = h * t := by
    obtain ⟨h, hh, t, ht, rfl⟩ := hx
    have hty : ∃ h ∈ H, ∃ t' ∈ A ⊓ B, t * y = h * t' := by
      rcases hy with hy | hy
      · exact hA _ (A.mul_mem ht.1 hy)
      · exact hB _ (B.mul_mem ht.2 hy)
    obtain ⟨h', hh', t', ht', he⟩ := hty
    exact ⟨h * h', H.mul_mem hh hh', t', ht', by rw [mul_assoc, he, mul_assoc]⟩
  have hg : g ∈ closure ((A : Set G) ∪ B) := by
    rw [closure_union, closure_eq A, closure_eq B, hgen]
    trivial
  refine Subgroup.closure_induction_right (p := fun x _ => ∃ h ∈ H,
    ∃ t ∈ A ⊓ B, x = h * t) ⟨1, H.one_mem, 1, (A ⊓ B).one_mem, (mul_one _).symm⟩
    (fun x _ y hy hx => hstep x y hy hx) ?_ hg
  intro x _ y hy hx
  apply hstep x y⁻¹ _ hx
  rcases hy with hy | hy
  · exact Or.inl (A.inv_mem hy)
  · exact Or.inr (B.inv_mem hy)

/-- A locally transitive normalizer cannot normalize a nontrivial subgroup
of a faithful common overlap. -/
theorem local_pair_normalized_eq_bot (A B K H : Subgroup G)
    (hgen : A ⊔ B = ⊤) (hcore : (A ⊓ B).normalCore = ⊥)
    (hKT : K ≤ A ⊓ B) (hnorm : H ≤ normalizer (K : Set G))
    (hA : ∀ a ∈ A, ∃ h ∈ H, ∃ t ∈ A ⊓ B, a = h * t)
    (hB : ∀ b ∈ B, ∃ h ∈ H, ∃ t ∈ A ⊓ B, b = h * t) : K = ⊥ := by
  apply le_bot_iff.mp
  rw [← hcore, normalCore_eq_iInf_comap_conj]
  intro k hk
  simp only [mem_iInf, mem_comap]
  intro g
  obtain ⟨h, hh, t, ht, he⟩ := local_pair_factor A B H hgen hA hB g⁻¹
  have hg : g = t⁻¹ * h⁻¹ := by rw [← mul_inv_rev, ← he, inv_inv]
  rw [hg]
  change (t⁻¹ * h⁻¹) * k * (t⁻¹ * h⁻¹)⁻¹ ∈ A ⊓ B
  have hhkh : h⁻¹ * k * h ∈ K := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp (hnorm (H.inv_mem hh)) k).mp hk
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using
    (A ⊓ B).mul_mem ((A ⊓ B).mul_mem ((A ⊓ B).inv_mem ht) (hKT hhkh)) ht

/-- A subgroup of order three complements a two-group of index three. -/
theorem three_complement_of_two_group_index_three {G : Type*} [Group G] [Finite G]
    (P X : Subgroup G) (hP : IsPGroup 2 P) (hi : P.index = 3)
    (hX : Nat.card X = 3) : X.IsComplement' P := by
  apply isComplement'_of_coprime
  · rw [hX, ← hi]
    exact P.index_mul_card
  · rw [hX]
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
end Subgroup
