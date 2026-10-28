module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactData
public import Theory.GroupTheory.BinaryCollection

/-!
# A four-element upper bound for the subgroup used in the coset certificate

Relators 0, 6 and 14 make compact generators 3 and 9 commuting involutions.
Binary collection bounds their subgroup by four, without any model identification.
The numbering here is zero-based. The literal relators and their provenance are
frozen in `../CompactData.lean` and `../source/README.md`.
-/

@[expose] public section
namespace Rudvalis.Multiplier.TwoPrimary.LocalPresentation.PresentationFaithfulness.CompactOrder
open Subgroup.CosetWordCertificate

def generator : Fin 11 → CompactPresentation := PresentedGroup.of

theorem generator_relators (r : Fin 159) : eval generator (compactRelator r) = 1 := by
  have hm : FreeGroup.lift generator =
      PresentedGroup.mk (Set.range (fun i => FreeGroup.mk (compactRelator i))) := by
    apply FreeGroup.ext_hom
    intro i
    exact FreeGroup.lift_apply_of
  rw [eval, hm]
  exact PresentedGroup.one_of_mem (Set.mem_range_self r)

def smallGenerators : List CompactPresentation := [generator 3, generator 9]
def smallSubgroup : Subgroup CompactPresentation := Subgroup.closure {x | x ∈ smallGenerators}

theorem involutions : ∀ i ∈ ([3, 9] : List (Fin 11)), generator i * generator i = 1 := by
  intro i hi
  have h3 := generator_relators 6
  have h9 := generator_relators 0
  simp [compactRelator, eval_cons] at h3 h9
  have h (x : CompactPresentation) (hx : x⁻¹ * x⁻¹ = 1) : x * x = 1 := by
    simpa only [mul_inv_rev, inv_inv, inv_one] using congrArg Inv.inv hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact h _ h3
  · exact h _ h9

theorem generator_inverse (i : Fin 11) (hi : i ∈ ([3, 9] : List (Fin 11))) :
    (generator i)⁻¹ = generator i := inv_eq_of_mul_eq_one_left (involutions i hi)

theorem commuting : Commute (generator 3) (generator 9) := by
  have h := generator_relators 14
  have hi3 := generator_inverse 3 (by simp)
  have hi9 := generator_inverse 9 (by simp)
  simp [compactRelator, eval_cons, hi3, hi9] at h
  have he : generator 9 * generator 3 = (generator 9 * generator 3)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa [mul_assoc] using h)
  simpa only [mul_inv_rev, hi3, hi9, Commute, SemiconjBy] using he.symm

theorem small_triangular : Theory.GroupTheory.BinaryCollection.triangular smallGenerators := by
  have hs3 := involutions 3 (by simp)
  have hs9 := involutions 9 (by simp)
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · rw [hs3]; exact Subgroup.one_mem _
  · intro b hb
    have he : b = generator 9 := by simpa using hb
    rw [he, mul_assoc, ← commuting.eq, inv_mul_cancel_left]
    exact Subgroup.subset_closure (by simp)
  · rw [hs9]; exact Subgroup.one_mem _
  · simp

theorem small_bound : Finite smallSubgroup ∧ Nat.card smallSubgroup ≤ 4 := by
  have mem_product (l : List CompactPresentation) (n : Nat) :
      Theory.GroupTheory.BinaryCollection.product l n ∈ Subgroup.closure {x | x ∈ l} := by
    induction l generalizing n with
    | nil => simp [Theory.GroupTheory.BinaryCollection.product]
    | cons a l ih =>
      apply Subgroup.mul_mem
      · exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
      · exact (Subgroup.closure_mono (by intro x hx; exact List.mem_cons_of_mem a hx)) (ih _)
  let f : Fin 4 → smallSubgroup := fun n =>
    ⟨Theory.GroupTheory.BinaryCollection.product smallGenerators n.val, mem_product _ _⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨n, hn, he⟩ :=
      Theory.GroupTheory.BinaryCollection.cover smallGenerators small_triangular x.val x.property
    refine ⟨⟨n, hn⟩, ?_⟩
    exact Subtype.ext he
  exact ⟨Finite.of_surjective f hf, by simpa using Nat.card_le_card_of_surjective f hf⟩

/-- Only the two chosen positive letters are subgroup-loop axioms. -/
def allowed (a : Letter (Fin 11)) : Bool := a.2 && (a.1 == 3 || a.1 == 9)

theorem allowed_mem (a : Letter (Fin 11)) (ha : allowed a = true) :
    eval generator [a] ∈ smallSubgroup := by
  have h : a.2 = true ∧ (a.1 = 3 ∨ a.1 = 9) := by simpa [allowed] using ha
  rw [eval_letter, if_pos h.1]
  apply Subgroup.subset_closure
  rcases h.2 with he | he <;> simp [smallGenerators, he]

end Rudvalis.Multiplier.TwoPrimary.LocalPresentation.PresentationFaithfulness.CompactOrder
