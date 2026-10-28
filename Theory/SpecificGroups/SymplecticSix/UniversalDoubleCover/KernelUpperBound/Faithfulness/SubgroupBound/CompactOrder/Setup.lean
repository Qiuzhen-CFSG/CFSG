module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.SubgroupBound.CompactData
public import Theory.GroupTheory.BinaryCollection

/-!
# A subgroup of order at most eight in the compact presentation

The literal relators make compact generators 1, 2 and 4 commuting involutions.
Binary collection therefore bounds their subgroup by eight elements. This is
the finite subgroup used by the independent 5040-representative coset cover.

Source: the 51 relators in `../CompactData.lean`, extracted from ATLAS S62G1-P1.
-/

@[expose] public section
open Subgroup.CosetWordCertificate
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound.CompactOrder

def generator : Fin 8 → CompactPresentation := PresentedGroup.of

theorem generator_relators (r : Fin 51) : eval generator (compactRelator r) = 1 := by
  have hm : FreeGroup.lift generator =
      PresentedGroup.mk (Set.range (fun i => FreeGroup.mk (compactRelator i))) := by
    apply FreeGroup.ext_hom
    intro i
    exact FreeGroup.lift_apply_of
  rw [eval, hm]
  exact PresentedGroup.one_of_mem (Set.mem_range_self r)

def smallGenerators : List CompactPresentation := [generator 1, generator 2, generator 4]
def smallSubgroup : Subgroup CompactPresentation := Subgroup.closure {x | x ∈ smallGenerators}

theorem involutions : ∀ i ∈ ([1, 2, 4] : List (Fin 8)), generator i * generator i = 1 := by
  intro i hi
  have h1 := generator_relators 3
  have h2 := generator_relators 2
  have h4 := generator_relators 1
  simp [compactRelator, eval_cons] at h1 h2 h4
  have h (x : CompactPresentation) (hx : x⁻¹ * x⁻¹ = 1) : x * x = 1 := by
    simpa only [mul_inv_rev, inv_inv, inv_one] using congrArg Inv.inv hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact h _ h1
  · exact h _ h2
  · exact h _ h4

theorem generator_inverse (i : Fin 8) (hi : i ∈ ([1, 2, 4] : List (Fin 8))) :
    (generator i)⁻¹ = generator i := inv_eq_of_mul_eq_one_left (involutions i hi)

theorem commuting : Commute (generator 1) (generator 2) ∧
    Commute (generator 1) (generator 4) ∧ Commute (generator 2) (generator 4) := by
  have h12 := generator_relators 8
  have h14 := generator_relators 7
  have h24 := generator_relators 6
  have hi1 := generator_inverse 1 (by simp)
  have hi2 := generator_inverse 2 (by simp)
  have hi4 := generator_inverse 4 (by simp)
  simp [compactRelator, eval_cons, hi1, hi2, hi4] at h12 h14 h24
  have h (x y : CompactPresentation) (hx : x⁻¹ = x) (hy : y⁻¹ = y)
      (hxy : y * (x * (y * x)) = 1) : Commute x y := by
    have he : y * x = (y * x)⁻¹ := eq_inv_of_mul_eq_one_left (by simpa [mul_assoc] using hxy)
    simpa only [mul_inv_rev, hx, hy, Commute, SemiconjBy] using he.symm
  exact ⟨h _ _ hi1 hi2 h12, h _ _ hi1 hi4 h14, h _ _ hi2 hi4 h24⟩

theorem small_triangular : Theory.GroupTheory.BinaryCollection.triangular smallGenerators := by
  obtain ⟨h12, h14, h24⟩ := commuting
  have hs1 := involutions 1 (by simp)
  have hs2 := involutions 2 (by simp)
  have hs4 := involutions 4 (by simp)
  have conjugate (a b : CompactPresentation) (h : Commute a b) : a⁻¹ * b * a = b := by
    rw [mul_assoc, ← h.eq, inv_mul_cancel_left]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · rw [hs1]; exact Subgroup.one_mem _
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · rw [conjugate _ _ h12]; exact Subgroup.subset_closure (by simp)
    · rw [conjugate _ _ h14]; exact Subgroup.subset_closure (by simp)
  · rw [hs2]; exact Subgroup.one_mem _
  · intro b hb
    have he : b = generator 4 := by simpa using hb
    rw [he, conjugate _ _ h24]; exact Subgroup.subset_closure (by simp)
  · rw [hs4]; exact Subgroup.one_mem _
  · simp

theorem small_bound : Finite smallSubgroup ∧ Nat.card smallSubgroup ≤ 8 := by
  have mem_product (l : List CompactPresentation) (n : Nat) :
      Theory.GroupTheory.BinaryCollection.product l n ∈ Subgroup.closure {x | x ∈ l} := by
    induction l generalizing n with
    | nil => simp [Theory.GroupTheory.BinaryCollection.product]
    | cons a l ih =>
      apply Subgroup.mul_mem
      · exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
      · exact (Subgroup.closure_mono (by intro x hx; exact List.mem_cons_of_mem a hx)) (ih _)
  let f : Fin 8 → smallSubgroup := fun n =>
    ⟨Theory.GroupTheory.BinaryCollection.product smallGenerators n.val, mem_product _ _⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨n, hn, he⟩ := Theory.GroupTheory.BinaryCollection.cover smallGenerators small_triangular x.val x.property
    refine ⟨⟨n, hn⟩, ?_⟩
    exact Subtype.ext he
  exact ⟨Finite.of_surjective f hf, by simpa using Nat.card_le_card_of_surjective f hf⟩

/-- Only the three chosen positive letters are subgroup-loop axioms. -/
def allowed (a : Letter (Fin 8)) : Bool :=
  a.2 && (a.1 == 1 || a.1 == 2 || a.1 == 4)

theorem allowed_mem (a : Letter (Fin 8)) (ha : allowed a = true) :
    eval generator [a] ∈ smallSubgroup := by
  have h : a.2 = true ∧ (a.1 = 1 ∨ a.1 = 2 ∨ a.1 = 4) := by
    simpa [allowed, or_assoc] using ha
  rw [eval_letter, if_pos h.1]
  apply Subgroup.subset_closure
  rcases h.2 with he | he | he <;> simp [smallGenerators, he]

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound.CompactOrder
