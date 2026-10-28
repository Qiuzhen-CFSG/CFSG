module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.Defs

/-!
# Counting seed-type elements by quotient fibers

Quotient involution coverage divides the actual local centralizer into the
kernel branch and two quotient conjugacy classes. Lifting a quotient conjugator
injects every colored fiber into the corresponding distinguished fiber; the
kernel branch has at most 2048 elements. No centralization is inferred from
quotient membership, and every possible kernel lift remains counted.

This is a counting reduction for the Thompson argument in Aschbacher--Smith,
`refs/quasithin.pdf`, A.6, printed pp.64--65. Its numerical premises must be
proved separately before asserting the local involution bound.
-/

public section


namespace Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound
open Cardinality Simplicity.Max1Fusion
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localX localY
  localKernelSeed localKernel

private theorem card_le_mul_of_fibers {α β : Type*} [Finite α] [Finite β]
    (f : α → β) (n : ℕ) (h : ∀ b, Nat.card {a // f a = b} ≤ n) :
    Nat.card α ≤ Nat.card β * n := by
  classical
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  calc
    Nat.card α = ∑ b : β, Nat.card {a // f a = b} := by
      rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_eq_fintype_card,
        Fintype.card_sigma]
      simp only [Nat.card_eq_fintype_card]
    _ ≤ ∑ _b : β, n := Finset.sum_le_sum (fun b _ => h b)
    _ = Nat.card β * n := by simp [Nat.card_eq_fintype_card]

/-- Lifting a quotient conjugator injects any colored fiber into the
corresponding distinguished fiber. Every kernel lift is retained. -/
theorem coloredFiber_card_le (b : Bool) (q : Quotient hA hB)
    (hq : IsConj (projection hA hB (base hA hB b)) q) :
    Nat.card (ColoredFiber hA hB q) ≤ Nat.card (BaseFiber hA hB b) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hq.symm
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (localKernel hA hB) c
  let f : ColoredFiber hA hB q → BaseFiber hA hB b := fun w =>
    ⟨g * w.val * g⁻¹, w.property.1.trans
      ((max1Subgroup hA hB).subtype.map_isConj (isConj_iff.mpr ⟨g, rfl⟩)), by
        rw [map_mul, map_mul, map_inv, w.property.2]
        exact hc⟩
  apply Nat.card_le_card_of_injective f
  intro w v h
  apply Subtype.ext
  exact mul_left_cancel (mul_right_cancel (congrArg Subtype.val h))

private abbrev KernelPart :=
  {u : SeedType hA hB // projection hA hB (u.val : Local hA hB) = 1}

private abbrev ClassPart (b : Bool) :=
  {u : SeedType hA hB // IsConj (projection hA hB (base hA hB b))
    (projection hA hB (u.val : Local hA hB))}

private theorem kernelPart_card_le : Nat.card (KernelPart hA hB) ≤ 2048 := by
  let f : KernelPart hA hB → localKernel hA hB := fun u =>
    ⟨u.val.val.val, (QuotientGroup.eq_one_iff _).mp u.property⟩
  have hf : Function.Injective f := by
    intro u v h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun n : localKernel hA hB => n.val) h
  exact (Nat.card_le_card_of_injective f hf).trans_eq (localKernel_card hA hB)

private def classProjection (b : Bool) : ClassPart hA hB b → QuotientClass hA hB b :=
  fun u => ⟨projection hA hB (u.val.val : Local hA hB),
    ⟨⟨u.val.val.val, u.val.val.property, rfl⟩, u.property⟩⟩

private theorem classPart_card_le (b : Bool) :
    Nat.card (ClassPart hA hB b) ≤
      Nat.card (QuotientClass hA hB b) * Nat.card (BaseFiber hA hB b) := by
  apply card_le_mul_of_fibers (classProjection hA hB b)
  intro q
  let f : {u : ClassPart hA hB b // classProjection hA hB b u = q} →
      ColoredFiber hA hB q.val := fun u =>
    ⟨u.val.val.val.val, u.val.val.property, congrArg Subtype.val u.property⟩
  have hf : Function.Injective f := by
    intro u v h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun n : ColoredFiber hA hB q.val => n.val) h
  exact (Nat.card_le_card_of_injective f hf).trans
    (coloredFiber_card_le hA hB b q.val q.property.2)

private theorem seedType_coverage (u : SeedType hA hB) :
    projection hA hB (u.val : Local hA hB) = 1 ∨
    IsConj (projection hA hB (base hA hB false))
      (projection hA hB (u.val : Local hA hB)) ∨
    IsConj (projection hA hB (base hA hB true))
      (projection hA hB (u.val : Local hA hB)) := by
  classical
  by_cases h : projection hA hB (u.val : Local hA hB) = 1
  · exact Or.inl h
  have ho : orderOf (projection hA hB (u.val : Local hA hB)) = 2 := by
    apply orderOf_eq_prime _ h
    rw [← map_pow, ← colored_order hA hB (u.val : Local hA hB) u.property,
      pow_orderOf_eq_one, map_one]
  obtain ⟨g, hg | hg⟩ := quotient_involution_coverage hA hB _ ho
  · exact Or.inr (Or.inl ((isConj_iff.mpr ⟨g, hg.symm⟩).symm))
  · exact Or.inr (Or.inr ((isConj_iff.mpr ⟨g, hg.symm⟩).symm))

/-- Count the actual centralizer elements by kernel, then the two quotient
classes and their complete distinguished fibers. This is a reduction; its
numerical premises must be certified before asserting the requested bound. -/
theorem seedType_card_le_sum :
    Nat.card (SeedType hA hB) ≤ 2048 +
      Nat.card (QuotientClass hA hB false) * Nat.card (BaseFiber hA hB false) +
      Nat.card (QuotientClass hA hB true) * Nat.card (BaseFiber hA hB true) := by
  let f : KernelPart hA hB ⊕ (ClassPart hA hB false ⊕ ClassPart hA hB true) →
      SeedType hA hB := Sum.elim Subtype.val (Sum.elim Subtype.val Subtype.val)
  have hf : Function.Surjective f := by
    intro u
    rcases seedType_coverage hA hB u with h | h | h
    · exact ⟨Sum.inl ⟨u, h⟩, rfl⟩
    · exact ⟨Sum.inr (Sum.inl ⟨u, h⟩), rfl⟩
    · exact ⟨Sum.inr (Sum.inr ⟨u, h⟩), rfl⟩
  have h := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_sum, Nat.card_sum] at h
  have h0 := kernelPart_card_le hA hB
  have h1 := classPart_card_le hA hB false
  have h2 := classPart_card_le hA hB true
  omega

/-- The two independent finite counts suffice, with margin, for the requested
bound. This theorem does not assert its quotient or fiber premises. -/
theorem seedType_card_le_of_counts
    (hx : Nat.card (QuotientClass hA hB false) ≤ 1600)
    (hq : Nat.card (QuotientClass hA hB true) ≤ 1600)
    (hfx : Nat.card (BaseFiber hA hB false) ≤ 32)
    (hfq : Nat.card (BaseFiber hA hB true) ≤ 128) :
    Nat.card (SeedType hA hB) ≤ 262144 := by
  have h := seedType_card_le_sum hA hB
  have h1 := Nat.mul_le_mul hx hfx
  have h2 := Nat.mul_le_mul hq hfq
  omega

end Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound
