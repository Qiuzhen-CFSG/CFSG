module
public import Theory.GroupTheory.GroupSection
public import Mathlib.GroupTheory.Index

/-!
# Incidence of nested isomorphic finite sections

For two sections of a finite group, suppose the first numerator lies in the
second, their quotient groups are isomorphic, and the second denominator
intersects the first numerator inside the first denominator. Then the two
sections are incident, in the ordered-product sense of `GroupSection`.

The quotient of the first numerator by its intersection with the second
kernel embeds naturally in the second section and surjects onto the first.
The given quotient isomorphism makes their finite orders equal, so both maps
are bijective. Injectivity of the surjection gives equality of the kernels;
surjectivity of the embedding supplies the required product covering.
No arbitrary isomorphism is assumed to agree with either natural map.

This is Alperin--Brauer--Gorenstein II.8 Lemma 6, article p65 / PDF66,
`refs/latex/alperin-brauer-gorenstein-pages/page-066.tex`. The finite counting
argument makes explicit the order comparison in the paper's Zassenhaus proof.
-/

namespace GroupSection

public theorem incident_of_isomorphic_of_le {G : Type*} [Group G] [Finite G]
    (first second : GroupSection G)
    (nested : first.numerator ≤ second.numerator)
    (isomorphic : Nonempty ((first.numerator ⧸ first.denominator.subgroupOf first.numerator) ≃*
      (second.numerator ⧸ second.denominator.subgroupOf second.numerator)))
    (kernel_le : second.denominator ⊓ first.numerator ≤ first.denominator) :
    first.Incident second := by
  let D := second.denominator.subgroupOf first.numerator
  let C := first.denominator.subgroupOf first.numerator
  have hDC : D ≤ C := fun x hx => kernel_le ⟨hx, x.property⟩
  let projection : (first.numerator ⧸ D) → (first.numerator ⧸ C) :=
    Quotient.map' id (fun _ _ h => QuotientGroup.leftRel_apply.mpr
      (hDC (QuotientGroup.leftRel_apply.mp h)))
  have projection_surj : Function.Surjective projection := by
    intro y
    obtain ⟨x, rfl⟩ := Quotient.exists_rep y
    exact ⟨QuotientGroup.mk x, rfl⟩
  let embedding := Subgroup.quotientSubgroupOfEmbeddingOfLE second.denominator nested
  obtain ⟨e⟩ := isomorphic
  have card_eq := Nat.card_congr e.toEquiv
  have projection_inj : Function.Injective projection :=
    (projection_surj.bijective_of_nat_card_le (by
      rw [card_eq]
      exact Nat.card_le_card_of_injective embedding embedding.injective)).1
  have embedding_surj : Function.Surjective embedding :=
    (embedding.injective.bijective_of_nat_card_le (by
      rw [← card_eq]
      exact Nat.card_le_card_of_surjective projection projection_surj)).2
  have kernel_eq : first.denominator = first.numerator ⊓ second.denominator := by
    apply le_antisymm
    · intro x hx
      refine ⟨first.denominator_le hx, ?_⟩
      let y : first.numerator := ⟨x, first.denominator_le hx⟩
      have hproj : projection (QuotientGroup.mk y) = projection (QuotientGroup.mk 1) := by
        apply QuotientGroup.eq.mpr
        change x⁻¹ * 1 ∈ first.denominator
        simpa using first.denominator.inv_mem hx
      have hrel := QuotientGroup.eq.mp (projection_inj hproj)
      change x⁻¹ * 1 ∈ second.denominator at hrel
      simpa using second.denominator.inv_mem hrel
    · intro x hx
      exact kernel_le ⟨hx.2, hx.1⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact ⟨x, nested hx, 1, first.denominator.one_mem, mul_one x⟩
  · intro x hx
    obtain ⟨z, hz⟩ := embedding_surj (QuotientGroup.mk (⟨x, hx⟩ : second.numerator))
    obtain ⟨y, rfl⟩ := Quotient.exists_rep z
    have hrel := QuotientGroup.eq.mp hz
    exact ⟨y.val, y.property, y.val⁻¹ * x, hrel, mul_inv_cancel_left _ _⟩
  · rw [inf_eq_left.mpr (first.denominator_le.trans nested), kernel_eq]

end GroupSection
