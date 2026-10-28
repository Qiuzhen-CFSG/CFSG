module

public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard
public import Theory.SpecificGroups.HaradaNorton.Order.LocalIndex.ColumnAction

/-!
# A proper alternating subgroup in the concrete Harada--Norton group

The checked Suzuki presentation identifies the ATLAS word subgroup with A₁₂.
Its invariant column is moved by the ambient generator b at coordinate 1,
proving properness without an ambient order or simplicity assumption.

Source: ATLAS HNG1-max1W1 and HNG1-f5r133B0, retained by the imported
construction modules; GLS3 Table 5.3w. This is the F₅ subgroup used in
Aschbacher--Smith, Lemma A.2.19, printed p. 41.
-/

public section
namespace HaradaNorton.OrderCertificate
open Matrix

private theorem b_moves_a12_fixed_column :
    matrixHom b *ᵥ indexBaseVector ≠ indexBaseVector := by
  intro h
  have h1 := congrFun h 1
  rw [matrixHom_b] at h1
  have hne : (bMatrix *ᵥ indexBaseVector) 1 ≠ indexBaseVector 1 := by
    decide +kernel
  exact hne h1

/-- The certified A₁₂ word subgroup is proper in the fixed HN matrix carrier. -/
theorem alternatingTwelveSubgroup_ne_top : localSubgroup ≠ ⊤ := by
  intro h
  exact b_moves_a12_fixed_column
    (localSubgroup_fixes_indexBaseVector b (h ▸ Subgroup.mem_top b))


/-- The explicit A₁₂ embedding obtained from the checked presentation. -/
noncomputable def alternatingTwelveEmbedding : alternatingGroup (Fin 12) →* HN :=
  localSubgroup.subtype.comp localSubgroupEquiv.symm.toMonoidHom

/-- The presentation identification makes this homomorphism injective. -/
theorem alternatingTwelveEmbedding_injective :
    Function.Injective alternatingTwelveEmbedding :=
  localSubgroup.subtype_injective.comp localSubgroupEquiv.symm.injective

/-- The image is proper, witnessed by an element moving its fixed column. -/
theorem alternatingTwelveEmbedding_range_ne_top :
    alternatingTwelveEmbedding.range ≠ ⊤ := by
  intro h
  have hs := MonoidHom.range_eq_top.mp h
  obtain ⟨x, hx⟩ := hs b
  have hb : b ∈ localSubgroup := hx ▸ (localSubgroupEquiv.symm x).property
  exact b_moves_a12_fixed_column (localSubgroup_fixes_indexBaseVector b hb)

end HaradaNorton.OrderCertificate
