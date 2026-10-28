module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.Normalizer
public import Theory.GroupTheory.PRadical.NormalizerRestriction
public import Theory.GroupTheory.MaximalTwoLocalElementary

/-!
# The native Mathieu kernel as an ambient radical

The ambient centralizer and normalizer calculations identify the full normalizer
of the embedded binary kernel `E` with the literal max1 subgroup. This proves
that max1 is a two-local and that `E` is radical, including the literal local
normalizer and core identities.

These are the kernel endpoint facts for the Mathieu local in Kleidman--Wilson,
*The Maximal Subgroups of J4* (1988), Section 1.1. The observation about elementary
subgroups containing `E` concerns only `E` itself. Proposition 2.2.3 concerns
subgroups contained in `E` and requires a separate uniqueness argument.
-/

public section
open Subgroup
namespace Janko4.LocalStructure.ElementaryNormalizerCover

attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

abbrev max1 : Subgroup Janko4.Model :=
  Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four
abbrev kernel : Subgroup max1 :=
  Janko4.Cardinality.localKernel Janko4.matrixA_mul_self Janko4.matrixB_pow_four
abbrev embeddedKernel : Subgroup Janko4.Model := kernel.map max1.subtype

/-- The literal max1 subgroup is the full ambient normalizer of its kernel. -/
theorem embedded_localKernel_normalizer_eq_max1 :
    normalizer (embeddedKernel : Set Janko4.Model) = max1 := by
  apply le_antisymm
  · exact Janko4.LocalStructure.normalizer_embedded_localKernel_le_max1
  · change max1 ≤ normalizer ((kernel.map max1.subtype : Subgroup Janko4.Model) : Set Janko4.Model)
    have hk : kernel = pCore 2 max1 :=
      Janko4.LocalStructure.localKernel_eq_twoCore _ _
    rw [hk]
    exact max1.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image max1 (pCore 2 max1))

/-- The embedded kernel is an actual two-local, witnessed by itself. -/
theorem embedded_localKernel_isTwoLocal : IsTwoLocal max1 := by
  refine ⟨embeddedKernel, ?_, ?_, embedded_localKernel_normalizer_eq_max1.symm⟩
  · intro h
    have h0 : kernel = ⊥ := by
      apply Subgroup.map_injective max1.subtype_injective
      simpa only [Subgroup.map_bot] using h
    exact Janko4.LocalStructure.localKernel_ne_bot _ _ h0
  · exact IsPGroup.of_card (n := 11) (by
      rw [card_map_of_injective max1.subtype_injective,
        Janko4.Cardinality.localKernel_card]
      norm_num)

/-- An elementary subgroup containing the native binary kernel is exactly it.

The containment in the centralizer follows because every element of an
elementary subgroup commutes with the containing subgroup; self-centrality of
`E` then gives the reverse inclusion.
-/
theorem elementary_eq_embedded_localKernel_of_le
    (X : Subgroup Janko4.Model) [IsElementaryAbelian 2 X]
    (hXE : embeddedKernel ≤ X) : X = embeddedKernel := by
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ centralizer (embeddedKernel : Set Janko4.Model) := by
      intro e he
      exact (X.le_centralizer (hXE he) x hx).symm
    rw [Janko4.LocalStructure.centralizer_embedded_localKernel] at hx'
    exact hx'
  · exact hXE

/-- The full normalizer of an elementary overgroup of the kernel is max1. -/
theorem elementary_normalizer_le_max1_of_le_embedded_localKernel
    (X : Subgroup Janko4.Model) [IsElementaryAbelian 2 X]
    (hXE : embeddedKernel ≤ X) :
    normalizer (X : Set Janko4.Model) ≤ max1 := by
  rw [elementary_eq_embedded_localKernel_of_le X hXE]
  exact embedded_localKernel_normalizer_eq_max1.le

/-- The native kernel is radical in the ambient J₄ model. -/
theorem embedded_localKernel_isPRadical : embeddedKernel.IsPRadical 2 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h0 : kernel = ⊥ := by
      apply Subgroup.map_injective max1.subtype_injective
      simpa only [Subgroup.map_bot] using h
    exact Janko4.LocalStructure.localKernel_ne_bot _ _ h0
  · rw [embedded_localKernel_normalizer_eq_max1]
    rw [← Janko4.LocalStructure.localKernel_eq_twoCore]

/-- The literal restriction data used by the radical consumers. -/
theorem embedded_localKernel_local_consumer :
    embeddedKernel ≤ max1 ∧
      (normalizer (embeddedKernel.subgroupOf max1 : Set max1)).map max1.subtype =
        normalizer (embeddedKernel : Set Janko4.Model) ∧
      (embeddedKernel.subgroupOf max1).IsPRadical 2 ∧
      (normalizer (embeddedKernel.subgroupOf max1 : Set max1)).pCoreIn 2 =
        embeddedKernel.subgroupOf max1 ∧
      ((normalizer (embeddedKernel.subgroupOf max1 : Set max1)).pCoreIn 2).map
          max1.subtype = embeddedKernel := by
  have hPM : embeddedKernel ≤ max1 := map_subtype_le _
  have hNM : normalizer (embeddedKernel : Set Janko4.Model) ≤
      normalizer (max1 : Set Janko4.Model) := by
    rw [embedded_localKernel_normalizer_eq_max1]
    exact max1.le_normalizer
  have hNPM : normalizer (embeddedKernel : Set Janko4.Model) ≤ max1 := by
    rw [embedded_localKernel_normalizer_eq_max1]
  have hrad := Subgroup.IsPRadical.subgroupOf_of_normalizer_normalizes
    embedded_localKernel_isPRadical max1 hPM hNM
  have hcore := Subgroup.IsPRadical.normalizer_core_subgroupOf
    embedded_localKernel_isPRadical max1 hPM hNM
  refine ⟨hPM, ?_, hrad, hcore, ?_⟩
  · rw [← subgroupOf_normalizer_eq hPM, map_subgroupOf_eq_of_le hNPM]
  · rw [hcore, map_subgroupOf_eq_of_le hPM]

end Janko4.LocalStructure.ElementaryNormalizerCover
