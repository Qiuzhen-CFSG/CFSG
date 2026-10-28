module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Products.Placement
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order

/-!
# The selected binary component row, with its original quotient maps

The order of the actual component forces the coefficient field in any SL₃
row to have degree one: otherwise the unitriangular subgroup has order
divisible by 64, whereas the component has order 168. The established field
transport then uses one actor isomorphism and one linear intertwiner on the
natural module or both repeated copies.

Combining this comparison with component placement orients the original
internal product with C first, retains the other factor and both literal
quotient images, and exhausts the selected factor's source constructors.
The doubled row is still an assertion on the quotient image. Recovering its
whole moved space is a separate splitting obligation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.6(3),
printed p.105, and the module alternatives in 13.6.20, printed p.931.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Products
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction

variable {D : Type*} [Group D] {C : Subgroup D}

/-- A field of degree at least two would give a 64-divisor of 168. -/
theorem component_field_degree (e : C ≃* Matrix.PSL3Two.PSL) (F : BinaryField)
    (a : C ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) : F.degree = 1 := by
  have hd := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.card_unipotentSL, F.card_eq, ← pow_mul,
    ← Nat.card_congr a.toEquiv, Nat.card_congr e.toEquiv, Matrix.PSL3Two.card_PSL] at hd
  have hp := F.degree_pos
  by_contra hn
  have hlarge : 6 ≤ F.degree * 3 := by omega
  have h64 : 64 ∣ 168 := (Nat.pow_dvd_pow 2 hlarge).trans hd
  norm_num at h64

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

/-- The exhaustive binary rows on the image modulo C_V(D). None asserts
that the quotient map is injective on the original moved space. -/
inductive ComponentFactorCase (C : Subgroup D) (U : Subrepresentation ρ) : Prop
  | natural (moved_eq : U.toSubmodule = moved ρ C)
      (coordinates : ActionEquiv
        (((fixed ρ).quotientImage U).toRepresentation.comp C.subtype) BinaryLinearThree.W)
  | doubled (moved_eq : U.toSubmodule = moved ρ C)
      (coordinates : ActionEquiv
        (((fixed ρ).quotientImage U).toRepresentation.comp C.subtype)
        (repeated BinaryLinearThree.W 2))
  | exceptional (moved_le : moved ρ C ≤ U.toSubmodule)
      (extension : FourDimensionalSource
        (((fixed ρ).quotientImage U).toRepresentation.comp C.subtype))

variable {ρ}

/-- Compare all natural actors and transport the surviving field and action. -/
theorem natural_factor_coordinates (e : C ≃* Matrix.PSL3Two.PSL)
    {U : Subrepresentation ρ}
    (h : FactorNatural (((fixed ρ).quotientImage U).toRepresentation.comp C.subtype)) :
    Nonempty (ActionEquiv
      (((fixed ρ).quotientImage U).toRepresentation.comp C.subtype) BinaryLinearThree.W) := by
  cases h with
  | linearTwo F hn =>
      obtain ⟨a⟩ := hn
      exact (no_linearTwo_factor e le_rfl F a.groupEquiv).elim
  | symmetricFive hn =>
      obtain ⟨a⟩ := hn
      exact (no_symmetricFive_factor e le_rfl a.groupEquiv).elim
  | linearThree F _ hn =>
      obtain ⟨a⟩ := hn
      let b := ExtensionConsequences.degreeOneNaturalEquiv F
        (component_field_degree e F a.groupEquiv) 3
      refine ⟨⟨a.groupEquiv.trans b.groupEquiv, a.linearEquiv.trans b.linearEquiv, ?_⟩⟩
      intro g v
      exact (congrArg b.linearEquiv (a.intertwines g v)).trans (b.intertwines _ _)

/-- The original source factor yields exactly one of the three binary rows. -/
theorem component_factor_rows (e : C ≃* Matrix.PSL3Two.PSL)
    {U : Subrepresentation ρ} (h : SourceFactorCase ρ C U) : ComponentFactorCase ρ C U := by
  cases h with
  | natural hm hn =>
      obtain ⟨a⟩ := natural_factor_coordinates e hn
      exact .natural hm a
  | doubleNatural F _ hm hn =>
      obtain ⟨a⟩ := hn
      let b := ExtensionConsequences.degreeOneRepeatedEquiv F
        (component_field_degree e F a.groupEquiv) 3 2
      refine .doubled hm ⟨a.groupEquiv.trans b.groupEquiv,
        a.linearEquiv.trans b.linearEquiv, ?_⟩
      intro g v
      exact (congrArg b.linearEquiv (a.intertwines g v)).trans (b.intertwines _ _)
  | exceptional hm he => exact .exceptional hm he

/-- The product is oriented using the actual component, with the original
complement, subspaces, quotient images, and full opposite-factor source row. -/
structure SelectedTwoFactorCase (ρ : Representation (ZMod 2) D V) (C : Subgroup D) where
  other : Subgroup D
  product : InternalProduct C other
  space : Subrepresentation ρ
  otherSpace : Subrepresentation ρ
  decomposition : IsCompl ((fixed ρ).quotientImage space).toSubmodule
    ((fixed ρ).quotientImage otherSpace).toSubmodule
  componentCase : ComponentFactorCase ρ C space
  otherCase : SourceFactorCase ρ other otherSpace

/-- Selection is proved from the full source product; it is not a premise of
the component classifier. Swapping retains the multiplication inclusion law. -/
theorem select_twoFactor [C.Normal] (e : C ≃* Matrix.PSL3Two.PSL)
    (c : SourceTwoFactorCase ρ) : Nonempty (SelectedTwoFactorCase ρ C) := by
  rcases twoFactor_component_eq e c with h | h
  · subst C
    exact ⟨⟨c.second, c.product, c.firstSpace, c.secondSpace, c.decomposition,
      component_factor_rows e c.firstCase, c.secondCase⟩⟩
  · subst C
    exact ⟨⟨c.first, swapProduct c.product, c.secondSpace, c.firstSpace,
      c.decomposition.symm, component_factor_rows e c.secondCase, c.firstCase⟩⟩

/-- The binary normalization retains the full source factor contract. -/
theorem ComponentFactorCase.toSource {U : Subrepresentation ρ}
    (h : ComponentFactorCase ρ C U) : SourceFactorCase ρ C U := by
  cases h with
  | natural hm e => exact .natural hm (.linearThree BinaryField.two (by decide) ⟨e⟩)
  | doubled hm e => exact .doubleNatural BinaryField.two (by decide) hm ⟨e⟩
  | exceptional hm e => exact .exceptional hm e

/-- Reassemble B.5.6(3) with the same maps, now with its actual C-factor first. -/
def SelectedTwoFactorCase.toSource (c : SelectedTwoFactorCase ρ C) : SourceTwoFactorCase ρ where
  first := C
  second := c.other
  product := c.product
  firstSpace := c.space
  secondSpace := c.otherSpace
  decomposition := c.decomposition
  firstCase := by exact c.componentCase.toSource
  secondCase := c.otherCase

universe u w

/-- Exactly the universal row extraction supplied by the independent
quasisimple-row owner. Its source conclusion retains all six B.5.1 clauses;
no local classified-module witness or restriction hypothesis is substituted. -/
def QuasisimpleRowExtraction : Prop :=
  ∀ (E : Type u) [Group E] [Finite E]
    (W : Type w) [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (σ : Representation (ZMod 2) E W) (L : Subgroup E) [L.Normal],
    (L ≃* Matrix.PSL3Two.PSL) →
    ProjectiveLine.QuasisimpleSourceConclusion σ L → LinearThreeModuleCase σ L

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Products
