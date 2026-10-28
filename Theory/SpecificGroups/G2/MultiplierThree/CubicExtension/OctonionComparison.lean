module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.Relations
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.Generation
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound
public import Theory.AtlasPort.LinearGroups.G2.OrderChecks

/-!
# Comparing the six-relator presentation with octonion G₂(3)

The fixed root/Weyl pair satisfies all six literal ATLAS relations, so it
defines a homomorphism from `Presentation.Presented` into the genuine
split-octonion automorphism group. Its image is exactly the subgroup generated
by that marked pair. The checked generation certificate and finite presentation
bound therefore make this homomorphism an equivalence, using the already
proved octonion order 4245696. The conditional construction is retained as the
comparison interface used by the final assembly.

Source: the six ATLAS relations retained in `CubicExtension/Presentation.lean`.
The marked octonion pair and checked matrix relations are in the descendants
of this module. No central-extension or multiplier module is imported here.
-/

@[expose] public section

namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison

/-- Evaluation at the marked pair of actual octonion automorphisms. -/
def octonionHom : Presentation.Presented →* Model (ZMod 3) :=
  Presentation.hom (generator false) (generator true) generator_relations

@[simp] theorem octonionHom_generator (b : Bool) :
    octonionHom (Presentation.generator b) = generator b := by
  rw [octonionHom, Presentation.hom_generator]
  cases b <;> rfl

/-- The literal free quotient map has the expected generator marking. -/
theorem octonionHom_toPresented : octonionHom.comp Presentation.toPresented =
    FreeGroup.lift generator := by
  apply FreeGroup.ext_hom
  intro b
  exact octonionHom_generator b

theorem octonionHom_range :
    octonionHom.range = Subgroup.closure (Set.range generator) := by
  rw [MonoidHom.range_eq_map,
    ← PresentedGroup.closure_range_of (Set.range Presentation.relator),
    MonoidHom.map_closure, ← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext b
  exact octonionHom_generator b

theorem octonionHom_surjective_of_generation
    (hgen : Subgroup.closure (Set.range generator) = ⊤) :
    Function.Surjective octonionHom :=
  MonoidHom.range_eq_top.mp (octonionHom_range.trans hgen)

/-- The two independent certificates imply faithfulness of the marked map. -/
theorem octonionHom_bijective_of_generation_of_bound
    (hgen : Subgroup.closure (Set.range generator) = ⊤)
    (hbound : Finite Presentation.Presented ∧ Nat.card Presentation.Presented ≤ 4245696) :
    Function.Bijective octonionHom := by
  let := hbound.1
  exact (octonionHom_surjective_of_generation hgen).bijective_of_nat_card_le
    (OrderChecks.ternary_order ▸ hbound.2)

/-- Conditional assembly; the generation and finite bound still require proofs. -/
noncomputable def equivOfGenerationOfBound
    (hgen : Subgroup.closure (Set.range generator) = ⊤)
    (hbound : Finite Presentation.Presented ∧ Nat.card Presentation.Presented ≤ 4245696) :
    Presentation.Presented ≃* Model (ZMod 3) :=
  MulEquiv.ofBijective octonionHom
    (octonionHom_bijective_of_generation_of_bound hgen hbound)

@[simp] theorem equivOfGenerationOfBound_generator
    (hgen : Subgroup.closure (Set.range generator) = ⊤)
    (hbound : Finite Presentation.Presented ∧ Nat.card Presentation.Presented ≤ 4245696)
    (b : Bool) :
    equivOfGenerationOfBound hgen hbound (Presentation.generator b) = generator b :=
  octonionHom_generator b

/-! The certified generation and presentation bound discharge the two inputs
to the comparison construction above. -/

/-- The literal six-relator presentation is the actual split-octonion group
`G₂(3)`. -/
public noncomputable def presentationEquivModel :
    Presentation.Presented ≃* Model (ZMod 3) :=
  equivOfGenerationOfBound closure_generator_range
    PresentationBound.finite_card_presented_le

@[simp] public theorem presentationEquivModel_generator (b : Bool) :
    presentationEquivModel (Presentation.generator b) = generator b :=
  equivOfGenerationOfBound_generator closure_generator_range
    PresentationBound.finite_card_presented_le b

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison
