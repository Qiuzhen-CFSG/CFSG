module

public import Theory.SpecificGroups.Tits.R1CosetCover
public import Theory.SpecificGroups.Tits.R1DihedralBound
public import Theory.SpecificGroups.Tits.ReeLocalBlockOrders

/-!
# Recognition by the local Tits presentation

Parrott's nine-generator presentation is exactly the whole first parabolic.
Its certified coset bound gives order at most 10240, and its surjection to the
concrete first parabolic gives the opposite bound. The resulting equivalence
preserves all nine generators. Consequently a generating tuple satisfying
the 28 local relations identifies any group of order at least 10240 with
this parabolic. In particular this reconstructs the extension, including
its multiplication, rather than identifying only its core quotient.

Source: Parrott, “A Characterization of the Tits' Simple Group” (1972),
§5, p.683. The local presentation and its certified bound are documented in
`R1Presentation` and `R1CosetCover`.
-/

public noncomputable section
namespace Tits.FirstParabolicPresentation
open Subgroup

/-- The certified local presentation has at most 10240 elements. -/
theorem finite_card_le : Finite ParrottR1Group ∧ Nat.card ParrottR1Group ≤ 10240 := by
  obtain ⟨hfinite, hcard⟩ := parrottR1DihedralSubgroup_finite_card_le
  let := hfinite
  obtain ⟨hlocal, hbound⟩ := parrottR1CosetCover.finite_card_le
    parrottR1_closure_range_generator
  exact ⟨hlocal, hbound.trans (by simpa using Nat.mul_le_mul_right 1024 hcard)⟩

private def subgroupEquiv : ParrottR1Group ≃* parrottR1Subgroup := by
  let := finite_card_le.1
  exact MulEquiv.ofBijective parrottR1ToSubgroup
    (parrottR1ToSubgroup_surjective.bijective_of_nat_card_le
      (by rw [ReeLocalBlockOrders.r1_card]; exact finite_card_le.2))

/-- The whole local presentation is the actual first parabolic. -/
def modelEquiv : ParrottR1Group ≃* ExceptionalParabolics.first :=
  subgroupEquiv.trans ((parrottFiniteImageEquiv.subgroupMap parrottR1Subgroup).trans
    (MulEquiv.subgroupCongr ReeLocalBlockOrders.first_map))

/-- This is the prescribed Parrott marking, not an unmarked order comparison. -/
theorem modelEquiv_generator_val (i : ParrottR1Generator) :
    (modelEquiv (parrottR1Generator i)).val =
      atlas1600ParrottAssignment (parrottR1GeneratorInclusion i) := by
  change parrottFiniteImageEquiv (parrottR1ToParrott (parrottR1Generator i)) = _
  rw [parrottR1ToParrott_generator, parrottFiniteImageEquiv_generator]

/-- Actual generators, their 28 equations, and generation of the entire target.
No quotient, core, cardinality, or isomorphism is included in these data. -/
structure Generators (H : Type*) [Group H] where
  element : ParrottR1Generator → H
  relations : ∀ i : ParrottR1RelatorIndex,
    FreeGroup.lift element (parrottR1Relator i) = 1
  generates : closure (Set.range element) = ⊤

namespace Generators
variable {H : Type*} [Group H] (d : Generators H)

/-- Evaluation of the local presentation on the supplied generators. -/
def lift : ParrottR1Group →* H :=
  PresentedGroup.toGroup (by rintro _ ⟨i, rfl⟩; exact d.relations i)

@[simp] theorem lift_generator (i : ParrottR1Generator) :
    d.lift (parrottR1Generator i) = d.element i := PresentedGroup.toGroup.of _

/-- Generation makes evaluation onto the whole target. -/
theorem lift_surjective : Function.Surjective d.lift := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← d.generates]
  apply (closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact ⟨parrottR1Generator i, d.lift_generator i⟩

include d in
/-- Relations and generation alone give the finite upper bound. -/
theorem finite_card_le : Finite H ∧ Nat.card H ≤ 10240 := by
  let := FirstParabolicPresentation.finite_card_le.1
  exact ⟨Finite.of_surjective _ d.lift_surjective,
    (Nat.card_le_card_of_surjective _ d.lift_surjective).trans
      FirstParabolicPresentation.finite_card_le.2⟩

/-- The lower bound removes the kernel of the relation-defined map. -/
theorem exists_equiv (hlower : 10240 ≤ Nat.card H) :
    ∃ e : ExceptionalParabolics.first ≃* H,
      ∀ i, e (modelEquiv (parrottR1Generator i)) = d.element i := by
  let := FirstParabolicPresentation.finite_card_le.1
  let e : ParrottR1Group ≃* H := MulEquiv.ofBijective d.lift
    (d.lift_surjective.bijective_of_nat_card_le
      (FirstParabolicPresentation.finite_card_le.2.trans hlower))
  refine ⟨modelEquiv.symm.trans e, ?_⟩
  intro i
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  exact d.lift_generator i

end Generators
end Tits.FirstParabolicPresentation
