module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Tactic.FinCases

/-!
# The five standard Hall--Janko relators

We define the five relators of the ATLAS presentation `J2G1-P2` and check
them on the literal degree-100 generating pair. This gives a surjection from
the presented group to the carrier. Injectivity of that surjection remains a
separate obligation: the checked word equations alone are not a presentation
proof. The universal map below allows the independent octonion calculation
to use exactly the same five words.

Source: R. A. Wilson et al., ATLAS of Finite Group Representations,
https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/J2G1-P2 . The generator data and
attributions are retained by the imported permutation construction. The
application is Aschbacher--Smith, K.4.5, printed p.460/PDF p.471.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.Presentation

/-- The additional length-ten word in the five-relator presentation. -/
def longWord {G : Type*} [Group G] (x y : G) : G :=
  x * y * x * y * x * y⁻¹ * x * y * x * y⁻¹

/-- The commutator uses the literal ATLAS convention `x⁻¹ y⁻¹ x y`. -/
def relatorValues {G : Type*} [Group G] (x y : G) : Fin 5 → G :=
  ![x ^ 2, y ^ 3, (x * y) ^ 7, (x⁻¹ * y⁻¹ * x * y) ^ 12, longWord x y ^ 6]

/-- These are equations, not an assertion that they present the generated group. -/
def Relations {G : Type*} [Group G] (x y : G) : Prop :=
  ∀ i, relatorValues x y i = 1

@[simp] theorem map_longWord {G H : Type*} [Group G] [Group H]
    (f : G →* H) (x y : G) : f (longWord x y) = longWord (f x) (f y) := by
  simp [longWord]

theorem map_relatorValues {G H : Type*} [Group G] [Group H]
    (f : G →* H) (x y : G) (i : Fin 5) :
    f (relatorValues x y i) = relatorValues (f x) (f y) i := by
  fin_cases i <;> simp [relatorValues]

set_option maxRecDepth 20000 in
/-- The original carrier satisfies all five displayed relations. -/
theorem carrier_relations : Relations GeneratorPair.a GeneratorPair.b := by
  intro i
  apply inclusion_injective
  rw [map_relatorValues, map_one]
  change relatorValues generatorA generatorB i = 1
  rw [GeneratorPair.generatorA_eq_table, GeneratorPair.generatorB_eq_table]
  revert i
  decide +kernel

/-- Relators in the free group, with generator 0 corresponding to `a`. -/
def relators : Set (FreeGroup (Fin 2)) :=
  Set.range (relatorValues (FreeGroup.of 0) (FreeGroup.of 1))

abbrev UniversalGroup := PresentedGroup relators

/-- The universal homomorphism associated to a pair satisfying the five words. -/
def toGroup {H : Type*} [Group H] (x y : H) (h : Relations x y) : UniversalGroup →* H :=
  PresentedGroup.toGroup (f := ![x, y]) (by
    rintro r ⟨i, rfl⟩
    rw [map_relatorValues]
    simpa using h i)

@[simp] theorem toGroup_zero {H : Type*} [Group H] (x y : H) (h : Relations x y) :
    toGroup x y h (PresentedGroup.of 0) = x := by
  exact PresentedGroup.toGroup.of _

@[simp] theorem toGroup_one {H : Type*} [Group H] (x y : H) (h : Relations x y) :
    toGroup x y h (PresentedGroup.of 1) = y := by
  exact PresentedGroup.toGroup.of _

/-- The map onto the actual permutation carrier, without an injectivity assertion. -/
def toCarrier : UniversalGroup →* Carrier :=
  toGroup GeneratorPair.a GeneratorPair.b carrier_relations

@[simp] theorem toCarrier_zero : toCarrier (PresentedGroup.of 0) = GeneratorPair.a :=
  toGroup_zero _ _ _

@[simp] theorem toCarrier_one : toCarrier (PresentedGroup.of 1) = GeneratorPair.b :=
  toGroup_one _ _ _

theorem toCarrier_surjective : Function.Surjective toCarrier := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← GeneratorPair.closure_pair_eq_top]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact ⟨PresentedGroup.of 0, toCarrier_zero⟩
  · rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨PresentedGroup.of 1, toCarrier_one⟩

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.Presentation
