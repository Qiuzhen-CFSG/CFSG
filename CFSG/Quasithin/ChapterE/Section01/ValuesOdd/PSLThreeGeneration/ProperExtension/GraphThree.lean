module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Overgroups
public import Theory.SpecificGroups.PSL3.OddPrimeGraphExtension
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.LocalGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry
public import Theory.SpecificGroups.PSL3.OddPrimeGraphExtension.FieldTransport
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Rank-one generation from local geometry in the graph extension

The local-section calculation proves E1 membership from actual symmetric-three
quotients, while simple-socle structure settles actors of rank at most one.
The concrete finite calculation places conjugates of larger actors in suitable
local subgroups. Field transport commutes with inverse transpose and identifies
the literal graph extensions, transporting the proved calculation over ZMod 3
to every field of order three. This proves rank-one E-generation without an
additional strong-quasithinness hypothesis.

The earlier solvable-generating-pair implications are preserved as conditional
APIs. No such pair is asserted here. The current route requires local subgroups
containing the actor's Sylow centralizer, with a Sylow intersection; it does not
require each local subgroup to contain the whole ambient Sylow subgroup.

Source: Aschbacher--Smith, E.1.2, E.1.5, E.1.8, E.1.12--13 and E.1.14(7),
printed pp.209--214, and Asc82a Lemma 4.11. The model input is the concrete graph extension of
`Theory.SpecificGroups.PSL3.OddPrimeGraphExtension`.
-/

public section

open Subgroup
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree

variable {G : Type*} [Group G] [Finite G]

/-- Two solvable overgroups of one Sylow two-subgroup give rank-one
E-generation.  The hypotheses are exactly the source-faithful generating
family used by E.1.12; the E-member and local-tau obligations are discharged
by `solvable_overgroup_le_generationTarget`.
-/
theorem isEGenerated_one_of_solvable_generating_pair
    (hpair : ∃ (T : Sylow 2 G) (P Q : Subgroup G),
      (T : Subgroup G) ≤ P ∧ (T : Subgroup G) ≤ Q ∧
      Group.IsSolvable P ∧ Group.IsSolvable Q ∧ P ⊔ Q = ⊤) :
    IsEGenerated 1 G := by
  obtain ⟨T, P, Q, hTP, hTQ, hP, hQ, hPQ⟩ := hpair
  let _ := hP
  let _ := hQ
  apply IsEGeneratedAt.isEGenerated (T := T)
  intro Ω hΩ
  apply top_unique
  change ⊤ ≤ ChiefOrbit.generationTarget 1 T Ω
  rw [← hPQ]
  exact sup_le
    (ChiefOrbit.solvable_overgroup_le_generationTarget (by decide) T P hTP hΩ)
    (ChiefOrbit.solvable_overgroup_le_generationTarget (by decide) T Q hTQ hΩ)

/-- A sufficient generating-pair criterion, retained as a conditional API.
This theorem does not construct such a pair in the graph model.
-/
theorem graphExtension_isEGenerated_one_of_solvable_generating_pair
    {F : Type*} [Field F] [Finite F] [IsSimpleGroup PSL(3, F)]
    (hpair : ∃ (T : Sylow 2 (graphExtension F))
      (P Q : Subgroup (graphExtension F)),
      (T : Subgroup (graphExtension F)) ≤ P ∧
      (T : Subgroup (graphExtension F)) ≤ Q ∧
      Group.IsSolvable P ∧ Group.IsSolvable Q ∧ P ⊔ Q = ⊤) :
    IsEGenerated 1 (graphExtension F) :=
  isEGenerated_one_of_solvable_generating_pair hpair

/-- The order-three graph-model branch after the concrete placement theorem.
The field need not be definitionally ZMod 3, and simplicity is transported
from the supplied instance. Strong quasithinness is unnecessary for this
conditional route. The finite local geometry remains a separate obligation. -/
theorem graphExtension_isEGenerated_one_of_three_localGeometry
    (hgeo : ∃ T : Sylow 2 (graphExtension (ZMod 3)), LocalGeometryAt T)
    {F : Type*} [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]
    (hF : Nat.card F = 3) : IsEGenerated 1 (graphExtension F) := by
  let _ := Fintype.ofFinite F
  let e : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  let _ : IsSimpleGroup PSL(3,ZMod 3) := (Atlas.fieldEquivPSL 3 e).symm.isSimpleGroup
  exact (isEGenerated_one_of_localGeometry (ZMod 3) hgeo).map_equiv
    (FieldTransport.graphExtensionEquiv e).symm

/-- The actual PSL₃ graph extension over every field of order three is
rank-one E-generated. The concrete placement theorem discharges the entire
local-geometry premise, including both inner and outer elementary actors.
This supplies `hthree` in
`ProperExtension.isEGenerated_one_of_graph_model_calculations`; its
strong-quasithinness premise is not needed for this model calculation. -/
theorem graphExtension_isEGenerated_one_of_three
    {F : Type*} [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]
    (hF : Nat.card F = 3) : IsEGenerated 1 (graphExtension F) :=
  graphExtension_isEGenerated_one_of_three_localGeometry
    exists_localGeometry_zmod_three hF

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree
