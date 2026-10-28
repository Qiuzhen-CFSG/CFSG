module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Setup
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Contracts
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.OuterOrder
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# The model facts needed by the symplectic block action

The literal binary derived symplectic carrier is A₆, whose outer group has
order four. Over four elements the actual derived inclusion is an isomorphism
onto Sp₄(F); its center is trivial. Diagram-preserving semilinear coverage
then bounds the order of its outer group by four. This last coverage theorem
is still an explicit prerequisite, owned by the existing symplectic
semilinear-classification development.

Only centerlessness and the two-group outer quotient are needed here.
Source: Aschbacher–Smith E.6.8(2), printed pp.247–248, and E.6.23, p.254;
GLS3, Theorem 2.5.12 for the automorphism classification.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Symplectic
open Components Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms

/-- The field-four instance of the separately owned semilinear theorem.
It is a new prerequisite here, not a conclusion of E.6.8. -/
def FourDiagramClassification : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 →
    ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ (g : Sp F) (σ : F ≃+* F), a = MulAut.conj g * fieldAutomorphism σ

private theorem centerless_of_equiv {D E : Type*} [Group D] [Group E]
    (e : D ≃* E) (hz : center E = ⊥) : center D = ⊥ := by
  apply bot_unique
  intro d hd
  have hm := (centerCongr e ⟨d, hd⟩).property
  change e d ∈ center E at hm
  rw [hz] at hm
  exact e.injective (hm.trans (map_one e).symm)

private theorem disjoint_centralizer_of_centerless {G : Type*} [Group G]
    (X : Subgroup G) (hz : center X = ⊥) : Disjoint X (centralizer (X : Set G)) := by
  apply disjoint_iff_inf_le.mpr
  intro x hx
  have hm : (⟨x, hx.1⟩ : X) ∈ center X := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hx.2 y y.property)
  rw [hz] at hm
  exact congrArg Subtype.val hm

variable {G : Type*} [Group G] {X : Subgroup G}

/-- No outer-action premise is needed for the binary derived endpoint. -/
theorem binary_action_data (hm : SymplecticDerivedModel X 1) :
    Disjoint X (centralizer (X : Set G)) ∧ IsPGroup 2 (MulAut.Outer X) := by
  obtain ⟨e⟩ := ComponentCase.binary_symplectic_model hm
  refine ⟨disjoint_centralizer_of_centerless X
    (centerless_of_equiv e (alternatingGroup.center_eq_bot (by simp))), ?_⟩
  exact (IsPGroup.of_card (p := 2) (n := 2)
    AlternatingSix.ShadowLocal.outer_card).of_equiv (MulAut.outerCongr e).symm

/-- The nonbinary carrier is identified by the actual derived inclusion.
The remaining semilinear premise gives the two-group outer bound. -/
theorem four_action_data (hclass : FourDiagramClassification)
    (hm : SymplecticDerivedModel X 2) :
    Disjoint X (centralizer (X : Set G)) ∧ IsPGroup 2 (MulAut.Outer X) := by
  obtain ⟨_, F, _, _, hF, ⟨e⟩⟩ := hm
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  have hF4 : Nat.card F = 4 := hF
  have hlarge : 2 < Nat.card F := by omega
  let f : X ≃* Sp F := e.trans (derivedEquivFull_of_card_gt_two hlarge)
  refine ⟨disjoint_centralizer_of_centerless X
    (centerless_of_equiv f EvenProjective.center_eq_bot), ?_⟩
  have ho : IsPGroup 2 (MulAut.Outer (Sp F)) :=
    IsPGroup.of_card_dvd_pow (n := 2)
      (card_outer_dvd_two_mul hF hlarge (hclass F hF4))
  exact ho.of_equiv (MulAut.outerCongr f).symm

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Symplectic
