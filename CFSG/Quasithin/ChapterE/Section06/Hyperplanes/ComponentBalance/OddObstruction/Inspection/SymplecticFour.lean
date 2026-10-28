module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Inspection.Geometry
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Models
public import Theory.SpecificGroups.SymplecticFour.FieldFourOddCore
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification

/-!
# The field-four symplectic branch of the E.6.19 inspection

The specified model identifies L with the actual derived subgroup of Sp₄(F),
where F has four elements. Root generation and torus commutators prove that
this matrix group is perfect, so inclusion identifies its derived subgroup
with the full group. Transport the faithful action through that equivalence,
keeping the acting group and its specified order-two subgroup unchanged.

The intrinsic calculation eliminates the odd core of the surrounding action
centralizer. A conditional helper records the transfer interface, while the
public theorem below discharges its diagram-preserving semilinear premise via
the actual geometric classification of symplectic automorphisms.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8(2),
printed pp.247–248 (PDF pp.258–259), and E.6.19, printed p.252 (PDF p.263).
-/

public section

open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction

/-- Conditional assembly for the actual derived field-four model. Semilinear
classification is the only extra premise, and must be proved separately before
asserting the unconditional symplectic branch of E.6.19. -/
theorem symplectic_four_oddCore_eq_bot_of_semilinear
    (hclass : ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 →
      ∀ a : MulAut (Sp F), DiagramAutomorphisms.PreservesDiagram a →
        ∃ g : Sp F, ∃ σ : F ≃+* F,
          a = MulAut.conj g * DiagramAutomorphisms.fieldAutomorphism σ)
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {L : Subgroup G} (_hL : IsQuasisimple L)
    {φ : H →* MulAut L} {E : Subgroup H}
    (d : Theory.GroupAction.SylowFixedInvolution φ E)
    (hm : Components.SymplecticDerivedModel L 2) :
    pPrimeCore 2 (centralizer (E : Set H)) = ⊥ := by
  obtain ⟨_, F, hField, hFinite, hF, ⟨e⟩⟩ := hm
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  have hfour : Nat.card F = 4 := hF
  let e' : L ≃* Sp F := e.trans (derivedEquivFull_of_card_gt_two (by omega))
  exact FieldFourOddCore.action_centralizer_oddCore_eq_bot_of_semilinear hfour
    (hclass F hfour) (d.equiv e')

/-- The field-four symplectic derived model cannot realize the odd-core
obstruction. Diagram preservation forces every automorphism in the actual
surrounding action to be inner-field, so the intrinsic Sylow-centralizer
calculation transfers to that action. -/
theorem symplectic_four_oddCore_eq_bot
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {L : Subgroup G} (_hL : IsQuasisimple L)
    {φ : H →* MulAut L} {E : Subgroup H}
    (d : Theory.GroupAction.SylowFixedInvolution φ E)
    (hm : Components.SymplecticDerivedModel L 2) :
    pPrimeCore 2 (centralizer (E : Set H)) = ⊥ := by
  exact symplectic_four_oddCore_eq_bot_of_semilinear
    (fun F _ _ _ hF a ha =>
      DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram
        a ha)
    _hL d hm

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction
