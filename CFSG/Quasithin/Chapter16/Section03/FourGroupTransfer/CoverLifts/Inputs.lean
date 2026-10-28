module
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.Contracts
public import Theory.GroupTheory.DoubleCoverCentralizer.Action
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# The remaining table reduction for the exceptional cover argument

All subgroups below are the actual layer closure and intrinsic centralizer.
`CoverLiftConclusion` requests concrete C₄/Q₈ isomorphisms and an element
implementing the given ambient conjugation action. `TableReduction` is an
intermediate output still to be proved from the earlier component tables;
it is not declared to be an equivalent statement of those source theorems.

The unresolved adapter must prove the non-2-central mark on the quotient by
the center, the inner-action index bound, the M₁₂ restriction on outer actors,
and the center bound. The lift and small-group recognition are independent
of that adapter. Perfectness and the equality of the two descriptions of the
inner action are proved here directly from the supplied component hypotheses.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.2 and 16.1.5, printed pp.1170–1172, and the final paragraph of 16.3.6,
printed p.1179 / PDF p.1196.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.CoverLifts
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer ClassificationModels
variable {G : Type*} [Group G]

abbrev Enlargement (L : Subgroup G) (i : G) :=
  ComponentTransfer.layerClosure (involutionCentralizer i) L

abbrev ComponentInside (L : Subgroup G) (i : G) := L.subgroupOf (Enlargement L i)

abbrev ComponentCentralizer (L : Subgroup G) (i : G) :=
  centralizer (ComponentInside L i : Set (Enlargement L i))

/-- Intermediate table obligations, not a reformulation of 16.1.2 or 16.1.5.
The source-table adapter must construct this record. In particular the mark
must be proved from the centralizer table and component hypothesis. -/
structure TableReduction (E L : Subgroup G) (i : G)
    (h : ExceptionalEnlargement E L i) : Prop where
  center_bound : Nat.card (center (Enlargement L i)) ≤ 2
  inner_index : (innerActors (inducedAction E (Enlargement L i) h.normalizes)).index ≤ 2
  outer_m12 : ∀ e : E,
    inducedAction E (Enlargement L i) h.normalizes e ∉
      (MulAut.conj : Enlargement L i →* MulAut (Enlargement L i)).range →
      Nonempty ((Enlargement L i ⧸ pCore 2 (Enlargement L i)) ≃* SporadicName.m12.Carrier)
  non_two_central_mark : ∀ f : Enlargement L i,
    orderOf (QuotientGroup.mk' (center (Enlargement L i)) f) = 2 →
    MulAut.conj f ∈ (inducedAction E (Enlargement L i) h.normalizes).range →
      ¬ TwoCentral (QuotientGroup.mk' (center (Enlargement L i)) f)

/-- Both concrete centralizer alternatives and the actual order-four lift
used to write the nonidentity actor as r₀f in the ambient group. -/
def CoverLiftConclusion (E L : Subgroup G) (i : G)
    (h : ExceptionalEnlargement E L i) : Prop :=
  (Nonempty (ComponentCentralizer L i ≃* QuaternionGroup 2) ∨
    (Nonempty (ComponentCentralizer L i ≃* Multiplicative (ZMod 4)) ∧
      Nonempty ((Enlargement L i ⧸ pCore 2 (Enlargement L i)) ≃* SporadicName.m12.Carrier))) ∧
  ∃ e : E, e ≠ 1 ∧ ∃ f : Enlargement L i,
    (f : G) ∈ centralizer (L : Set G) ∧ orderOf f = 4 ∧
      f ^ 2 ∈ center (Enlargement L i) ∧
        inducedAction E (Enlargement L i) h.normalizes e = MulAut.conj f

/-- The action of L on its enlargement is precisely its intrinsic inner action. -/
theorem component_action_range (L : Subgroup G) (i : G) :
    (inducedAction L (Enlargement L i)
      ((ComponentTransfer.le_layerClosure _ _).trans (Enlargement L i).le_normalizer)).range =
        (ComponentInside L i).map (MulAut.conj : Enlargement L i →* MulAut (Enlargement L i)) := by
  ext a
  constructor
  · rintro ⟨l, rfl⟩
    refine ⟨⟨l, ComponentTransfer.le_layerClosure _ _ l.property⟩, l.property, ?_⟩
    ext x
    rfl
  · rintro ⟨l, hl, rfl⟩
    refine ⟨⟨l, hl⟩, ?_⟩
    ext x
    rfl

/-- A nonidentity actor supplies the perfectness needed in centralizer reflection. -/
theorem componentInside_perfect [Finite G] {E L : Subgroup G} {i : G}
    (hcard : Nat.card E = 4) (hc : CentralizesAsComponent E L) :
    Group.IsPerfect (ComponentInside L i) := by
  have hne : 1 < Nat.card E := by omega
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp hne
  obtain ⟨e, he⟩ := exists_ne (1 : E)
  have hcomp := hc e e.property (fun hh => he (Subtype.ext hh))
  let := hcomp.quasisimple
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (ComponentTransfer.le_layerClosure (involutionCentralizer i) L)).symm.toMonoidHom)
    (subgroupOfEquivOfLe (ComponentTransfer.le_layerClosure (involutionCentralizer i) L)).symm.surjective

end CFSG.Quasithin.Chapter16.FourGroupTransfer.CoverLifts
