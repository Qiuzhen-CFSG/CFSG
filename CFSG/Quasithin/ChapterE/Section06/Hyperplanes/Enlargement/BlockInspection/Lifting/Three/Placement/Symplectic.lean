module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Setup
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Symplectic.FixedProducts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Symplectic.Models
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Symplectic.FactorSeparation
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Five
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification

/-!
# The two symplectic mixed-action branches

The source orbit theorem and two-perfection make L normalize X. The actual
outer action, the centerless model and the original subnormal chain then
reduce the dichotomy to normal-factor separation in characteristic two.
For the binary branch the outer-group input is proved unconditionally from
Sp₄(2)' ≃ A₆. The field-four branch specializes the proved classification
of diagram-preserving automorphisms of the actual symplectic matrix group.

The final theorem discharges both new prerequisites and proves the original
SymplecticInteraction contract using only E.6.1, characteristic two of the
hyperplane centralizers, and the earlier orbit clause of 1.2.1(3). In particular,
no localization, normalization or factor-placement conclusion is assumed.
Source: Aschbacher–Smith E.6.8 and E.6.23, printed pp.247–248 and 254–255;
Proposition 1.2.1(3), p.504, and Definition 1.2.3/Lemma 1.2.4, p.505.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement
open ComponentBalance Components Symplectic
universe u
variable {G : Type u} [Group G]

/-- The complete orbit/model clause of source 1.2.1(3), in its equivalent
normalizer-index form. It applies to the genuine relative C-components. -/
def EarlierComponentOrbits : Prop :=
  ∀ H : Subgroup G, H ∈ Chapter1.H G → ∀ X : Subgroup H, X.IsCComponent →
    X.Normal ∨ (normalizer (X : Set H)).index = 2 ∧
      Chapter1.Section02.NonnormalCComponentModel (X ⧸ pCore 2 X)

variable [Finite G] {M V : Subgroup G}

/-- The symplectic interaction follows after the two independent new
prerequisites are supplied. All normalization and fixed-product hypotheses
are proved here from the original source configuration. -/
theorem symplecticInteraction_of_factor_separation_and_diagram
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (hchar : ∀ W : Subgroup G, IsHyperplane V W →
      generalizedFitting (centralizer (W : Set G)) = pCore 2 (centralizer (W : Set G)))
    (horbit : EarlierComponentOrbits (G := G))
    (hsep : ThreeFactorSeparation.{u}) (hclass : FourDiagramClassification) :
    SymplecticInteraction M V := by
  intro U _ hUh L hL h3 _ A hA hAU _ X hX _ hm
  have hXo : (X.subgroupOf (centralizer (A : Set G))).Normal ∨
      (normalizer (X.subgroupOf (centralizer (A : Set G)) :
        Set (centralizer (A : Set G)))).index = 2 :=
    (horbit _ (obstruction_centralizer_mem_H h hA) _ hX.2.isCComponent).imp_right And.left
  have hUX : U ≤ normalizer (X : Set G) :=
    hUh.1.trans (component_normalized_by_V h hA hX)
  have ha : Disjoint X (centralizer (X : Set G)) ∧ IsPGroup 2 (MulAut.Outer X) := by
    rcases hm with hb | ⟨hf, _, _⟩
    · exact binary_action_data hb.model
    · exact four_action_data hclass hf.model
  exact interaction_of_factor_separation hsep hL h3 (centralizer_le hAU) hX.1
    hXo (hchar U hUh) hUX ha.1 ha.2

/-- The original A₃ block either lies in the symplectic component or centralizes
it, in both the binary derived and field-four branches. The only explicit
earlier inputs are hyperplane characteristic two and the exact orbit clause
of 1.2.1(3); E.6.15 is not needed once these inputs are supplied. -/
theorem symplecticInteraction
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (hchar : ∀ W : Subgroup G, IsHyperplane V W →
      generalizedFitting (centralizer (W : Set G)) = pCore 2 (centralizer (W : Set G)))
    (horbit : EarlierComponentOrbits (G := G)) :
    SymplecticInteraction M V := by
  apply symplecticInteraction_of_factor_separation_and_diagram h hchar horbit
    threeFactorSeparation
  intro F _ _ _ _ a ha
  exact Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram a ha

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement
