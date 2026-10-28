module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.Structure
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.ModelRank
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# The complete earlier B.5.2 and B.5.5 implications

These are universal source inputs, not asserted theorems. B.5.2 selects its
own prepared cover. B.5.5 retains the fixed space, both offenders, the actual
faithful chief section, its literal action image, and every B.4.2 action row.
The application below deduces positive three-rank for every component from
that section. The assembly owner must discharge the two universal inputs.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.2–5,
printed pp.103–105. Source producer: `qt-b05-quotient-components`.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction
universe u v

/-- All four B.5.2 clauses on one existentially selected presentation. -/
structure ComponentCover (K : GroupClass.{u}) (G : Type u) [Group G] where
  prepared : PreparedCover K G
  component_lifts : ∀ L : Subgroup G, IsComponent G L →
    ∃ M : Subgroup prepared.Cover,
      IsComponent prepared.Cover M ∧ M.map prepared.projection = L
  fitting_image : (generalizedFitting prepared.Cover).map prepared.projection =
    generalizedFitting G

/-- B.5.2 is existential; this does not assert lifting for arbitrary covers. -/
def CoverInput (K : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    Nonempty (SQTKQuotient K G) → Nonempty (ComponentCover K G)

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The precise fixed space in B.5.5(1ii), inside the original module. -/
noncomputable def componentFixed (L A : Subgroup G) : Submodule (ZMod 2) V :=
  fixedSpace ρ ((pCore 2 (L ⊔ A : Subgroup G)).map (L ⊔ A).subtype)

/-- All fixed-space assertions in B.5.5(1ii) for the specified offender. -/
structure FixedOffender (L A : Subgroup G) : Prop where
  stable : L ⊔ A ≤ subspaceStabilizer ρ (componentFixed ρ L A)
  faithful : subspaceKernel ρ (componentFixed ρ L A) L = ⊥
  centralizer : subspaceKernel ρ (componentFixed ρ L A) A =
    A ⊓ Subgroup.centralizer (L : Set G)
  offender : IsBestOffender (subspaceImageRepresentation ρ (componentFixed ρ L A))
    (restrictedSubgroup ρ (componentFixed ρ L A) A)

/-- An A-invariant L-chief section of the original V. Its actor is LA;
the group acting faithfully on it is the actual image of this representation. -/
structure ChiefSection (L A : Subgroup G) where
  lower : Subrepresentation (ρ.comp (L ⊔ A).subtype)
  upper : Subrepresentation (ρ.comp (L ⊔ A).subtype)
  contained : lower ≤ upper
  faithful : Function.Injective
    ((sectionRepresentation (ρ.comp (L ⊔ A).subtype) lower upper).comp
      (L.subgroupOf (L ⊔ A)).subtype)
  irreducible : IsIrreducible
    ((sectionRepresentation (ρ.comp (L ⊔ A).subtype) lower upper).comp
      (L.subgroupOf (L ⊔ A)).subtype)

noncomputable abbrev ChiefSection.action {L A : Subgroup G} (s : ChiefSection ρ L A) :=
  sectionRepresentation (ρ.comp (L ⊔ A).subtype) s.lower s.upper

/-- B.5.5(1iii–iv), with the same section in the Fitting, offender and model clauses. -/
structure ChiefOffender (L : Subgroup G) where
  offender : Subgroup G
  best : IsBestOffender ρ offender
  moves : ⁅L, offender⁆ = L
  sectionData : ChiefSection ρ L offender
  fitting : generalizedFitting (actionImage sectionData.action) =
    actionSubgroup sectionData.action (L.subgroupOf (L ⊔ offender))
  contains_offender : ∃ B : Subgroup (actionImage sectionData.action),
    B ≤ actionSubgroup sectionData.action (offender.subgroupOf (L ⊔ offender)) ∧
      IsBestOffender (imageRepresentation sectionData.action) B
  models : ProjectiveLine.IrreducibleActionCase (imageRepresentation sectionData.action)
    (actionSubgroup sectionData.action (L.subgroupOf (L ⊔ offender)))
    (offenderSubgroup (imageRepresentation sectionData.action))

/-- The complete B.5.5 conclusion, including its assertions for every offender
moving L and for every prime other than three. -/
structure ComponentConclusion : Prop where
  normal : ∀ L : Subgroup G, IsComponent G L → L.Normal
  exists_offender : ∀ L : Subgroup G, IsComponent G L →
    ∃ A : Subgroup G, IsBestOffender ρ A ∧ ⁅L, A⁆ = L
  fixed_offender : ∀ L : Subgroup G, IsComponent G L →
    ∀ A : Subgroup G, IsBestOffender ρ A → ⁅L, A⁆ = L → FixedOffender ρ L A
  chief_offender : ∀ L : Subgroup G, IsComponent G L → Nonempty (ChiefOffender ρ L)
  cores_central : ∀ p : ℕ, p.Prime → p ≠ 3 → pCore p G ≤ center G
  fitting : generalizedFitting G = (componentLayer G ⊔ pCore 3 G) ⊔ center G

/-- The full universal B.5.5 implication under the unchanged B.5.3 hypotheses. -/
def ComponentsInput (K : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G]
    (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V), FFHypothesis K ρ → ComponentConclusion ρ

variable [Finite G]

/-- Apply the complete model list to the literal section image, then transport
back through the original inclusion L → LA. No component is omitted. -/
theorem component_rank_pos {K : GroupClass.{u}} (h55 : ComponentsInput.{u,v} K)
    (hyp : FFHypothesis K ρ) {L : Subgroup G} (hL : IsComponent G L) :
    0 < primeRank 3 L := by
  obtain ⟨s⟩ := (h55 G V ρ hyp).chief_offender L hL
  have hi := rank_pos_of_section_action (actionHom s.sectionData.action)
    (L.subgroupOf (L ⊔ s.offender)) s.models
  rwa [primeRank_equiv 3 (subgroupOfEquivOfLe
    (show L ≤ L ⊔ s.offender from le_sup_left))] at hi

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction
