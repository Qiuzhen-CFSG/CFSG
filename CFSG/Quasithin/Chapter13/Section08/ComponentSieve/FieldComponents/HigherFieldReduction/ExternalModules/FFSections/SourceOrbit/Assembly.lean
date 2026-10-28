module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SectionCoordinates
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.FullSource
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.HomogeneousSelection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.OuterAssembly
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage

/-!
# The external constituent, its cubic orbit, and its faithful central action

The parent supplies the genuine F.9 setup and the earlier external-branch
structure, including the marked commuting S₃. The complete universal
F.9.18(4) implication is the sole earlier module-classification input.
Quasisimplicity is transported through the actual two-core quotient;
faithfulness and A.1.42 then construct a homogeneous Irr⁺ member.

The paired restriction excludes (4i) and (4iii), hence the member is
T-invariant and FF. The proved outer groups of all three surviving carriers
discharge the supplement calculation and give H* = K*X*T*. Thus its literal
orbit consists of two X*-conjugates. Its central quotient is identified with
the canonical multiplicity module by the inclusion and quotient maps in
CubicOrbit.Quotients, not by replacing the member with an inverter-fixed
space. Finally the actual KT action on I/C_I(K*) has faithful action image,
quasisimple generalized Fitting subgroup, irreducible component action,
SQTK and an actual best offender. No B.4.2 family is selected here.

Source: Aschbacher–Smith, proof of 13.8.20(a), pp.954–955; F.9.18(4),
pp.325–326; A.1.42, p.32; B.4.2, p.86, manuscript of 1 March 2004.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender InvertedCubicTensor Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit

universe u
variable {G : Type u} [Group G] [Finite G]
    (H K X L₁ T V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    [(Source.starImage H K).Normal]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (P : Sylow 2 (Source.Hstar H)) (s : S₃ →* Source.Hstar H)

/-- Earlier external-branch structural outputs, supplied by the parent.
No constituent, orbit identity, FF conclusion or action-image premise is assumed. -/
structure ExternalInputs : Prop where
  component_normal : (K.subgroupOf H).Normal
  centerless : center (Source.starImage H K) = ⊥
  component_rank : primeRank 3 K ≤ 1
  model : Structure.ExternalCarrier (Source.starImage H K)
  solvable : Group.IsSolvable (L₁ ⊔ T : Subgroup G)
  one_twoPerfect : IsPPerfect 2 L₁
  one_commutator : ⁅L₁, T⁆ = L₁
  fitting : Components.Fitting.twoFittingResidual H = ⊥ ∨
    Components.Fitting.twoFittingResidual H = X
  cubic_card : Nat.card (Source.starImage H X) = 3
  cubic_normal : (Source.starImage H X).Normal
  embedding : Function.Injective s
  commuting : ∀ (k : Source.starImage H K) g, Commute (k : Source.Hstar H) (s g)
  mark : (alternatingGroup (Fin 3)).map s = Source.starImage H X
  cubic_generation : subspaceCommutator ρ ⊤ (Source.starImage H X) = ⊤

variable {𝒦 : GroupClass.{u}}
    (L V : Subgroup G)
    (f : F918Hypotheses H K L L₁ T V V₃ V₁ ρ P 𝒦)
    (d : ExternalInputs H K X L₁ T V₃ V₁ ρ s)

omit [(Source.starImage H K).Normal] in
include f in
/-- The source's intrinsic quasisimple quotient is the actual K*, with
the kernel comparison supplied by the C-component theorem. -/
theorem source_quasisimple : IsQuasisimple (Source.starImage H K) :=
  (Components.quasisimple_star_iff H K f.component_le f.component).mpr
    f.quasisimple_quotient

omit [Finite G] [(Source.starImage H K).Normal] in
include f in
private theorem source_generation : H = K ⊔ (L₁ ⊔ T) := by
  rw [f.generation, f.single_component, f.overlap]

variable (I : Submodule (ZMod 2) (SeedAction.Space H V₃ V₁))
    (hI : IsIrrPlusWith ρ (Source.starImage H K) P I)
    (hIP : (P : Subgroup (Source.Hstar H)) ≤ subspaceStabilizer ρ I)

omit [(Source.starImage H K).Normal] in
include f d in
private theorem cubicInputs
    (hff : IsFFModule (imageRepresentation
      (constituentAction ρ (Source.starImage H K) P I hI.invariant hIP))) :
    SourceCubicInputs H K X L₁ T V₃ V₁ ρ P s I 𝒦 :=
  { conjugation := f.conjugation
    faithful := f.faithful
    generation := source_generation H K L₁ T V₃ V₁ ρ P L V f
    sylow_image := f.sylow_image
    sqtk := f.sqtk
    component := f.component
    component_normal := d.component_normal
    quasisimple := source_quasisimple H K L₁ T V₃ V₁ ρ P L V f
    centerless := d.centerless
    component_rank := d.component_rank
    model := d.model
    solvable := d.solvable
    one_twoPerfect := d.one_twoPerfect
    one_commutator := d.one_commutator
    fitting := d.fitting
    cubic_card := d.cubic_card
    cubic_normal := d.cubic_normal
    embedding := d.embedding
    commuting := d.commuting
    mark := d.mark
    cubic_generation := d.cubic_generation
    selected := hI
    invariant := hIP
    ff := hff }

local instance sourceCentralFinite :
    Finite (centralQuotient ρ (Source.starImage H K) I) :=
  Finite.of_surjective _ (ActionImage.projection_surjective ρ (Source.starImage H K) I)

/-- The constituent and orbit conclusions, including the literal action
to which the complete B.4.2 theorem applies. The coordinate constructors
and their quotient-map compatibility are re-exported from CubicOrbit.Quotients. -/
structure SelectedOrbitConclusion
    (hs : ∀ (k : Source.starImage H K) g, Commute (k : Source.Hstar H) (s g))
    (𝒦 : GroupClass.{u}) : Prop where
  sylow_orbit : orbitSpan ρ P I = I
  ff : IsFFModule (imageRepresentation
    (constituentAction ρ (Source.starImage H K) P I hI.invariant hIP))
  central_ff : IsFFModule (imageRepresentation
    (ActionImage.centralAction ρ (Source.starImage H K) P I hI.invariant hIP))
  conjugate_mem : (s cubic)⁻¹ ∈ Source.starImage H X
  conjugator_ne : (s cubic)⁻¹ ≠ 1
  conjugate_ne : rightConjugate ρ I (s cubic)⁻¹ ≠ I
  inclusion : I ≤ orbitSpan ρ ⊤ I
  conjugate_inclusion : rightConjugate ρ I (s cubic)⁻¹ ≤ orbitSpan ρ ⊤ I
  orbit : orbitSpan ρ ⊤ I = I ⊔ rightConjugate ρ I (s cubic)⁻¹
  central_disjoint : Disjoint (I.map (fixedSpace ρ (Source.starImage H K)).mkQ)
    ((rightConjugate ρ I (s cubic)⁻¹).map (fixedSpace ρ (Source.starImage H K)).mkQ)
  multiplicity : Nonempty
    ((centralQuotientRepresentation ρ (Source.starImage H K) I hI.isIrrPlus.choose).Equiv
      (sectionMultiplicityAction ρ (Source.starImage H K).subtype s hs
        (selectedOrbitLower ρ (Source.starImage H K)) (selectedOrbitUpper ρ I)))
  b4 : B4Hypotheses 𝒦 (imageRepresentation
    (ActionImage.centralAction ρ (Source.starImage H K) P I hI.invariant hIP))
  bestOffender : ∃ A, B42Hypotheses 𝒦 (imageRepresentation
    (ActionImage.centralAction ρ (Source.starImage H K) P I hI.invariant hIP)) A

include f in
/-- Every genuine homogeneous member has the asserted FF orbit and faithful
central action. All alternatives of the universal earlier theorem are tested. -/
theorem source_orbit_of_full_f918
    (earlier : FullF918Four 𝒦) :
    ∃ hIP : (P : Subgroup (Source.Hstar H)) ≤ subspaceStabilizer ρ I,
      SelectedOrbitConclusion H K X V₃ V₁ ρ P s I hI hIP d.commuting 𝒦 := by
  let : IsQuasisimple (Source.starImage H K) :=
    source_quasisimple H K L₁ T V₃ V₁ ρ P L V f
  let : IsMulCommutative (MulAut.Outer (Source.starImage H K)) :=
    externalCarrier_outer_abelian d.model d.centerless
  have hfull := earlier G H K L L₁ T V V₃ V₁ ρ P f
  obtain ⟨hIP, hIT, hff⟩ := ff_of_fourConclusion ρ (Source.starImage H K) P s
    d.commuting (by rw [d.mark]; exact d.cubic_generation) hfull I hI
  have c := cubicInputs H K X L₁ T V₃ V₁ ρ P s L V f d I hI hIP hff
  obtain ⟨ht, htne, hmoved, hIW, htW, horbit, hdis, he⟩ :=
    source_selected_cubic_orbit_of_outer_abelian H K X L₁ T V₃ V₁ ρ P s I c
  have a : ActionImage.SourceHypotheses H K L₁ T V₃ V₁ ρ P I 𝒦 :=
    { conjugation := f.conjugation
      generation := by simpa only [sup_assoc] using c.generation
      sylow_image := f.sylow_image
      sqtk := f.sqtk
      quasisimple := c.quasisimple
      centerless := d.centerless
      selected := hI
      invariant := hIP
      ff := hff }
  exact ⟨hIP, ⟨hIT, hff,
    ActionImage.quotient_ff ρ (Source.starImage H K) P I hI.invariant hIP hI hff,
    ht, htne, hmoved, hIW, htW, horbit, hdis, he,
    ActionImage.source_b4 H K L₁ T V₃ V₁ ρ P I a,
    ActionImage.source_b42 H K L₁ T V₃ V₁ ρ P I a⟩⟩

include f in
/-- Construct the actual constituent from faithfulness and A.1.42, then derive
its two-conjugate orbit and all B.4.2 premises. The full earlier F.9.18(4)
implication and the parent's structural outputs are the only source inputs. -/
theorem exists_source_orbit_of_full_f918 (earlier : FullF918Four 𝒦) :
    ∃ I : Submodule (ZMod 2) (SeedAction.Space H V₃ V₁),
      ∃ hI : IsIrrPlusWith ρ (Source.starImage H K) P I,
        ∃ hIP : (P : Subgroup (Source.Hstar H)) ≤ subspaceStabilizer ρ I,
          SelectedOrbitConclusion H K X V₃ V₁ ρ P s I hI hIP d.commuting 𝒦 := by
  let : IsQuasisimple (Source.starImage H K) :=
    source_quasisimple H K L₁ T V₃ V₁ ρ P L V f
  obtain ⟨I, hI⟩ := exists_homogeneous_of_quasisimple ρ f.faithful (Source.starImage H K) P
  exact ⟨I, hI, source_orbit_of_full_f918 H K X L₁ T V₃ V₁ ρ P s L V f d I hI earlier⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit
