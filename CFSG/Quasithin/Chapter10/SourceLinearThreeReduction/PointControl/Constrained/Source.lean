module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalSuzuki
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalBinaryExclusion
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalLocalPair
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalLocal
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalConstituents
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalSteinberg
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalSemisimple
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalBinaryAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalRecognition
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.OriginalAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.OriginalOrbit
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.Local.Exclusion
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.FourNaturalSelection
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.FourNaturalActions
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.FourNaturalRepeated
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.FourNaturalSeven
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.FourNatural
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.Torus
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.RankOne
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.AlternatingSeven
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.Recognized
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.RankOneExclusion
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.SevenDeleted
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.SevenCover
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.BinaryCover
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.BinaryKernel
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.RepeatedNatural
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.NaturalDual
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.Orthogonal
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.NaturalDualRows
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.NaturalDualSplit
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.NaturalDualPoint
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.NaturalDualExclusion
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.BinaryPositive
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.PositiveExclusion
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.QuietRows
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.FourNatural
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Local
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Branches
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Source

/-!
# Assembly of the constrained point-component exclusion

The literal reduced orbit VI supplies the containing FF action after the
proved preparation. The torus and A₇ exclusions leave the original binary-three
or Suzuki quotient. In the binary branch, local recognition gives a natural
three-space or natural–dual pair on [D.moduleSubgroup,L]. The pair is excluded
by the incompatible inner and outer actions of the same point Sylow.

The natural local marking now generates a reduced smaller orbit retaining
the exact VI kernel. Reselecting an opposite local point yields an irreducible
SL₅(2) action of dimension five or ten. Parabolic.Natural excludes both through
the plane centralizer, exchanged rank-one nodes and the SQTK cubic-rank bound.
Thus the entire original binary branch is excluded, independently of the size
or marking of [D.fullModule,L]. The full module and smaller orbit remain distinct.

The Suzuki pair is excluded on the full original action. Its centralizer has
no FF-offender by B.5.6, the actual Suzuki degree bounds and the doubled-natural
centralizer calculation. Local Thompson fixedness therefore extends to the
full module and supplies point Thompson equality. Preparation of the same VI
then forces cubic original quotient order, contradicting the Suzuki order.

`constrainedExclusion` proves the full parent contract with every constrained
premise discharged. Its literal point-control application retains only the
parent's independent half-Sylow, selection and quasisimple source inputs.
Earlier conditional APIs remain available. No later nonnormal-generation
bound, small-offender recognition or A₅ tensor exclusion is used.

Source: Aschbacher–Smith, 10.1.1 and 10.2.9, printed pp.741,751–753.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- Assembly on the original parent contract. Each independent producer
must be discharged before this becomes the source exclusion. -/
theorem constrainedExclusion_of_sourceSteps
    (hprepare : PreparationAt T) (hmodels : LinearFiveReductionAt T)
    (hendgame : LinearFiveExclusionAt T) : ConstrainedExclusionAt T := by
  intro hmany L D hminimal hnonA5 t v I hescape hnot hchar hr
  let c : Context D t v I := ⟨hmany,hminimal,hnonA5,hescape,hnot,hchar,hr⟩
  have p := hprepare L D t v I c
  have a := c.actionFacts p
  obtain ⟨m⟩ := hmodels L D t v I c a
  exact hendgame L D t v I c a m

/-- After the proved rank-ten exclusion, the terminal source obligation is
only the actual rank-five case. Preparation, model recognition, and this
remaining contradiction are still discharged by this module's final owner. -/
theorem constrainedExclusion_of_rankFiveSteps
    (hprepare : PreparationAt T) (hmodels : LinearFiveReductionAt T)
    (hfive : ∀ (L : Subgroup G) (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G) (c : Context D t v I),
      ActionFacts c → (m : LinearFiveData c) →
      (letI := c.reduced.elementary;
        Module.finrank (ZMod 2) (Additive (internalModule D v I)) = 5) → False) :
    ConstrainedExclusionAt T := by
  apply constrainedExclusion_of_sourceSteps hprepare hmodels
  intro L D t v I c a m
  exact hfive L D t v I c a m m.dimension_five

/-- The complete parabolic endgame leaves only the earlier preparation and
model recognition. This task's final owner must still discharge both. -/
theorem constrainedExclusion_of_preparation_and_models
    (hprepare : PreparationAt T) (hmodels : LinearFiveReductionAt T) :
    ConstrainedExclusionAt T :=
  constrainedExclusion_of_sourceSteps hprepare hmodels (linearFiveExclusion T)

/-- Actual point-control application: the constrained branch now uses the
proved rank-five and rank-ten exclusions on its literal action and orbit.
The owner qt-d-10-nona5-point-constrained retains hprepare and hmodels; the
parent qt-d-10-nona5-point-control owns discharge of the other source steps. -/
theorem source_nonnormalPointControl_of_preparation_and_models
    (hhalf : HalfSylowUniqueAt T) (hselect : SelectionAt T)
    (hquasi : QuasisimpleExclusionAt T)
    (hprepare : PreparationAt T) (hmodels : LinearFiveReductionAt T) :
    SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf hselect hquasi
    (constrainedExclusion_of_preparation_and_models hprepare hmodels)

/-- The moving and positive-fixed-layer preparations are discharged here.
The remaining local quiet preparation and containing-model recognition are
owned by qt-d-10-nona5-point-constrained. -/
theorem constrainedExclusion_of_quiet_fixed_free_and_models
    (hquiet : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G) (_c : Context D t v I),
      Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
        centralizer (D.moduleSubgroup : Set G) →
      D.fullModule ⊓ centralizer (Chapter3.Section02.localOrbit T L : Set G) = ⊥ →
      Prepared D v I)
    (hmodels : LinearFiveReductionAt T) : ConstrainedExclusionAt T := by
  apply constrainedExclusion_of_preparation_and_models ?_ hmodels
  intro L D t v I c
  exact hquiet L D t v I c c.local_thompson_fixed c.full_fixed_eq_bot

/-- Actual point-control application after excluding all original natural
covers. General quiet preparation and containing-model recognition remain
with qt-d-10-nona5-point-constrained; the parent owns the other source steps. -/
theorem source_nonnormalPointControl_of_quiet_fixed_free_and_models
    (hhalf : HalfSylowUniqueAt T) (hselect : SelectionAt T)
    (hquasi : QuasisimpleExclusionAt T)
    (hquiet : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G) (_c : Context D t v I),
      Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
        centralizer (D.moduleSubgroup : Set G) →
      D.fullModule ⊓ centralizer (Chapter3.Section02.localOrbit T L : Set G) = ⊥ →
      Prepared D v I)
    (hmodels : LinearFiveReductionAt T) : SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf hselect hquasi
    (constrainedExclusion_of_quiet_fixed_free_and_models hquiet hmodels)

/-- Point Thompson equality is already proved at cubic component order.
The remaining cubic orbit generation, three-free preparation and model
recognition stay with this task's final assembly owner. -/
theorem constrainedExclusion_of_quiet_orbits_three_free_and_models
    (horbit : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G) (_c : Context D t v I),
      Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
        centralizer (D.moduleSubgroup : Set G) →
      D.fullModule ⊓ centralizer (Chapter3.Section02.localOrbit T L : Set G) = ⊥ →
      3 ∣ Nat.card (L ⧸ pCore 2 L) → ⁅D.fullModule,L⁆ ≤ orbitModule D v I)
    (hfree : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G) (_c : Context D t v I),
      Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
        centralizer (D.moduleSubgroup : Set G) →
      D.fullModule ⊓ centralizer (Chapter3.Section02.localOrbit T L : Set G) = ⊥ →
      ¬ 3 ∣ Nat.card (L ⧸ pCore 2 L) → Prepared D v I)
    (hmodels : LinearFiveReductionAt T) : ConstrainedExclusionAt T :=
  constrainedExclusion_of_preparation_and_models
    (preparationAt_of_quiet_orbits_and_three_free horbit hfree) hmodels

/-- The concrete marked source rows leave only the retained four-natural
branch. This owner must still prove row recognition and exclude that branch;
neither premise is supplied by a conditional row definition. -/
theorem constrainedExclusion_of_original_covers_and_four_natural
    (hrows : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I → OriginalMovedCover D)
    (hfour : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I → FourNaturalCover D → False) :
    ConstrainedExclusionAt T := by
  intro hmany L D hminimal hnonA5 t v I hescape hnot hchar hr
  let c : Context D t v I := ⟨hmany,hminimal,hnonA5,hescape,hnot,hchar,hr⟩
  exact hfour L D t v I c (c.four_natural_of_original_moved_cover (hrows L D t v I c))

/-- Literal point-control consumer after excluding every marked original
row except four identical natural copies. The constrained owner retains
both displayed row obligations; qt-d-10-nona5-point-control owns the other
three source inputs. No later generation bound is used. -/
theorem source_nonnormalPointControl_of_original_covers_and_four_natural
    (hhalf : HalfSylowUniqueAt T) (hselect : SelectionAt T)
    (hquasi : QuasisimpleExclusionAt T)
    (hrows : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I → OriginalMovedCover D)
    (hfour : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I → FourNaturalCover D → False) :
    SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf hselect hquasi
    (constrainedExclusion_of_original_covers_and_four_natural hrows hfour)

/-- At cubic component order only the original local moved subgroup is
needed in the orbit. Local orbit recognition, three-free preparation and
containing-model recognition remain with the constrained source owner. -/
theorem constrainedExclusion_of_local_orbits_three_free_and_models
    (horbit : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I →
      3 ∣ Nat.card (L ⧸ pCore 2 L) → ⁅D.moduleSubgroup,L⁆ ≤ orbitModule D v I)
    (hfree : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I →
      ¬ 3 ∣ Nat.card (L ⧸ pCore 2 L) → Prepared D v I)
    (hmodels : LinearFiveReductionAt T) : ConstrainedExclusionAt T := by
  apply constrainedExclusion_of_preparation_and_models ?_ hmodels
  intro L D t v I c
  by_cases hd : 3 ∣ Nat.card (L ⧸ pCore 2 L)
  · exact c.prepared_of_local_moved_le_of_three hd (horbit L D t v I c hd)
  · exact hfree L D t v I c hd

/-- Literal point-control application of the weaker local orbit preparation.
The constrained owner retains the displayed source premises; the parent
point-control owner retains the other three source steps. -/
theorem source_nonnormalPointControl_of_local_orbits_three_free_and_models
    (hhalf : HalfSylowUniqueAt T) (hselect : SelectionAt T)
    (hquasi : QuasisimpleExclusionAt T)
    (horbit : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I →
      3 ∣ Nat.card (L ⧸ pCore 2 L) → ⁅D.moduleSubgroup,L⁆ ≤ orbitModule D v I)
    (hfree : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I →
      ¬ 3 ∣ Nat.card (L ⧸ pCore 2 L) → Prepared D v I)
    (hmodels : LinearFiveReductionAt T) : SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf hselect hquasi
    (constrainedExclusion_of_local_orbits_three_free_and_models horbit hfree hmodels)

/-- Local orbit containment is discharged from the original context. The
remaining three-free preparation and containing-action reduction stay with
this constrained owner; neither is asserted as a source theorem here. -/
theorem constrainedExclusion_of_three_free_and_models
    (hfree : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I →
      ¬ 3 ∣ Nat.card (L ⧸ pCore 2 L) → Prepared D v I)
    (hmodels : LinearFiveReductionAt T) : ConstrainedExclusionAt T :=
  constrainedExclusion_of_local_orbits_three_free_and_models
    (fun _ _ _ _ _ c _ => c.local_moved_le) hfree hmodels

/-- Literal point-control application with original local orbit preparation
proved. This owner retains the displayed constrained source premises;
the parent point-control owner retains the other three source steps. -/
theorem source_nonnormalPointControl_of_three_free_and_models
    (hhalf : HalfSylowUniqueAt T) (hselect : SelectionAt T)
    (hquasi : QuasisimpleExclusionAt T)
    (hfree : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I →
      ¬ 3 ∣ Nat.card (L ⧸ pCore 2 L) → Prepared D v I)
    (hmodels : LinearFiveReductionAt T) : SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf hselect hquasi
    (constrainedExclusion_of_three_free_and_models hfree hmodels)

/-- All marked original rows now provide preparation. This owner retains
original row exhaustion and the containing-model reduction; the latter must
exclude the retained four-natural branch on its literal prepared action. -/
theorem constrainedExclusion_of_original_covers_and_models
    (hrows : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I → OriginalMovedCover D)
    (hmodels : LinearFiveReductionAt T) : ConstrainedExclusionAt T := by
  apply constrainedExclusion_of_preparation_and_models ?_ hmodels
  intro L D t v I c
  exact c.prepared_of_original_moved_cover (hrows L D t v I c)

/-- The original point-control application now discharges orbit preparation
for every marked source row, including four natural copies. The constrained
owner retains hrows and hmodels; the parent point-control owner retains the
other three source inputs. -/
theorem source_nonnormalPointControl_of_original_covers_and_models
    (hhalf : HalfSylowUniqueAt T) (hselect : SelectionAt T)
    (hquasi : QuasisimpleExclusionAt T)
    (hrows : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I → OriginalMovedCover D)
    (hmodels : LinearFiveReductionAt T) : SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf hselect hquasi
    (constrainedExclusion_of_original_covers_and_models hrows hmodels)

/-- All marked original rows reduce to four-natural covers and literal binary
containing quotients. Row exhaustion and the two binary exclusions remain
with qt-d-10-nona5-point-constrained. -/
theorem constrainedExclusion_of_original_covers_and_binary_components
    (hrows : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I → OriginalMovedCover D)
    (hbinary : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I → FourNaturalCover D →
      ∀ d, (d = 4 ∨ d = 5) → Nonempty ((I ⧸ pCore 2 I) ≃* SL(d,ZMod 2)) → False) :
    ConstrainedExclusionAt T := by
  intro hmany L D hminimal hnonA5 t v I hescape hnot hchar hr
  let c : Context D t v I := ⟨hmany,hminimal,hnonA5,hescape,hnot,hchar,hr⟩
  obtain ⟨hf,d,hd,hI⟩ := c.four_natural_and_binary_quotient_of_original_moved_cover
    (hrows L D t v I c)
  exact hbinary L D t v I c hf d hd hI

/-- The original point-control consumer with the four-natural A₇ cases
removed. The constrained owner retains the two displayed source obligations;
the parent point-control owner discharges the other three inputs. -/
theorem source_nonnormalPointControl_of_original_covers_and_binary_components
    (hhalf : HalfSylowUniqueAt T) (hselect : SelectionAt T)
    (hquasi : QuasisimpleExclusionAt T)
    (hrows : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I → OriginalMovedCover D)
    (hbinary : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I → FourNaturalCover D →
      ∀ d, (d = 4 ∨ d = 5) → Nonempty ((I ⧸ pCore 2 I) ≃* SL(d,ZMod 2)) → False) :
    SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf hselect hquasi
    (constrainedExclusion_of_original_covers_and_binary_components hrows hbinary)


/-- Every marked original row supplies the literal fully moved FF action on
one local fixed involution's orbit. The orbit detects the original VI kernel.
This is a reduction of the retained row, not its exclusion. -/
theorem Context.local_seed_classification_of_original_moved_cover
    {L : Subgroup G}
    {D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L}
    {t v : G} {I : Subgroup G} (c : Context D t v I) (h : OriginalMovedCover D) :
    ∃ u : G, ∃ hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G),
      u ≠ 1 ∧
      let H := pointJoin T v I
      let R := (conjugateSpanBy (zpowers u) I).subgroupOf H
      letI := (c.local_seed_orbit_reduced hu).normal
      letI := (c.local_seed_orbit_reduced hu).elementary
      let A := (I.subgroupOf H).map (ChapterB.InternalThompsonAction.actionMk R)
      let N := Representation.BinaryOffender.offenderSubgroup
        (ChapterB.InternalThompsonAction.action R)
      (∃ d, (d = 4 ∨ d = 5) ∧ Nonempty (A ≃* SL(d,ZMod 2))) ∧
      centralizer (R : Set H) = centralizer (internalModule D v I : Set H) ∧
      ChapterB.QuasisimpleSource.moved (ChapterB.InternalThompsonAction.action R) A = ⊤ ∧
      Representation.BinaryOffender.IsFFModule (V := Additive R) (ChapterB.InternalThompsonAction.action R) ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((ChapterB.InternalThompsonAction.action R).comp N.subtype) (A.subgroupOf N)) := by
  obtain ⟨u,hu,hne,_⟩ := c.local_seed_orbit_of_original_moved_cover h
  have hf := c.four_natural_of_original_moved_cover h
  exact ⟨u,hu,hne,c.local_seed_binary_actor_of_four_natural_cover hf hu hne,
    c.local_seed_centralizer_eq_of_four_natural_cover hf hu hne,
    c.local_seed_orbit_fully_moved_of_four_natural_cover hf hu hne,
    c.local_seed_ff_of_four_natural_cover hf hu hne⟩

/-- The constrained source conclusion reduced to the actual smaller FF
orbit. Original row exhaustion and exclusion of these local actions remain
with qt-d-10-nona5-point-constrained. -/
theorem constrainedExclusion_of_original_covers_and_local_seed_actions
    (hrows : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I → OriginalMovedCover D)
    (hlocal : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G) (c : Context D t v I), FourNaturalCover D →
      ∀ (u : G) (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G)),
      u ≠ 1 →
      let H := pointJoin T v I
      let R := (conjugateSpanBy (zpowers u) I).subgroupOf H
      letI := (c.local_seed_orbit_reduced hu).normal
      letI := (c.local_seed_orbit_reduced hu).elementary
      let A := (I.subgroupOf H).map (ChapterB.InternalThompsonAction.actionMk R)
      let N := Representation.BinaryOffender.offenderSubgroup
        (ChapterB.InternalThompsonAction.action R)
      (∃ d, (d = 4 ∨ d = 5) ∧ Nonempty (A ≃* SL(d,ZMod 2))) →
      ChapterB.QuasisimpleSource.moved (ChapterB.InternalThompsonAction.action R) A = ⊤ →
      Representation.BinaryOffender.IsFFModule (V := Additive R) (ChapterB.InternalThompsonAction.action R) →
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((ChapterB.InternalThompsonAction.action R).comp N.subtype) (A.subgroupOf N)) → False) :
    ConstrainedExclusionAt T := by
  intro hmany L D hminimal hnonA5 t v I hescape hnot hchar hr
  let c : Context D t v I := ⟨hmany,hminimal,hnonA5,hescape,hnot,hchar,hr⟩
  have h := hrows L D t v I c
  obtain ⟨u,hu,hne,hbinary,_,hm,hff,hclass⟩ := c.local_seed_classification_of_original_moved_cover h
  exact hlocal L D t v I c (c.four_natural_of_original_moved_cover h) u hu hne hbinary hm hff hclass

/-- Literal point-control application of the smaller-orbit classification.
The constrained owner retains row exhaustion and local-action exclusion;
qt-d-10-nona5-point-control retains the other three source inputs. -/
theorem source_nonnormalPointControl_of_original_covers_and_local_seed_actions
    (hhalf : HalfSylowUniqueAt T) (hselect : SelectionAt T)
    (hquasi : QuasisimpleExclusionAt T)
    (hrows : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I → OriginalMovedCover D)
    (hlocal : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G) (c : Context D t v I), FourNaturalCover D →
      ∀ (u : G) (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G)),
      u ≠ 1 →
      let H := pointJoin T v I
      let R := (conjugateSpanBy (zpowers u) I).subgroupOf H
      letI := (c.local_seed_orbit_reduced hu).normal
      letI := (c.local_seed_orbit_reduced hu).elementary
      let A := (I.subgroupOf H).map (ChapterB.InternalThompsonAction.actionMk R)
      let N := Representation.BinaryOffender.offenderSubgroup
        (ChapterB.InternalThompsonAction.action R)
      (∃ d, (d = 4 ∨ d = 5) ∧ Nonempty (A ≃* SL(d,ZMod 2))) →
      ChapterB.QuasisimpleSource.moved (ChapterB.InternalThompsonAction.action R) A = ⊤ →
      Representation.BinaryOffender.IsFFModule (V := Additive R) (ChapterB.InternalThompsonAction.action R) →
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((ChapterB.InternalThompsonAction.action R).comp N.subtype) (A.subgroupOf N)) → False) :
    SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf hselect hquasi
    (constrainedExclusion_of_original_covers_and_local_seed_actions hrows hlocal)

/-- Every marked original row supplies the actual local orbit with only a
single natural, orthogonal-cover or ten-dimensional irreducible action.
The entire original VI kernel is still detected by this smaller orbit. -/
theorem Context.single_local_action_of_original_moved_cover
    {L : Subgroup G}
    {D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L}
    {t v : G} {I : Subgroup G} (c : Context D t v I) (h : OriginalMovedCover D) :
    ∃ u : G, ∃ hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G),
      u ≠ 1 ∧
      let H := pointJoin T v I
      let R := (conjugateSpanBy (zpowers u) I).subgroupOf H
      letI := (c.local_seed_orbit_reduced hu).normal
      letI := (c.local_seed_orbit_reduced hu).elementary
      let A := (I.subgroupOf H).map (ChapterB.InternalThompsonAction.actionMk R)
      centralizer (R : Set H) = centralizer (internalModule D v I : Set H) ∧
      BinarySingleOrbitAction (ChapterB.InternalThompsonAction.action R) A := by
  obtain ⟨u,hu,hne,_⟩ := c.local_seed_orbit_of_original_moved_cover h
  have hf := c.four_natural_of_original_moved_cover h
  exact ⟨u,hu,hne,c.local_seed_centralizer_eq_of_four_natural_cover hf hu hne,
    c.local_seed_single_action_of_four_natural_cover hf hu hne⟩

/-- The original constrained contract now needs only the remaining single
local-orbit actions. Row exhaustion and their exclusion remain with this
same constrained owner; the natural--dual and higher repeated containing rows are discharged. -/
theorem constrainedExclusion_of_original_covers_and_single_local_actions
    (hrows : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I → OriginalMovedCover D)
    (hlocal : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G) (c : Context D t v I), FourNaturalCover D →
      ∀ (u : G) (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G)),
      u ≠ 1 →
      let H := pointJoin T v I
      let R := (conjugateSpanBy (zpowers u) I).subgroupOf H
      letI := (c.local_seed_orbit_reduced hu).normal
      letI := (c.local_seed_orbit_reduced hu).elementary
      let A := (I.subgroupOf H).map (ChapterB.InternalThompsonAction.actionMk R)
      BinarySingleOrbitAction (ChapterB.InternalThompsonAction.action R) A → False) :
    ConstrainedExclusionAt T := by
  intro hmany L D hminimal hnonA5 t v I hescape hnot hchar hr
  let c : Context D t v I := ⟨hmany,hminimal,hnonA5,hescape,hnot,hchar,hr⟩
  have h := hrows L D t v I c
  obtain ⟨u,hu,hne,_,ha⟩ := c.single_local_action_of_original_moved_cover h
  exact hlocal L D t v I c (c.four_natural_of_original_moved_cover h) u hu hne ha

/-- Literal point-control application of the reduced local-action list.
This task retains both displayed constrained source obligations; the parent
point-control owner retains the other three source inputs. -/
theorem source_nonnormalPointControl_of_original_covers_and_single_local_actions
    (hhalf : HalfSylowUniqueAt T) (hselect : SelectionAt T)
    (hquasi : QuasisimpleExclusionAt T)
    (hrows : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I → OriginalMovedCover D)
    (hlocal : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G) (c : Context D t v I), FourNaturalCover D →
      ∀ (u : G) (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G)),
      u ≠ 1 →
      let H := pointJoin T v I
      let R := (conjugateSpanBy (zpowers u) I).subgroupOf H
      letI := (c.local_seed_orbit_reduced hu).normal
      letI := (c.local_seed_orbit_reduced hu).elementary
      let A := (I.subgroupOf H).map (ChapterB.InternalThompsonAction.actionMk R)
      BinarySingleOrbitAction (ChapterB.InternalThompsonAction.action R) A → False) :
    SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf hselect hquasi
    (constrainedExclusion_of_original_covers_and_single_local_actions hrows hlocal)

/-- Original marked rows reduce to a local opposite point with an actual
irreducible SL₅(2) orbit. The arbitrary-point binary-four branches and the
augmentation cover have been discharged. Original row exhaustion and the
localized five/ten-dimensional endgame remain with this constrained owner. -/
theorem constrainedExclusion_of_original_covers_and_local_point_five
    (hrows : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I → OriginalMovedCover D)
    (hlocal : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t w : G) (J : Subgroup G) (c : Context D t w J), FourNaturalCover D →
      w ∈ (⁅D.moduleSubgroup,L⁆).map (MulAut.conj t).toMonoidHom →
      pointSylow T w = (T : Subgroup G) ⊓ normalizer (L : Set G) →
      ∀ (u : G) (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T w : Set G)),
      u ≠ 1 →
      let H := pointJoin T w J
      let U := (conjugateSpanBy (zpowers u) J).subgroupOf H
      letI := (c.local_seed_orbit_reduced hu).normal
      letI := (c.local_seed_orbit_reduced hu).elementary
      let A := (J.subgroupOf H).map (ChapterB.InternalThompsonAction.actionMk U)
      centralizer (U : Set H) = centralizer (internalModule D w J : Set H) →
      Nonempty (A ≃* SL(5,ZMod 2)) → A = ⊤ →
      Representation.IsIrreducible ((ChapterB.InternalThompsonAction.action U).comp A.subtype) →
      (Module.finrank (ZMod 2) (Additive U) = 5 ∨ Module.finrank (ZMod 2) (Additive U) = 10) → False) :
    ConstrainedExclusionAt T := by
  intro hmany L D hminimal hnonA5 t v I hescape hnot hchar hr
  let c : Context D t v I := ⟨hmany,hminimal,hnonA5,hescape,hnot,hchar,hr⟩
  have h := hrows L D t v I c
  have hf := c.four_natural_of_original_moved_cover h
  obtain ⟨u,hu,hne,_⟩ := c.local_seed_orbit_of_original_moved_cover h
  obtain ⟨J,c',hw,hs,hu',hc,hE,ht,hi,hd⟩ := c.local_binary_five_of_four_natural_cover hf hu hne
  exact hlocal L D t ((MulAut.conj t) u) J c' hf hw hs u hu' hne hc hE ht hi hd

/-- Literal point-control application of the reselected binary-five action.
The constrained owner retains row exhaustion and the localized parabolic
endgame; the parent point-control owner retains the three earlier inputs. -/
theorem source_nonnormalPointControl_of_original_covers_and_local_point_five
    (hhalf : HalfSylowUniqueAt T) (hselect : SelectionAt T)
    (hquasi : QuasisimpleExclusionAt T)
    (hrows : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I → OriginalMovedCover D)
    (hlocal : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t w : G) (J : Subgroup G) (c : Context D t w J), FourNaturalCover D →
      w ∈ (⁅D.moduleSubgroup,L⁆).map (MulAut.conj t).toMonoidHom →
      pointSylow T w = (T : Subgroup G) ⊓ normalizer (L : Set G) →
      ∀ (u : G) (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T w : Set G)),
      u ≠ 1 →
      let H := pointJoin T w J
      let U := (conjugateSpanBy (zpowers u) J).subgroupOf H
      letI := (c.local_seed_orbit_reduced hu).normal
      letI := (c.local_seed_orbit_reduced hu).elementary
      let A := (J.subgroupOf H).map (ChapterB.InternalThompsonAction.actionMk U)
      centralizer (U : Set H) = centralizer (internalModule D w J : Set H) →
      Nonempty (A ≃* SL(5,ZMod 2)) → A = ⊤ →
      Representation.IsIrreducible ((ChapterB.InternalThompsonAction.action U).comp A.subtype) →
      (Module.finrank (ZMod 2) (Additive U) = 5 ∨ Module.finrank (ZMod 2) (Additive U) = 10) → False) :
    SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf hselect hquasi
    (constrainedExclusion_of_original_covers_and_local_point_five hrows hlocal)

/-- All marked source rows, including the four-natural row, are now excluded.
The original marked-row exhaustion remains with this constrained owner. -/
theorem constrainedExclusion_of_original_covers
    (hrows : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I → OriginalMovedCover D) :
    ConstrainedExclusionAt T :=
  constrainedExclusion_of_original_covers_and_four_natural hrows
    (fun _ _ _ _ _ c h => c.no_fourNaturalCover h)

/-- Literal point-control application with every constrained marked-row
exclusion discharged. This owner retains only original row exhaustion;
qt-d-10-nona5-point-control retains the other three source inputs. -/
theorem source_nonnormalPointControl_of_original_covers
    (hhalf : HalfSylowUniqueAt T) (hselect : SelectionAt T)
    (hquasi : QuasisimpleExclusionAt T)
    (hrows : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I → OriginalMovedCover D) :
    SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf hselect hquasi
    (constrainedExclusion_of_original_covers hrows)

/-- Original group recognition reduces marked-row exhaustion to the two
remaining actual quotient families. Their moved-module markings remain
with this owner; no later generation or small-offender theorem is used. -/
theorem constrainedExclusion_of_binary_three_and_suzuki_covers
    (hbinary : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I →
      Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) → OriginalMovedCover D)
    (hsuzuki : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I →
      ∀ m : ℕ, 0 < m →
        Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) →
          OriginalMovedCover D) : ConstrainedExclusionAt T := by
  apply constrainedExclusion_of_original_covers
  intro L D t v I c
  rcases c.original_component_alternatives with hb | ⟨m,hm,hs⟩
  · exact hbinary L D t v I c hb
  · exact hsuzuki L D t v I c m hm hs

/-- Literal point-control application of the original two-family reduction.
Only moved-module recognition remains in the constrained branch; the parent
point-control owner retains the other three source inputs. -/
theorem source_nonnormalPointControl_of_binary_three_and_suzuki_covers
    (hhalf : HalfSylowUniqueAt T) (hselect : SelectionAt T)
    (hquasi : QuasisimpleExclusionAt T)
    (hbinary : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I →
      Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) → OriginalMovedCover D)
    (hsuzuki : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I →
      ∀ m : ℕ, 0 < m →
        Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) →
          OriginalMovedCover D) : SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf hselect hquasi
    (constrainedExclusion_of_binary_three_and_suzuki_covers hbinary hsuzuki)

/-- Original A₇ exclusion and binary moved-action recognition restrict the
binary-three marking obligation to actual SL₄(2)/SL₅(2) containing quotients
and the bounded literal VI. Both remaining original-row constructions are
still owned here; this conditional reduction does not assert exhaustion. -/
theorem constrainedExclusion_of_binary_containing_and_suzuki_covers
    (hbinary : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G) (c : Context D t v I),
      Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) →
      ∀ d : ℕ, (d = 4 ∨ d = 5) → Nonempty ((I ⧸ pCore 2 I) ≃* SL(d,ZMod 2)) →
      (letI := c.reduced.elementary;
        Module.finrank (ZMod 2) (Additive (internalModule D v I)) ≤ 20) →
      OriginalMovedCover D)
    (hsuzuki : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I →
      ∀ m : ℕ, 0 < m →
        Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) →
          OriginalMovedCover D) : ConstrainedExclusionAt T := by
  apply constrainedExclusion_of_binary_three_and_suzuki_covers _ hsuzuki
  intro L D t v I c he
  have a := c.actionFacts_of_binary_three_quotient he.some
  obtain ⟨d,hd,hI⟩ := c.original_containing_binary_quotient a
  exact hbinary L D t v I c he d hd hI (c.original_orbit_finrank_le_twenty a)

/-- Literal point-control application of the original binary containing-action
reduction. The two original-row constructions remain in the constrained
owner; the other three source inputs retain their parent assembly owner. -/
theorem source_nonnormalPointControl_of_binary_containing_and_suzuki_covers
    (hhalf : HalfSylowUniqueAt T) (hselect : SelectionAt T)
    (hquasi : QuasisimpleExclusionAt T)
    (hbinary : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G) (c : Context D t v I),
      Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) →
      ∀ d : ℕ, (d = 4 ∨ d = 5) → Nonempty ((I ⧸ pCore 2 I) ≃* SL(d,ZMod 2)) →
      (letI := c.reduced.elementary;
        Module.finrank (ZMod 2) (Additive (internalModule D v I)) ≤ 20) →
      OriginalMovedCover D)
    (hsuzuki : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I →
      ∀ m : ℕ, 0 < m →
        Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) →
          OriginalMovedCover D) : SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf hselect hquasi
    (constrainedExclusion_of_binary_containing_and_suzuki_covers hbinary hsuzuki)

/-- The original binary module is either at least nine-dimensional or has an
actual Steinberg marking, with its full/local comparison proved. Both remaining
binary exclusions and the Suzuki marking are still discharged by this owner. -/
theorem constrainedExclusion_of_large_binary_steinberg_and_suzuki
    (hlarge : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G) (_c : Context D t v I),
      Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) →
      (letI := source_original_full_moved_elementary D;
        9 ≤ Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G))) →
      OriginalMovedCover D)
    (hsteinberg : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G) (_c : Context D t v I)
      (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group),
      Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
        (BinaryLinearThree.S.comp
          (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) →
      D.fullModule = D.moduleSubgroup →
      ⁅D.fullModule,L⁆ ≤ orbitModule D v I → False)
    (hsuzuki : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I →
      ∀ m : ℕ, 0 < m →
        Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) →
          OriginalMovedCover D) : ConstrainedExclusionAt T := by
  apply constrainedExclusion_of_binary_three_and_suzuki_covers _ hsuzuki
  intro L D t v I c he
  let := source_original_full_moved_elementary D
  by_cases hd : 9 ≤ Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G))
  · exact hlarge L D t v I c he hd
  · have hsmall : Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) < 9 := by omega
    exact (hsteinberg L D t v I c he.some
      (c.original_small_binary_steinberg he.some hsmall).some
      (c.original_small_binary_full_eq_local he.some hsmall)
      (c.original_small_binary_moved_le he.some hsmall)).elim

/-- Literal point control from the original small/large binary reduction and
Suzuki recognition. The three other source inputs retain their parent owner. -/
theorem source_nonnormalPointControl_of_large_binary_steinberg_and_suzuki
    (hhalf : HalfSylowUniqueAt T) (hselect : SelectionAt T)
    (hquasi : QuasisimpleExclusionAt T)
    (hlarge : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G) (_c : Context D t v I),
      Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) →
      (letI := source_original_full_moved_elementary D;
        9 ≤ Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G))) →
      OriginalMovedCover D)
    (hsteinberg : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G) (_c : Context D t v I)
      (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group),
      Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
        (BinaryLinearThree.S.comp
          (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) →
      D.fullModule = D.moduleSubgroup →
      ⁅D.fullModule,L⁆ ≤ orbitModule D v I → False)
    (hsuzuki : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I →
      ∀ m : ℕ, 0 < m →
        Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) →
          OriginalMovedCover D) : SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf hselect hquasi
    (constrainedExclusion_of_large_binary_steinberg_and_suzuki hlarge hsteinberg hsuzuki)

/-- The original Steinberg alternative is discharged. Only the larger binary
moved-module rows and the Suzuki row remain with this constrained owner. -/
theorem constrainedExclusion_of_large_binary_and_suzuki
    (hlarge : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G) (_c : Context D t v I),
      Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) →
      (letI := source_original_full_moved_elementary D;
        9 ≤ Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G))) →
      OriginalMovedCover D)
    (hsuzuki : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I →
      ∀ m : ℕ, 0 < m →
        Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) →
          OriginalMovedCover D) : ConstrainedExclusionAt T := by
  apply constrainedExclusion_of_original_covers
  intro L D t v I c
  rcases c.original_local_natural_or_suzuki with ⟨e,_⟩ | ⟨m,hm,he⟩
  · exact hlarge L D t v I c ⟨e⟩ (c.original_binary_finrank_ge_nine e)
  · exact hsuzuki L D t v I c m hm he

/-- Literal point control with the original Steinberg case excluded. The
larger binary and Suzuki markings remain here, while the other three source
inputs retain their parent point-control assembly owner. -/
theorem source_nonnormalPointControl_of_large_binary_and_suzuki
    (hhalf : HalfSylowUniqueAt T) (hselect : SelectionAt T)
    (hquasi : QuasisimpleExclusionAt T)
    (hlarge : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G) (_c : Context D t v I),
      Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) →
      (letI := source_original_full_moved_elementary D;
        9 ≤ Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G))) →
      OriginalMovedCover D)
    (hsuzuki : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I →
      ∀ m : ℕ, 0 < m →
        Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) →
          OriginalMovedCover D) : SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf hselect hquasi
    (constrainedExclusion_of_large_binary_and_suzuki hlarge hsuzuki)

/-- The original binary branch, including its local parabolic endgame, is
fully discharged. Only exclusion of the actual Suzuki quotient remains in
this constrained owner; no binary moved-row exhaustion is required. -/
theorem constrainedExclusion_of_suzuki
    (hsuzuki : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I →
      ∀ m : ℕ, 0 < m →
        Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) →
          False) : ConstrainedExclusionAt T := by
  intro hmany L D hminimal hnonA5 t v I hescape hnot hchar hr
  let c : Context D t v I := ⟨hmany,hminimal,hnonA5,hescape,hnot,hchar,hr⟩
  obtain ⟨m,hm,he⟩ := c.original_suzuki_quotient
  exact hsuzuki L D t v I c m hm he

/-- Literal point-control application with the original binary-three branch
excluded. The Suzuki exclusion remains here; the three earlier source inputs
retain their existing point-control producers. -/
theorem source_nonnormalPointControl_of_suzuki
    (hhalf : HalfSylowUniqueAt T) (hselect : SelectionAt T)
    (hquasi : QuasisimpleExclusionAt T)
    (hsuzuki : ∀ (L : Subgroup G)
      (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G), Context D t v I →
      ∀ m : ℕ, 0 < m →
        Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) →
          False) : SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf hselect hquasi
    (constrainedExclusion_of_suzuki hsuzuki)

/-- Original 10.2.9, constrained branch: exclude every nonquasisimple
escaping component on the literal reduced orbit supplied by point control.
All preparation, containing-action and parabolic alternatives are discharged. -/
theorem constrainedExclusion (T : Sylow 2 G) : ConstrainedExclusionAt T := by
  apply constrainedExclusion_of_suzuki
  intro L D t v I c m hm he
  exact c.no_original_suzuki m hm he.some

/-- Apply the complete constrained exclusion to the actual nonnormal
point-control contract. Only the three independent earlier source inputs
owned by the parent point-control task remain explicit. -/
theorem source_nonnormalPointControl_of_remaining_sourceSteps
    (hhalf : HalfSylowUniqueAt T) (hselect : SelectionAt T)
    (hquasi : QuasisimpleExclusionAt T) : SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf hselect hquasi (constrainedExclusion T)

end CFSG.Quasithin.Chapter10.PointControl.Constrained
