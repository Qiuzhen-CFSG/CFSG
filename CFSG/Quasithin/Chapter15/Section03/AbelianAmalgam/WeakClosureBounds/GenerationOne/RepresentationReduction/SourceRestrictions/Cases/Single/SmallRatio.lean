module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.ClassificationInputs
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Ratios
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity.Unitary
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio.FF
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio.Table

/-!
# Natural constituent recognition from the complete B.4 outputs

For a finite faithful binary action with quasisimple irreducible generalized
Fitting subgroup L and quadratic ratio at most two, the full B.4.5 output
has three branches. Its first branch supplies a genuine best offender on
the same action, so the full B.4.2 output applies. Its table is exhausted
row by row, and both boundary cases have quadratic ratio greater than two.

A connected E.2.2 marking of L/Z(L), at odd defining exponent greater than
one, and the explicit intermediate premise Z(L)=1 leave precisely the
natural SL₂, Suzuki, SL₃ and Sp₄ actions. Each witness keeps its group
isomorphism, binary linear equivalence and intertwining equation, together
with equality of the actual defining-field cardinality to the source 2^f.
In particular, SU₃ is treated on its actual natural module and is excluded
by its cubic center after recovering its fixed-field exponent.

The two universal classification implications are explicit earlier source
inputs. The caller must also discharge centerlessness and the central
quotient marking. This module proves their constituent-recognition
consequence, not the source classification implications or the later
Borel alignment, diagram movement, or F.9.18 orbit assertions.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), B.4.2/B.4.5,
printed pp.86--87, and the constituent deduction on printed p.1152.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
open scoped ENNReal

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio

universe u v
variable {D : Type u} [Group D] [Finite D] {V : Type v}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {𝒦 : GroupClass.{u}} (ρ : Representation (ZMod 2) D V) {f : ℕ}

/-- The complete three-branch B.4.5 deduction. The FF branch produces its
best offender using the cubic ratio, without replacing the input catalogue. -/
theorem natural_of_B45 (hB42 : FullB42.{u,v} 𝒦) (hyp : B4Hypotheses 𝒦 ρ)
    (h : B45Conclusion ρ) (hq : quadraticRatio ρ ≤ 2)
    (hs : SourceModel (generalizedFitting D ⧸ center (generalizedFitting D)) f)
    (hf : 1 < f) (ho : Odd f) (hz : center (generalizedFitting D) = ⊥) :
    NaturalConstituent ρ (generalizedFitting D) f := by
  cases h with
  | ff cubic =>
    obtain ⟨A, hA⟩ := hyp.exists_B42_of_cubic_le_one cubic
    exact natural_of_full_B42 ρ hs hf ho hz (hB42 D V ρ A hA)
  | table _ _ row => exact natural_of_table_B45 ρ hs hf ho hz hq row
  | boundary _ quadratic alternative =>
    cases alternative with
    | symplectic _ => exact (not_lt_of_ge hq quadratic).elim
    | jankoTwo _ _ => exact (not_lt_of_ge hq quadratic).elim

/-- Constituent recognition from the two unfiltered universal source inputs.
All intermediate premises are displayed on this exact action and its F*. -/
theorem natural_of_full_classification (hB42 : FullB42.{u,v} 𝒦)
    (hB45 : FullB45.{u,v} 𝒦) (hyp : B4Hypotheses 𝒦 ρ)
    (hq : quadraticRatio ρ ≤ 2)
    (hs : SourceModel (generalizedFitting D ⧸ center (generalizedFitting D)) f)
    (hf : 1 < f) (ho : Odd f) (hz : center (generalizedFitting D) = ⊥) :
    NaturalConstituent ρ (generalizedFitting D) f :=
  natural_of_B45 ρ hB42 hyp (hB45 D V ρ (hyp.with_quadratic_bound hq))
    hq hs hf ho hz

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio
