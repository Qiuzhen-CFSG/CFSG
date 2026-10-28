module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Exceptional

/-!
# The point-radical conclusion in degrees greater than two

The actual C.2.8 source specialization proves uniqueness over L when n>2,
hence centralizer control for every nonzero subgroup of the fixed center.
The existing fixed-line geometry and 11.0.4 residual and cubic clauses now
construct the genuine Cartan--TI pair. The proved center calculation and
exceptional block actions give invariance of the fixed summand and the
original radical-normalizer alternative.

There is no remaining local centralizer, pair or exceptional-action callback
in these degree-restricted results. The field-four SL3 local quotient
exclusion remains with qt-d-1222-natural-point-fixed-summand; the preceding
source inputs retain their flag/Cartan, preliminary, component and block
producers and final assembly owner qt-d-1222-natural-normalizer-source.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.5, printed pp.765--766, using 4.2.13, printed p.611.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02

open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
open Centralizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original Cartan--TI pair for every degree larger than two. Only
the permitted preceding fixed-line and 11.0.4 source inputs remain. -/
theorem pairConstruction_of_degree_ne_two
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hdegree : S.field.degree ≠ 2)
    (hline : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hres : ∀ p : ℕ, p.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    PairConstruction D S f := by
  apply Pair.pairConstruction_of_fixed_line_and_source_residuals D S f hline hres hcubic
  intro _ _ _ _ U hU hne
  exact fixedCenter_control_of_degree_ne_two D S hdegree (f.Ri 0) U hU hne

/-- The original fixed-summand conclusion for n>2, with the center
calculation, TI control and exceptional block actions all discharged. -/
theorem chosen_fixed_of_degree_ne_two
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hdegree : S.field.degree ≠ 2)
    (he : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L)
    (hn : Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0) (normalizer (L : Set G)))
    (hline : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hres : ∀ p : ℕ, p.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    normalizer (f.Ri 0 : Set G) ≤ normalizer (radicalFixedCenter (f.Ri 0) L : Set G) :=
  chosen_fixed_of_pair D S f he hb (PointCohomology.center_eq D S f hb) hn
    (pairConstruction_of_degree_ne_two D S f hdegree hline hres hcubic)

/-- Actual application to source 11.1.5 for n>2. The retained inputs belong
to the preceding flag/Cartan, preliminary, relative-component and block
producers, with final assembly in qt-d-1222-natural-normalizer-source.
The field-four SL3 branch remains with the fixed-summand owner. -/
theorem chosen_radicalAlternative_of_degree_ne_two
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hdegree : S.field.degree ≠ 2)
    (hn : Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0) (normalizer (L : Set G)))
    (hblocks : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L)
    (hline : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hres : ∀ p : ℕ, p.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree := by
  apply chosen_radicalAlternative_of_fixed_line_residuals_and_control D S f hn
    (fun he => PointBlocks.point_blocks_with_span D (hblocks he))
    (fun _ hb => PointCohomology.center_eq D S f hb) hline hres hcubic
  intro _ _ _ _ U hU hne
  exact fixedCenter_control_of_degree_ne_two D S hdegree (f.Ri 0) U hU hne

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
