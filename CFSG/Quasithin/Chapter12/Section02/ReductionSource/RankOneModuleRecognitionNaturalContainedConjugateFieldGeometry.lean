module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryCentralizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryClosureSource

/-!
# Complete field-fixed-space geometry for the high-parameter branch

The arranged field witness and its centralizer formula complete the literal
FieldFixedSpaceGeometry contract. Thompson control provides the Sylow and
characteristic-two assertions; the rank calculation and A₂ exclusion supply
weak closure; corrected G.2.2 supplies the elementary, reduced closure in
N_G(U)/U. All clauses are proved here for n > 2, as required by the field
escape consumer. The local-component normality argument in 6.1.14(5)
remains with the contained-branch assembly owner.

Source: Aschbacher–Smith, 6.1.14(1–4), printed pp.670–671.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G} {n : ℕ}

/-- All source 6.1.14(1–4) clauses, with the actual actor and quotient. -/
theorem source_field_fixedSpace_geometry
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n) (hUne : U ≠ ⊥) (hn : 2 < n) :
    ∃ P : Sylow 2 G, FieldFixedSpaceGeometry L (normalizer (L : Set G))
      (commutatorLayer T L) U n P := by
  obtain ⟨P, hPL, hBP, hPB, hf, _, hCJ, hNS, hCS, hN, hC, _⟩ :=
    source_field_fixedSpace_sylow_geometry D h h611 hnatural hfield hUne
  have hzero := source_field_fixedSpace_weak_closure D h h611 hnatural hfield hUne
    P hPB (i := 0) (by omega)
  obtain ⟨_, hEl, hRed, hCore⟩ := source_field_closure_of_relative_sylow
    h611 hnatural hfield hUne hn P hBP hPL hPB hNS hN (hzero.trans inf_le_right)
  refine ⟨P, ⟨hPL, hBP, hPL, hPB, hfield.even, ?_, hCS, hNS, hCJ,
    hN, hC, hzero, ?_, hEl, hRed, hCore⟩⟩
  · obtain ⟨t, htP, htB, hU, hmark⟩ := hf
    exact ⟨t, htP, htB, hU,
      field_fixedSpace_centralizer_eq_sup hnatural hPL hPB t htP htB hU hUne hmark,
      hmark⟩
  · intro _
    exact source_field_fixedSpace_weak_closure D h h611 hnatural hfield hUne
      P hPB (i := 1) (by omega)

/-- The published geometry family, with no remaining geometric callbacks.
Its consumer is the local-component construction in source 6.1.14(5). -/
theorem source_fieldFixedSpaceGeometryFamily
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hn : 2 < n) :
    FieldFixedSpaceGeometryFamily L (normalizer (L : Set G)) (commutatorLayer T L) n := by
  intro U hUne _ hfield
  exact source_field_fixedSpace_geometry D h h611 hnatural hfield hUne hn

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
