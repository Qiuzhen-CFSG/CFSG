module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometrySylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryWeakClosure
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryClosure

/-!
# The field-space normalizer closure for n > 2 on the original layer

Choose the ambient Sylow using the two-primary field witness. Thompson
control supplies the full-normalizer Sylow and characteristic two. The
field-plane A₂ exclusion supplies the zeroth weak-closure bound. These
prove all premises of the corrected G.2.2 application, so the literal
normalizer closure is elementary abelian, reduced modulo U in N_G(U)/U,
and centralized modulo U by O₂(N_G(U)).

Source: Aschbacher–Smith, 6.1.14(4), printed p.671. The subsequent
local-component identification and residual normality remain with
qt-d-1222-rankone-recognition-natural-contained.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G} {n : ℕ}

/-- Source 6.1.14(4) for n > 2, with every Sylow, characteristic-two and
weak-closure premise discharged on the original Chapter12 layer. -/
theorem source_field_fixedSpace_closure
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n) (hUne : U ≠ ⊥) (hn : 2 < n) :
    ∃ P : Sylow 2 G,
      (P : Subgroup G) ≤ normalizer (L : Set G) ∧ commutatorLayer T L ≤ P ∧
      (P : Subgroup G) ≤ normalizer (commutatorLayer T L : Set G) ∧
      (∃ R : Sylow 2 (normalizer (U : Set G)),
        (R : Subgroup (normalizer (U : Set G))).map (normalizer (U : Set G)).subtype =
          (P : Subgroup G) ⊓ normalizer (U : Set G)) ∧
      fieldModuleClosure (commutatorLayer T L) U ≤
        (P : Subgroup G) ⊓ centralizer (U : Set G) ∧
      IsElementaryAbelian 2 (fieldModuleClosure (commutatorLayer T L) U) ∧
      IsPReduced 2 (fieldModuleClosureQuotient (commutatorLayer T L) U) ∧
      ⁅(normalizer (U : Set G)).pCoreIn 2,
        fieldModuleClosure (commutatorLayer T L) U⁆ ≤ U := by
  obtain ⟨P, hPL, hBP, hPB, _, _, _, hSyl, _, hHe, _⟩ :=
    source_field_fixedSpace_sylow_geometry D h h611 hnatural hfield hUne
  have hweak := source_field_fixedSpace_weak_closure D h h611 hnatural hfield hUne
    P hPB (i := 0) (by omega)
  obtain ⟨hR, hEl, hRed, hCore⟩ := source_field_closure_of_relative_sylow
    h611 hnatural hfield hUne hn P hBP hPL hPB hSyl hHe (hweak.trans inf_le_right)
  exact ⟨P, hPL, hBP, hPB, hSyl, hR, hEl, hRed, hCore⟩
end CFSG.Quasithin.Chapter12.Section02.RankOneModule
