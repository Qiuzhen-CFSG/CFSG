module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryClosure
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryQuotient
public import CFSG.Quasithin.Chapter1.Section01

/-!
# The normalizer closure of a field fixed space on the Chapter 12 layer

The actual quotient B/U supplies G.2.2's irreducibility hypothesis for
O²(N_L(U)). The relative Sylow arrangement, characteristic-two normalizer,
and zeroth weak-closure bound then give all closure conclusions of 6.1.14(4).
The quotient is the literal N_G(U)/U and the commutator uses its original
two-core. The earlier geometric premises remain explicit; their production
and the local-component argument belong to qt-d-1222-rankone-recognition-natural-contained.

Source: Aschbacher–Smith, 6.1.14(4), printed p.671.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L U : Subgroup G} {n : ℕ}

/-- The original quotient has no proper nonzero invariant subgroup under
the literal O²(N_L(U)); this discharges G.2.1's module premise. -/
theorem source_field_fixedSpace_invariant_interval
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n)
    (hUne : U ≠ ⊥) (hn : 2 < n) :
    U ≠ commutatorLayer T L ∧ ∀ A : Subgroup G,
      U ≤ A → A ≤ commutatorLayer T L →
      fieldLocalResidual L U ≤ normalizer (A : Set G) →
      A = U ∨ A = commutatorLayer T L :=
  field_fixedSpace_invariant_interval hnatural hfield hUne hn

/-- Source 6.1.14(4) on the original layer, retaining exactly its earlier
relative Sylow, characteristic-two, and weak-closure geometry. -/
theorem source_field_closure_of_relative_sylow
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n)
    (hUne : U ≠ ⊥) (hn : 2 < n)
    (P : Sylow 2 G) (hBP : commutatorLayer T L ≤ P)
    (hPL : (P : Subgroup G) ≤ normalizer (L : Set G))
    (hPB : (P : Subgroup G) ≤ normalizer (commutatorLayer T L : Set G))
    (hSyl : ∃ R : Sylow 2 (normalizer (U : Set G)),
      (R : Subgroup (normalizer (U : Set G))).map (normalizer (U : Set G)).subtype =
        (P : Subgroup G) ⊓ normalizer (U : Set G))
    (hHe : normalizer (U : Set G) ∈ Chapter1.He G)
    (hweak : Chapter6.Source.W (commutatorLayer T L)
      ((P : Subgroup G) ⊓ centralizer (U : Set G)) 0 ≤ centralizer (commutatorLayer T L : Set G)) :
    fieldModuleClosure (commutatorLayer T L) U ≤ (P : Subgroup G) ⊓ centralizer (U : Set G) ∧
      IsElementaryAbelian 2 (fieldModuleClosure (commutatorLayer T L) U) ∧
      IsPReduced 2 (fieldModuleClosureQuotient (commutatorLayer T L) U) ∧
      ⁅(normalizer (U : Set G)).pCoreIn 2, fieldModuleClosure (commutatorLayer T L) U⁆ ≤ U := by
  let : IsElementaryAbelian 2 (commutatorLayer T L) := h611.layer_elementary
  have hUB : U ≤ commutatorLayer T L := by
    obtain ⟨_, _, _, hU, _⟩ := hfield
    exact hU.le.trans inf_le_left
  have hBN : commutatorLayer T L ≤ normalizer (U : Set G) :=
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hUB)).trans (Subgroup.centralizer_le_normalizer _)
  have hRC : ((P : Subgroup G) ⊓ normalizer (U : Set G)) ⊓ centralizer (U : Set G) =
      (P : Subgroup G) ⊓ centralizer (U : Set G) := by
    rw [inf_assoc, inf_eq_right.mpr (Subgroup.centralizer_le_normalizer _)]
  have hchar := (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
    (Chapter1.mem_He_iff.mp hHe)
  have hh := field_closure_of_sylow_geometry
    ((P : Subgroup G) ⊓ normalizer (U : Set G)) hnatural hfield hn hUne
    (le_inf hBP hBN) inf_le_right (inf_le_left.trans hPB) (inf_le_left.trans hPL)
    hSyl hchar (by simpa only [hRC] using hweak)
  simpa only [hRC] using hh
end CFSG.Quasithin.Chapter12.Section02.RankOneModule
