module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryDiagonal
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal.AlternatingFiveSplit
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveQuotientCentralizer

/-!
# Residual centralization in the original A₅ diagonal endgame

The actual quotient centralizer fixes the deleted A₅ layer, since its binary
commutant consists only of scalars. Its two-residual therefore fixes the
original moved module W_K=[R₂(KL₊T),K]. The established block calculation
identifies that module with U(K), supplies its direct core complement, and
proves the required centerless quotient and two-group outer action.

The original selected-component consumer now retains only the preceding
source conclusions: A₅ block recognition, L₊ not contained in K, and the
chief-count bound [O₂(KL₊T),L₊]≤W_K. The earlier 13.3.2 hypothesis supplies
normalization by T, on that same component. Its application gives the literal
F.9 hypothesis without an independent residual, quotient, or splitting input.
These earlier source conclusions remain obligations of the source assembly.

Source: Aschbacher--Smith, 13.3.14, final paragraph on p.893, and the original
13.7/F.9 application on pp.935--936.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The actual quotient-action kernel fixes the deleted binary A₅ layer. -/
theorem alternatingFive_quotientCentralizer_fixes (K A : Subgroup G)
    (hK : ChapterC.IsAlternatingBlock K 5) (hn : A ≤ normalizer (K : Set G)) :
    Diagonal.quotientCentralizer K A hn ≤ centralizer ((ChapterC.blockU K).map K.subtype : Set G) :=
  hK.quotient_centralizer_le_blockU_centralizer
    ((Diagonal.quotientCentralizer_le K A hn).trans (sup_le K.le_normalizer hn))
    (Diagonal.quotientCentralizer_commutator_le_core K A hn)

/-- Its two-residual fixes the literal original reduced moved module. -/
theorem alternatingFive_residual_fixes (K A T : Subgroup G)
    (hK : ChapterC.IsAlternatingBlock K 5)
    (hn : A ≤ normalizer (K : Set G)) (hT : T ≤ normalizer (K : Set G)) :
    Diagonal.centralizerResidual K A hn ≤ centralizer (Diagonal.movedModule K A T : Set G) := by
  rw [Diagonal.movedModule_eq_of_alternatingFive K A T hK hn hT]
  exact (Diagonal.centralizerResidual_le K A hn).trans
    (alternatingFive_quotientCentralizer_fixes K A hK hn)

/-- An A₅ block supplies every residual, quotient and splitting conclusion
of the diagonal endgame. Noncontainment and the chief-count estimate remain. -/
theorem ordinaryDiagonalData_of_alternatingFive (K A T : Subgroup G)
    (hK : ChapterC.IsAlternatingBlock K 5)
    (hn : A ≤ normalizer (K : Set G)) (hT : T ≤ normalizer (K : Set G))
    (hout : ¬ A ≤ K)
    (hm : ⁅(Diagonal.localGroup K A T).pCoreIn 2,A⁆ ≤ Diagonal.movedModule K A T) :
    OrdinaryDiagonalData K A T := by
  have hq := Diagonal.quotient_data_of_alternatingFive K hK
  have hs := Diagonal.core_split_of_alternatingFive K A T hK hn hT
  exact ⟨hout,hq.1,hq.2,(fun hn' => alternatingFive_residual_fixes K A T hK hn' hT),
    hs.1,hs.2,hm⟩

variable {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)

/-- The earlier source conclusions still required for the selected original
component: A₅ block recognition, noncontainment, and the chief-count estimate. -/
def OrdinaryBlockSource : Prop :=
  ∀ K : Subgroup H, K.IsCComponent →
      IsComponent (Star H) (K.map (QuotientGroup.mk' (pCore 2 H))) →
      ⁅K.map (QuotientGroup.mk' (pCore 2 H)),
        (star H (sourceOne L T P) (ordinary_point_residual_le_point d)).pCoreIn 2⁆ ≠ ⊥ →
      (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H) →
      ⁅K,(sourceOne L T P).subgroupOf H⁆ = K → IsQuasisimple (K ⧸ pCore 2 K) →
      ⁅conjugateSpanBy U H,K.map H.subtype⁆ ≠ ⊥ →
      K.map H.subtype ∈ MainForward.faithfulLocalComponents T →
      ChapterC.IsAlternatingBlock (K.map H.subtype) 5 ∧
        ¬ sourceOne L T P ≤ K.map H.subtype ∧
        ⁅(Diagonal.localGroup (K.map H.subtype) (sourceOne L T P) T).pCoreIn 2,
          sourceOne L T P⁆ ≤ Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T

/-- The source family already gives Sylow normalization of the same component. -/
theorem ordinaryDiagonalSource_of_blocks
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (hb : OrdinaryBlockSource d) : OrdinaryDiagonalSource d := by
  intro K hK hKs hm hn hgen hq hU hf
  obtain ⟨hblock,hout,hcomm⟩ := hb K hK hKs hm hn hgen hq hU hf
  have hnG : sourceOne L T P ≤ normalizer (K.map H.subtype : Set G) := by
    have hh := (map_mono hn).trans (K.le_normalizer_map H.subtype)
    rwa [map_subgroupOf_eq_of_le (ordinary_point_residual_le_point d)] at hh
  exact ordinaryDiagonalData_of_alternatingFive _ _ _ hblock hnG (h1332 _ hf).1 hout hcomm

end CFSG.Quasithin.Chapter13.Section03.Noncentrality

namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion Section03.Noncentrality
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {E M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ E D.Vplus M D.Gz)

/-- The literal original F.9 consumer after the A₅ block and chief-count steps. -/
theorem f9_of_alternatingFive_block_source
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (h1332 : SupercriticalSource.Source1332OneTwo D.T)
    (h318 : Chapter3.GuardedSourceTheorem318One G)
    (hV : ¬IsMulCommutative (conjugateSpanBy D.V D.Gz))
    (hH : D.H ∈ Section08.Source.Hz D.L₁ D.T D.Gz M)
    (hb : OrdinaryBlockSource d) : D.Hypothesis :=
  f9_of_diagonal_source d e h1221 h1332 h318 hV hH
    (ordinaryDiagonalSource_of_blocks d h1332 hb)

end CFSG.Quasithin.Chapter13.Section07.OrdinarySource
