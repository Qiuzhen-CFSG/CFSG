module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryComponents
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal

/-!
# The ordinary noncentrality consumer and its exact diagonal obligation

The preceding source reductions produce the actual faithful component K.
The terminal characteristic-two argument applies to J=K L₊ T and its
original moved module [R₂(J),K]. This file discharges the local containment,
characteristic-two and perfectness requirements and connects the resulting
plane noncentrality to the original F.9 application.

`OrdinaryDiagonalData` records the remaining geometric endgame: noncontainment,
the center-free quotient and outer two-group, the fixed centralizer residual,
and the direct core decomposition with its commutator bound. These are explicit
source obligations. In particular, the component module classification,
3.1.8(3) generation, Baumann escape and chief-factor count are not asserted here.
The earlier 13.3.2 list and guarded 3.1.8(1) also remain explicit. No F.9
hypothesis is used to prove its own plane-noncentrality input.

Source: Aschbacher–Smith, 13.3.14(e–g) and terminal paragraph, pp.892–893;
original 13.7 and F.9 application, pp.935–936.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]

/-- The remaining source geometry on the literal selected component and original actor. -/
structure OrdinaryDiagonalData (K A T : Subgroup G) : Prop where
  not_le : ¬ A ≤ K
  center_eq_bot : center (K ⧸ pCore 2 K) = ⊥
  outer_two : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K))
  residual_fixes : ∀ hn : A ≤ normalizer (K : Set G),
    Diagonal.centralizerResidual K A hn ≤
      centralizer (Diagonal.movedModule K A T : Set G)
  core_decomposition :
    ((Diagonal.localGroup K A T).pCoreIn 2 ⊓ centralizer (K : Set G)) ⊔
      Diagonal.movedModule K A T = (Diagonal.localGroup K A T).pCoreIn 2
  core_disjoint : Disjoint
    ((Diagonal.localGroup K A T).pCoreIn 2 ⊓ centralizer (K : Set G))
    (Diagonal.movedModule K A T)
  core_commutator : ⁅(Diagonal.localGroup K A T).pCoreIn 2,A⁆ ≤
    Diagonal.movedModule K A T

variable {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d

private theorem ordinary_diagonal_characteristic (K : Subgroup H) :
    Diagonal.localGroup (K.map H.subtype) (sourceOne L T P) T ∈ Chapter1.He G := by
  let J := Diagonal.localGroup (K.map H.subtype) (sourceOne L T P) T
  have hTH : (T : Subgroup G) ≤ H := d.first_normalizer ▸ d.line_stable
  have hJH : J ≤ H := sup_le
    (sup_le (map_subtype_le _) (ordinary_point_residual_le_point d)) hTH
  have hPT : P ≤ (T : Subgroup G) :=
    d.line_le_plane.trans (d.plane_le_seed.trans (d.seed_le.trans d.chosen.le_sylow))
  have hP : P ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le hPT) (hPT.trans le_sup_right)
    (hJH.trans d.first_normalizer.le)
  have hPn : P ≠ ⊥ := by intro he; have hh := d.line_card; simp [he] at hh
  exact Chapter1.lemma_1_1_4_6 T (d.counterexample.qtke.evenCharacteristic T)
    ⟨(fun he => hPn (bot_unique (he ▸ hP))),fun _ ht =>
      (show (T : Subgroup G) ≤ J from le_sup_right) ht⟩

/-- The remaining component-module and diagonal source input, on precisely
those components selected after reduction (d). This is an obligation of the
later source argument, not a consequence asserted by the present module. -/
def OrdinaryDiagonalSource : Prop :=
  ∀ K : Subgroup H, K.IsCComponent →
      IsComponent (Star H) (K.map (QuotientGroup.mk' (pCore 2 H))) →
      ⁅K.map (QuotientGroup.mk' (pCore 2 H)),
        (star H (sourceOne L T P) (ordinary_point_residual_le_point d)).pCoreIn 2⁆ ≠ ⊥ →
      (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H) →
      ⁅K,(sourceOne L T P).subgroupOf H⁆ = K → IsQuasisimple (K ⧸ pCore 2 K) →
      ⁅conjugateSpanBy U H,K.map H.subtype⁆ ≠ ⊥ →
      K.map H.subtype ∈ MainForward.faithfulLocalComponents T →
      OrdinaryDiagonalData (K.map H.subtype) (sourceOne L T P) T

/-- Exact ordinary 13.3.14 implication once its earlier and diagonal source obligations hold. -/
theorem ordinary_plane_noncentral_of_diagonal_source
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (h318 : Chapter3.GuardedSourceTheorem318One G)
    (hV : ¬IsMulCommutative (conjugateSpanBy V H))
    (hend : OrdinaryDiagonalSource d) :
    ⁅H.pCoreIn 2,E⁆ ≠ ⊥ := by
  intro hc
  obtain ⟨K,hK,hKs,hm,hn,hgen,hq,hU,hfaithful⟩ :=
    ordinary_faithful_component_of_guarded_sources d e h1221 h1332 h318 hV hc
  have b := hend K hK hKs hm hn hgen hq hU hfaithful
  have hnG : sourceOne L T P ≤ normalizer (K.map H.subtype : Set G) := by
    have hh := (map_mono hn).trans (K.le_normalizer_map H.subtype)
    rwa [map_subgroupOf_eq_of_le (ordinary_point_residual_le_point d)] at hh
  have hpK := Chapter1.Section02.Adequate.mem_L_isPPerfect
    ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T _).mp hfaithful).1
  exact Diagonal.contradiction_of_core_decomposition (K.map H.subtype) (sourceOne L T P) T
    hnG hpK ordinary_point_residual_twoPerfect b.center_eq_bot b.outer_two
    (ordinary_diagonal_characteristic d K) b.not_le (b.residual_fixes hnG)
    b.core_decomposition b.core_disjoint b.core_commutator

end CFSG.Quasithin.Chapter13.Section03.Noncentrality

namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion Section03.Noncentrality
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {E M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ E D.Vplus M D.Gz)

/-- Literal original F.9 consumer: the geometric diagonal source discharges
plane noncentrality in the abelian-seed, nonabelian-full-span branch. -/
theorem f9_of_diagonal_source
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (h1332 : SupercriticalSource.Source1332OneTwo D.T)
    (h318 : Chapter3.GuardedSourceTheorem318One G)
    (hV : ¬IsMulCommutative (conjugateSpanBy D.V D.Gz))
    (hH : D.H ∈ Section08.Source.Hz D.L₁ D.T D.Gz M)
    (hend : OrdinaryDiagonalSource d) : D.Hypothesis := by
  apply f9_of_plane_noncentral d e h1221 hH
  rw [←d.first_normalizer]
  exact ordinary_plane_noncentral_of_diagonal_source d e h1221 h1332 h318 hV hend
end CFSG.Quasithin.Chapter13.Section07.OrdinarySource
