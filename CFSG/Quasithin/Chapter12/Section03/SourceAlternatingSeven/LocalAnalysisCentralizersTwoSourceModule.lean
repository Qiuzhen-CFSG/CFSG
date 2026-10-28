module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersTwoSourceComponents
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperNatural
public import Theory.Representation.BinaryConjugationSection.FaithfulCommutant
public import Theory.Representation.BinaryPermutation.FiveCentralExtension.OuterCompatibility
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan

/-!
# The literal omega span and the A₅ commutant

B.2.14 makes U=⟨Ω₁Z(T)^{C_G(e)}⟩ reduced in the actual point centralizer.
The original K/O₂(K) action has trivial automorphism commutant on [V,K].
Thus any element of its section centralizer preserving [V,K] fixes it.
The B.5 equality [U,K]=[V,K] supplies this invariance once K is normal.

The LocalAnalysis application retains precisely proper quasisimple model
recognition and that B.5 equality. Both remain with
qt-d-1236-1238-point-centralizers before qt-d-1231-local-analysis assembly;
this conditional result does not assert the completed 12.3.8.
Source: Aschbacher–Smith, B.2.14, B.5.1, B.5.6 and 12.3.8, p.810.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Subgroup Theory.GroupTheory Section02 BinarySevenCode BinaryPermutation
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
variable {E : S.NaturalCoordinates}
namespace SylowNormalizer.Points
variable (P : Points E)

/-- Every actual section-centralizer actor preserving the moved A₅ space
fixes that space, through the literal K/O₂(K) action. -/
theorem two_section_fixes_moved_of_normalizes
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ChapterA.Section04.twoSectionCentralizer P.five
      (centralizer ({(P.two : G)} : Set G)) ≤ normalizer ((⁅V,P.five⁆ : Subgroup G) : Set G)) :
    ChapterA.Section04.twoSectionCentralizer P.five
      (centralizer ({(P.two : G)} : Set G)) ≤ centralizer ((⁅V,P.five⁆ : Subgroup G) : Set G) := by
  let d := P.five_moved_natural
  refine d.centralizes_of_faithful_trivial_commutant ?_ _ hn ?_
  · intro f hf
    apply LinearEquiv.ext
    intro w
    apply FiveCentralExtension.core_commuting_eq_id f.toLinearMap ?_ f.injective w
    intro g hg v
    obtain ⟨k,hk⟩ := (P.fiveCoreEquiv.surjective.comp
      (QuotientGroup.mk'_surjective (pCore 2 P.five))) ⟨g,hg⟩
    have he := hf k v
    change f (alternatingCoreRepresentation (Fin 5)
      (P.fiveCoreEquiv (QuotientGroup.mk' _ k)) v) =
      alternatingCoreRepresentation (Fin 5) (P.fiveCoreEquiv (QuotientGroup.mk' _ k)) (f v) at he
    change P.fiveCoreEquiv (QuotientGroup.mk' (pCore 2 P.five) k) = ⟨g,hg⟩ at hk
    rw [hk] at he
    exact he
  · have hcore : P.five.pCoreIn 2 ≤ (P.five ⊔ (T : Subgroup G)).pCoreIn 2 :=
      pCoreIn_mono_of_normalizes le_sup_left (sup_le P.five.le_normalizer
        (pointResidual_normalized S.chosen.sylow_normalizes_component P.two_central))
    have hfix : P.five.pCoreIn 2 ≤ centralizer ((⁅V,P.five⁆ : Subgroup G) : Set G) := by
      apply le_centralizer_iff.mp
      apply (P.five_moved_le_core_omega structural).trans
      exact (fun x hx => centralizer_le hcore ((mem_omegaCenterIn_iff _ _).mp hx).2.1)
    apply le_trans ?_ hfix
    rw [commutator_comm]
    exact ((ChapterA.Section04.le_twoSectionCentralizer_iff _ _ _).mp le_rfl).2.2

end SylowNormalizer.Points
namespace PointCentralizers

/-- Literal LocalAnalysis consumer of the two remaining source obligations:
the proper quasisimple model sieve and invariance of the moved module.
This task retains their discharge before the final owner can use this result. -/
def localAnalysis_of_quasisimple_models_and_moved_normalized
    (P : SylowNormalizer.Points E)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates)
    (models : ∀ Y : Subgroup G, Y ∈ Chapter1.LStar G (T : Subgroup G) →
      P.five < Y → IsQuasisimple (Y ⧸ pCore 2 Y) →
      ∃ W : Subgroup G, Nonempty (Setup T Y W))
    (hn : ChapterA.Section04.twoSectionCentralizer P.five
      (centralizer ({(P.two : G)} : Set G)) ≤ normalizer ((⁅V,P.five⁆ : Subgroup G) : Set G)) :
    S.LocalAnalysis :=
  localAnalysis_of_twoInput P structural
    ⟨P.two_normalizes_of_quasisimple_maximal_models structural escape natural models,
      P.two_section_fixes_moved_of_normalizes structural hn⟩

end PointCentralizers
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Subgroup Theory.GroupTheory Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
variable {E : S.NaturalCoordinates}
namespace SylowNormalizer.Points
variable (P : Points E)

/-- The literal U=⟨Ω₁Z(T)^{C_G(e)}⟩ of 12.3.8. -/
def twoOmegaSpan : Subgroup G :=
  conjugateSpanBy (omegaCenterIn (T : Subgroup G))
    (centralizer ({(P.two : G)} : Set G))

/-- B.2.14 for the actual weight-two point centralizer, with relative normality. -/
theorem twoOmegaSpan_reduced :
    IsPReduced 2 (P.twoOmegaSpan.subgroupOf
      (centralizer ({(P.two : G)} : Set G))) := by
  let H := centralizer ({(P.two : G)} : Set G)
  have hTH : (T : Subgroup G) ≤ H := fun t ht =>
    mem_centralizer_singleton_iff.mpr (P.two_central t ht)
  have hZT : omegaCenterIn (T : Subgroup G) ≤ (T : Subgroup G) :=
    fun _ hz => ((mem_omegaCenterIn_iff _ _).mp hz).1
  let R := T.subtype hTH
  have hz : Stellmacher.omegaOneCenterAmbient (R : Subgroup H) =
      (omegaCenterIn (T : Subgroup G)).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [← Stellmacher.omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le (hZT.trans hTH)]
    change Stellmacher.omegaOneCenterAmbient (((T : Subgroup G).subgroupOf H).map H.subtype) = _
    rw [map_subgroupOf_eq_of_le hTH]
    rfl
  have ho : orderOf (P.two : G) = 2 :=
    orderOf_eq_prime ((mem_omegaCenterIn_iff _ _).mp P.two_mem_omega).2.2 P.two_ne_one
  have hc := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (S.hypothesis.simpleQTKE.evenCharacteristic T)
      ⟨Chapter1.mem_H_of_isTwoLocal (isTwoLocal_involution_centralizer ho),hTH⟩)
  have hr := omegaCenter_normalClosure_reduced R hc
  rw [hz,normalClosure_subgroupOf_eq_conjugateSpanBy _ H (hZT.trans hTH)] at hr
  exact hr

/-- The remaining B.5 commutator equality implies invariance of the original
moved module under the whole point centralizer. -/
theorem two_moved_normalized_of_omegaSpan_commutator
    (hK : centralizer ({(P.two : G)} : Set G) ≤ normalizer (P.five : Set G))
    (hm : ⁅P.twoOmegaSpan,P.five⁆ = ⁅V,P.five⁆) :
    centralizer ({(P.two : G)} : Set G) ≤ normalizer ((⁅V,P.five⁆ : Subgroup G) : Set G) := by
  rw [← hm]
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq,map_commutator, twoOmegaSpan,
    mem_normalizer_iff_map_conj_eq.mp
      ((le_normalizer_conjugateSpanBy _ _) hg),
    mem_normalizer_iff_map_conj_eq.mp (hK hg)]

end SylowNormalizer.Points
namespace PointCentralizers

/-- Apply the rigidity and commutant arguments using precisely the literal
B.5 equality still required by the source proof. This task retains its proof. -/
def localAnalysis_of_quasisimple_models_and_omegaSpan
    (P : SylowNormalizer.Points E)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates)
    (models : ∀ Y : Subgroup G, Y ∈ Chapter1.LStar G (T : Subgroup G) →
      P.five < Y → IsQuasisimple (Y ⧸ pCore 2 Y) →
      ∃ W : Subgroup G, Nonempty (Setup T Y W))
    (hm : ⁅P.twoOmegaSpan,P.five⁆ = ⁅V,P.five⁆) : S.LocalAnalysis := by
  have hK := P.two_normalizes_of_quasisimple_maximal_models structural escape natural models
  exact localAnalysis_of_quasisimple_models_and_moved_normalized P structural escape natural models
    ((ChapterA.Section04.twoSectionCentralizer_le _ _).trans
      (P.two_moved_normalized_of_omegaSpan_commutator hK hm))

end PointCentralizers
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
