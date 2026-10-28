module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.CanonicalGeometry.Qrc.OmegaIntersection
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.CanonicalGeometry.Qrc.RelativeNormalizer

/-!
# The canonical qrc configuration in 13.1.9

The unique Sylow two-subgroup of H∩O∞(L) is R∩L. Relative
normality of this intersection in H∩N_G(L) makes R∩L invariant there.
The canonical residual-normalizer identification then makes Y invariant.
Finally O²(YT)=Y supplies the actual residual in case (I), and the
proved nonzero reduced module supplies the remaining qrc clauses.
Neither normality of Y in all of N_G(L) nor supplement uniqueness is
assumed. The only earlier source premise is canonical starred membership;
its final discharge remains with qt-d-1317-source.

Source: Aschbacher--Smith 13.1.9, printed p.869.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
open Chapter1 Chapter1.Section02 Chapter12.Section02 Chapter1.RadicalActions
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

theorem comparison_normalizes_radical_intersection
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : Escape.CanonicalStars T) {L H : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    H ⊓ normalizer (L : Set G) ≤
      normalizer ((radicalSylowCentralizer T L ⊓ L : Subgroup G) : Set G) := by
  let D := H ⊓ (solvableRadical L).map L.subtype
  let S := radicalSylowCentralizer (T : Subgroup G) L ⊓ L
  let A := H ⊓ normalizer (L : Set G)
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hSD : S ≤ D := by
    rw [show S = (T : Subgroup G) ⊓ (solvableRadical L).map L.subtype from
      radicalSylowCentralizer_inf_component T hTL]
    exact inf_le_inf_right _ hH.1.1.2
  obtain ⟨P,hP⟩ := (radicalSylowCentralizer_inf_component_isSylow T hTL).restrict hSD inf_le_right
  have hi := comparison_radical_twoClosed h hmany hs hL hn hH
  let Q : Sylow 2 D := pCore_isPGroup.toSylow hi.not_two_dvd_nat
  have hPQ : (P : Subgroup D) = pCore 2 D :=
    Q.is_maximal' P.isPGroup' (pCore_isPGroup.le_sylow_of_normal P)
  have hcore : D.pCoreIn 2 = S := by
    change (pCore 2 D).map D.subtype = S
    rw [← hPQ,hP]
  have hAD : A ≤ normalizer (D : Set G) :=
    (le_inf (inf_le_left.trans H.le_normalizer)
      (inf_le_right.trans (normalizer_le_normalizer_characteristic_image L (solvableRadical L)))).trans
        inf_normalizer_le_normalizer_inf
  change A ≤ normalizer (S : Set G)
  rw [← hcore]
  exact hAD.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D))

theorem comparison_normalizes_canonical
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : Escape.CanonicalStars T) {L H : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    H ⊓ normalizer (L : Set G) ≤ normalizer (canonicalSupplement T L : Set G) :=
  normalizes_canonical_of_normalizes_radical_intersection h hmany hL hn inf_le_right
    (comparison_normalizes_radical_intersection h hmany hs hL hn hH)

theorem canonical_qrc_hypotheses
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : Escape.CanonicalStars T) {L H : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Chapter3.QrcHypotheses T (normalizer (L : Set G))
      (canonicalSupplement T L ⊔ (T : Subgroup G)) H (canonicalReducedModule T L) := by
  obtain ⟨hWM,_,hVW,hWV,he,hre,hcore⟩ := canonical_reduced_action h hmany hL hn
  refine ⟨le_sup_right,hWM,hH,hVW,hWV,he,hre,hcore,Or.inl ?_⟩
  rw [canonical_embedded_twoResidual h hmany hL hn]
  exact comparison_normalizes_canonical h hmany hs hL hn hH


end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
