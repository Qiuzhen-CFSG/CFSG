module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.Noncentrality
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.CharacteristicSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly

/-!
# Source field exclusions with characteristic pushing-up discharged

For the literal 13.6.18 and 13.6.19 consumers, the established 13.6.16
characteristic-normalizer obstruction yields the full residual chi-zero
block product. This removes the distinguished-pair and C.1.26 assumptions
from the minimal replacement and from all three higher-field branches.
The original quotient maps, seed actions, noncentrality input and earlier
source hypotheses are retained.

Source: Aschbacher–Smith C.1.26, printed p.132; 13.6.17–19, pp.930–931.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields
open ComponentSelection A5Module SourceContainment.RankTwo.LocalApplication
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
open RankOneBorel.Replacement.NaturalRecognition HigherFieldParabolics
open RankOneBorel.BorelGeometry.Placement
open SourceContainment.LinearThree.CentralAction.ModuleAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Source 13.6.19 for the three actual larger-field models. The source
seed and characteristic-two equality supply the core/module premises of
the constructed maximal-parabolic residual; no parabolic is an input. -/
theorem lemma_13_6_19_of_characteristic_source
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (classification : AdequateClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
        ∀ B : Subgroup D, B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (hv : orderOf v = 2)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hzOmega : z ∈ omegaOneCenterAmbient (Tv T v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    (h16 : ∀ D ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (D : Set G) → ¬ D ≤ centralizer ({z} : Set G) →
        CharacteristicNormalizerObstruction (Tv T v) D) :
    ¬ (Nonempty (plusImage K L T z v hL hz K ≃* SL(3, F)) ∨
      Nonempty (plusImage K L T z v hL hz K ≃* Theory.SpecificGroups.SymplecticFour.Sp F) ∨
      Nonempty (plusImage K L T z v hL hz K ≃* Atlas.G2.Model F)) := by
  have hU := Uv_le_coreOmega T z v hSylow hzOmega hf
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (Qv v)) :=
    omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 (Uv z v) := IsElementaryAbelian.of_le hU
  have hcore : Uv z v ≤ (Gv v).pCoreIn 2 := by
    intro x hx
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp (hU hx)).1
  intro hmodel
  obtain ⟨P, _, _, _, _, hnR, hmove, hlocal, hnonshort, _, _, _, hsqtk, hfR, hpar⟩ :=
    HigherFieldParabolics.Assembly.source_parabolic K L T z v hL hz
      classification hG hA36 hF hm hv hK hn hcore hSylow hf hW hmodel
  exact false_of_moving_nonshort_source T (residualIn P) z v
    hlocal hnR hmove h16 hsqtk hfR hpar hnonshort

section RankOne
variable {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
    (d : FlagSource T L V V₁ V₂) (M : Subgroup G)
    (hv : orderOf (markedV d.module) = 2)
    (hL : Tv (T : Subgroup G) (markedV d.module) ≤
      normalizer (Lv L (markedV d.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.module) ≤
      centralizer ({markedZ d.module} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (markedV d.module))
      (Gv (markedV d.module)))
    (hzOmega : markedZ d.module ∈
      Stellmacher.omegaOneCenterAmbient (Tv (T : Subgroup G) (markedV d.module)))
    (hf : generalizedFitting (Gv (markedV d.module)) = pCore 2 (Gv (markedV d.module)))
    (h14 : ∀ D ∈ Yz L (T : Subgroup G) (markedZ d.module) (markedV d.module),
      Tv (T : Subgroup G) (markedV d.module) ≤ normalizer (D : Set G))
    (h15 : ∀ (D : Subgroup G)
      (hD : D ∈ Yz L (T : Subgroup G) (markedZ d.module) (markedV d.module)),
      let := wk_elementary D L (T : Subgroup G) (markedZ d.module) (markedV d.module)
        hD.1.1 hSylow hzOmega hf
      ExcludesAlternatingFiveSeed D L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz)
    (h16 : ∀ D ∈ Chapter1.LIn (Gv (markedV d.module))
      (Tv (T : Subgroup G) (markedV d.module)),
      Tv (T : Subgroup G) (markedV d.module) ≤ normalizer (D : Set G) →
      ¬ D ≤ centralizer ({markedZ d.module} : Set G) →
      CharacteristicNormalizerObstruction (Tv (T : Subgroup G) (markedV d.module)) D)
    (h1324 : ChapterB.baumann (T : Subgroup G) ≤ Tv (T : Subgroup G) (markedV d.module))
    (h1325 : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M)
    (hMV : normalizer (V : Set G) ≤ M)
    (hBV : Mv M (markedV d.module) ≤ normalizer (V : Set G))
    (hlocal : (pResidual 2 (Mv M (markedV d.module))).map (Mv M (markedV d.module)).subtype ≤
      Lv L (markedV d.module) ⊔ (M ⊓ centralizer (V : Set G)))
    (standing : SourceHypothesis T L)
    (hA39 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ →
        cComponentLayer X = solvableResidual X)
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hidx : (Tv (T : Subgroup G) (markedV d.module)).relIndex (T : Subgroup G) = 2)
    (hzGlobal : markedZ d.module ∈ omegaOneCenterAmbient (T : Subgroup G))
    (classification : AdequateClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (hE23 : SourceFactors.SourceImplication.{u} KnownSimple.IsKnownSimple)
    (hBaum : SourceBaumannImplication.{u} KnownSimple.IsKnownSimple)

include standing hA39 h63 hidx hzGlobal hv hSylow hzOmega hf h14 h15 h16 h1324 h1325 hMV hBV hlocal
  classification hE23 hBaum

/-- Source 13.6.18 for the literal projective rank-one model. Universal
13.6.17 is proved here for every replacement in Y_z, and is not a premise. -/
theorem lemma_13_6_18_of_characteristic_source (K : Subgroup G)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.module) (markedV d.module))
    (F : BinaryField) :
    ¬ Nonempty (plusImage K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz K ≃*
      PSL(2, F.Carrier)) := by
  apply RankOneBorel.not_projective_rank_one_of_characteristic_source standing.qtke d M hv hL hz
    hSylow hzOmega hf h14 h15 h16 h1324 h1325 hMV hBV hlocal
    (classification := classification)
    (hE23 := hE23) (hBaum := hBaum) (h17 := ?_) K hK F
  intro D hD a hag ha
  exact noncentral_of_checkedSylow_conjugate T L D (markedZ d.module) (markedV d.module)
    standing hA39 h63 hD (h14 D hD) hSylow hidx (d.V_le_T (map_mem d.module _))
    (by rw [← hv]; exact pow_orderOf_eq_one _) hzGlobal (markedZ_ne_one d.module)
    hf a hag ha

/-- The equivalent actual linear rank-one exclusion in characteristic two. -/
theorem not_linear_rank_one_of_characteristic_source (K : Subgroup G)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.module) (markedV d.module))
    (F : BinaryField) :
    ¬ Nonempty (plusImage K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz K ≃*
      SL(2, F.Carrier)) := by
  rintro ⟨e⟩
  exact lemma_13_6_18_of_characteristic_source d M hv hL hz hSylow hzOmega hf h14 h15 h16
    h1324 h1325 hMV hBV hlocal standing hA39 h63 hidx hzGlobal
    classification hE23 hBaum K hK F
    ⟨e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL⟩

/-- A common source consumer of 13.6.17–19. The same selected component,
marked seed, quotient map and field occur in all three conclusions. -/
theorem source_noncentrality_and_field_exclusions_of_characteristic_source (K : Subgroup G)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.module) (markedV d.module))
    (hW : WK K L (T : Subgroup G) (markedZ d.module) (markedV d.module) ∈
      Chapter6.Source.reducedFamily (plusActor K L (T : Subgroup G) (markedV d.module)))
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
        ∀ B : Subgroup D, B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (F : BinaryField) :
    (∀ a : Tv (T : Subgroup G) (markedV d.module),
      (∃ g : G, (a : G) = MulAut.conj g (markedZ d.module)) →
      (checkedSylowMap (T : Subgroup G) (markedV d.module)).rangeRestrict a ∈
        center (checkedSylowMap (T : Subgroup G) (markedV d.module)).range →
      ¬ K ≤ centralizer ({(a : G)} : Set G)) ∧
    ¬ Nonempty (plusImage K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz K ≃*
      PSL(2, F.Carrier)) ∧
    (1 < F.degree →
      ¬ (Nonempty (plusImage K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz K ≃*
        SL(3, F.Carrier)) ∨
      Nonempty (plusImage K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz K ≃*
        Theory.SpecificGroups.SymplecticFour.Sp F.Carrier) ∨
      Nonempty (plusImage K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz K ≃*
        Atlas.G2.Model F.Carrier))) := by
  refine ⟨?_, ?_, ?_⟩
  · exact noncentral_of_checkedSylow_conjugate T L K (markedZ d.module) (markedV d.module)
      standing hA39 h63 hK (h14 K hK) hSylow hidx (d.V_le_T (map_mem d.module _))
      (by rw [← hv]; exact pow_orderOf_eq_one _) hzGlobal (markedZ_ne_one d.module) hf
  · exact lemma_13_6_18_of_characteristic_source d M hv hL hz hSylow hzOmega hf h14 h15 h16
      h1324 h1325 hMV hBV hlocal standing hA39 h63 hidx hzGlobal
      classification hE23 hBaum K hK F
  · intro hm
    exact lemma_13_6_19_of_characteristic_source K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz
      classification standing.qtke hA36 F.card_eq hm hv hK (h14 K hK)
      hSylow hzOmega hf hW h16

end RankOne
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields
