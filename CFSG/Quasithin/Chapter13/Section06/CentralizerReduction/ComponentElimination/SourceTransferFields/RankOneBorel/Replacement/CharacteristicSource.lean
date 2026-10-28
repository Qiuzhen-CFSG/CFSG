module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.CharacteristicBlockSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition

/-!
# Minimal natural replacement from characteristic exclusion

The actual 13.6.16 obstruction excludes every nontrivial characteristic
Sylow subgroup from being normal. The complete chi-zero product theorem
therefore constructs the residual block orbit in the minimal local join.
Its distinguished local component is a factor; the existing natural-action
recognition then gives the original field degree and quotient marking.

Source: Aschbacher–Smith C.1.26, printed p.132, and 13.6.18, p.931.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement
open Subgroup Theory.GroupTheory ComponentSelection
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
open Matrix.SpecialLinearGroup.RankOneResidual
open HigherFieldParabolics NaturalRecognition MinimalGeometry
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
open scoped MatrixGroups IsMulCommutative

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The natural-module and minimal-block steps of 13.6.18, assembled on the
literal original and replacement actions. Minimality is in all of L(KT_v,T_v).
The block's subnormality is relative to K₀T_v, and the comparison of native
plus quotients preserves every representative in K₀. -/
theorem exists_minimal_natural_block_of_characteristic_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hzOmega : z ∈ Stellmacher.omegaOneCenterAmbient (Tv T v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hK : K ∈ Yz L T z v)
    (h14 : ∀ D ∈ Yz L T z v, Tv T v ≤ normalizer (D : Set G))
    (h15 : ∀ (D : Subgroup G) (hD : D ∈ Yz L T z v),
      let := wk_elementary D L T z v hD.1.1 hSylow hzOmega hf
      ExcludesAlternatingFiveSeed D L T z v hL hz)
    (h16 : ∀ D ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (D : Set G) → ¬ D ≤ centralizer ({z} : Set G) →
      CharacteristicNormalizerObstruction (Tv T v) D)
    (F : BinaryField) (e : plusImage K L T z v hL hz K ≃* SL(2, F.Carrier))
    (classification : AdequateClassificationInput.{u,u} KnownSimple.IsKnownSimple) :
    (let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf;
      Nonempty (NaturalSection (F := F.Carrier)
        (componentRepresentation K L T z v hL hz) (movingSpace K L T z v))) ∧
    ∃ (K₀ : Subgroup G) (hle : K₀ ≤ K) (hY : K₀ ∈ Yz L T z v),
      Minimal (fun D => D ∈ Chapter1.LIn (K ⊔ Tv T v) (Tv T v)) K₀ ∧
      starImage z v K₀ = starImage z v K ∧
      Tv T v ≤ normalizer (K₀ : Set G) ∧
      WK K₀ L T z v = WK K L T z v ∧
      ⁅WK K₀ L T z v, K₀⁆ = ⁅WK K L T z v, K⁆ ∧
      UX L z v (starImage z v K) = ⁅WK K₀ L T z v, K₀⁆ ∧
      ChapterC.IsBlock (K₀.subgroupOf (K₀ ⊔ Tv T v)) ∧
      ChapterC.IsL2EvenBlock K₀ F.degree ∧
      (∀ P : Sylow 2 (K₀ ⊔ Tv T v : Subgroup G),
        (P : Subgroup (K₀ ⊔ Tv T v : Subgroup G)).map (K₀ ⊔ Tv T v).subtype = Tv T v →
          ChapterB.IsMinimalParabolicOver P ⊤) ∧
      ∃ e₀ : plusImage K₀ L T z v hL hz K₀ ≃* SL(2, F.Carrier),
        (∀ k : K₀, e₀ (componentMap K₀ L T z v hL hz k) =
          e (componentMap K L T z v hL hz (inclusion hle k))) ∧
        (let := wk_elementary K₀ L T z v hY.1.1 hSylow hzOmega hf;
          Nonempty (NaturalSection (F := F.Carrier)
            (componentRepresentation K₀ L T z v hL hz) (movingSpace K₀ L T z v))) := by
  refine ⟨NaturalRecognition.Source.naturalSection hG K L T z v hv hL hz hSylow
    hzOmega hf hK (h14 K hK) F e classification (h15 K hK), ?_⟩
  obtain ⟨K₀, hle, hmin⟩ := exists_minimal_local K L T z v hK
  obtain ⟨he, hY, hn, hW, hU, hsqtk, hf₀, hpar⟩ :=
    minimal_local_geometry hG K₀ K L T z v hL hz hK hle hmin h14 hv hSylow hf e
  let e₀ := modelOfMinimal K₀ K L T z v hL hz hK hle hmin h14 e
  have hmove : ¬ K₀ ≤ centralizer ({z} : Set G) := by
    intro hc
    exact (invariant_component_consequences K₀ L T z v hY hn).1.2
      ((starPreimage_starImage_centralizes_seed_iff z v K₀ hY.1.1).mpr hc)
  obtain ⟨hb, htypes⟩ := block_alternatives_of_characteristic_obstruction
    (Tv T v) K₀ hY.1.2 hn (h16 K₀ hY.1 hn hmove) hsqtk hf₀ hpar
  have hwT : WK K₀ L T z v ≤ Tv T v := by
    have hw := (WK_le_Uv K₀ L T z v hY.1.1).trans
      (Uv_le_coreOmega T z v hSylow hzOmega hf)
    obtain ⟨P, hP⟩ := hSylow
    intro w hwK
    rw [← hP]
    exact pCoreIn_le_sylow (Gv v) P
      ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp (hw hwK)).1
  have ht := NaturalRecognition.Source.isL2EvenBlock hG K₀ L T z v hv hL hz hSylow
    hzOmega hf hY hn F e₀ classification (h15 K₀ hY)
    hwT hb htypes
  refine ⟨K₀, hle, hY, hmin, he, hn, hW, hU, ?_, hb, ht, hpar, e₀, ?_, ?_⟩
  · exact ((invariant_component_consequences K L T z v hK (h14 K hK)).2).trans hU.symm
  · exact modelOfMinimal_mk K₀ K L T z v hL hz hK hle hmin h14 e
  · exact NaturalRecognition.Source.naturalSection hG K₀ L T z v hv hL hz hSylow
      hzOmega hf hY hn F e₀ classification (h15 K₀ hY)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement

end
