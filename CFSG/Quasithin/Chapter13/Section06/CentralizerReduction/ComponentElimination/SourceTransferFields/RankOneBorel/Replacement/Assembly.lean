module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MinimalGeometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition

/-!
# Natural coordinates and the minimal block replacement in 13.6.18

The universal adequate B.5 classifier and the exact earlier 13.6.15 exclusion
give natural coordinates on the original U_K/C_U_K(K). Independently, choose
a minimal member of the full local family L(KT_v,T_v). Rank-one image rigidity
preserves its star image and hence W_K and U_K, and constructs its native plus
model with the original quotient markings. Its actual join with T_v is minimal
parabolic, SQTK and of characteristic two.

Apply the full C.1.26 implication using 13.6.16(2). The local C-component
condition and the transitive Sylow action reduce the central product to this
component; perfectness removes A₃. The exact 13.6.15 module exclusion removes
A₅, and natural coordinates recover the original field degree. Thus no block,
replacement, naturality or field-exclusion premise is retained.

Only the specified earlier local conclusions and the genuine universal B.5
and C.1.26 implications remain inputs. The centralizer-reduction assembly
owns their discharge, using ComponentControl, ComponentModules/A5Borel and
CharacteristicNormalizers together with the Chapter B and C source owners.
Those local modules alone are not complete producers of all these premises.
The enclosing 13.6.18 assembly owns the subsequent Borel argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.18, printed p.931 (PDF p.948), first paragraph.
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

private theorem wk_le_sylow (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hzOmega : z ∈ Stellmacher.omegaOneCenterAmbient (Tv T v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v)) :
    WK K L T z v ≤ Tv T v := by
  have hw := (WK_le_Uv K L T z v hK).trans
    (Uv_le_coreOmega T z v hSylow hzOmega hf)
  obtain ⟨P, hP⟩ := hSylow
  intro w hwK
  have hc := ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp (hw hwK)).1
  rw [← hP]
  exact pCoreIn_le_sylow (Gv v) P hc

/-- The natural-module and minimal-block steps of 13.6.18, assembled on the
literal original and replacement actions. Minimality is in all of L(KT_v,T_v).
The block's subnormality is relative to K₀T_v, and the comparison of native
plus quotients preserves every representative in K₀. -/
theorem exists_minimal_natural_block {𝒦 : GroupClass.{u}}
    (hG : IsSimpleQTKE 𝒦 G)
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
    (classification : AdequateClassificationInput.{u,u} 𝒦)
    (choices : DistinguishedPairs.{u}) (pushingUp : C126Source 𝒦 choices) :
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
  obtain ⟨he, hY, hn, hW, hU, _, _, hpar⟩ :=
    minimal_local_geometry hG K₀ K L T z v hL hz hK hle hmin h14 hv hSylow hf e
  let e₀ := modelOfMinimal K₀ K L T z v hL hz hK hle hmin h14 e
  obtain ⟨hb, htypes⟩ := block_alternatives_of_minimal_source choices pushingUp hG
    K₀ K L T z v hL hz hK hle hmin h14 h16 hv hSylow hf e
  have ht := NaturalRecognition.Source.isL2EvenBlock hG K₀ L T z v hv hL hz hSylow
    hzOmega hf hY hn F e₀ classification (h15 K₀ hY)
    (wk_le_sylow K₀ L T z v hY.1.1 hSylow hzOmega hf) hb htypes
  refine ⟨K₀, hle, hY, hmin, he, hn, hW, hU, ?_, hb, ht, hpar, e₀, ?_, ?_⟩
  · exact ((invariant_component_consequences K L T z v hK (h14 K hK)).2).trans hU.symm
  · exact modelOfMinimal_mk K₀ K L T z v hL hz hK hle hmin h14 e
  · exact NaturalRecognition.Source.naturalSection hG K₀ L T z v hv hL hz hSylow
      hzOmega hf hY hn F e₀ classification (h15 K₀ hY)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement

end
