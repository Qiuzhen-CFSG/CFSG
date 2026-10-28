module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MinimalGeometry.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MinimalGeometry.LocalHypotheses
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MinimalGeometry.ImageRigidity
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MinimalGeometry.UniqueMaximal

/-!
# Geometry of the minimal replacement in 13.6.18

Starting with the original rank-one model, full local-family minimality gives
an equal-star-image replacement in Y_z. The earlier universal conclusion of
13.6.14 then gives its invariance. Its native plus quotient inherits the model
with the same markings and conjugation action on the unchanged W_K.

Full minimality and Borel uniqueness give the unique maximal overgroup of each
Sylow with ambient image T_v; its nonnormality follows from the rank-one model.
Thus K₀T_v satisfies Definition B.6.1. The involution-centralizer hypotheses
also give SQTK and characteristic two for this actual local join.

The final consumer applies the separate C.1.26 implication, deriving its
geometric premises and applying the earlier universal 13.6.16(2) to K₀.
The earlier-source inputs remain explicit, as in `ComponentModules`,
`ComponentControl`, and `CharacteristicTwo`. Natural recognition, the C.1.26
source theorem and elimination of the A₅ alternative belong to the enclosing
13.6.18 assembly; none is used to prove the geometry.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.18, printed p.931 (PDF p.948), and Definition B.6.1, printed p.112.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MinimalGeometry
open Subgroup Theory.GroupTheory ComponentSelection
open scoped MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Full local minimality gives the source's minimal parabolic, starting with
the original model. Neither invariance nor a model of K₀ is an extra premise. -/
theorem minimal_local_parabolic
    (K₀ K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hle : K₀ ≤ K)
    (hmin : Minimal (fun D => D ∈ Chapter1.LIn (K ⊔ Tv T v) (Tv T v)) K₀)
    (h14 : ∀ D ∈ Yz L T z v, Tv T v ≤ normalizer (D : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : plusImage K L T z v hL hz K ≃* SL(2, F)) :
    ∀ P : Sylow 2 (K₀ ⊔ Tv T v : Subgroup G),
      (P : Subgroup (K₀ ⊔ Tv T v : Subgroup G)).map (K₀ ⊔ Tv T v).subtype = Tv T v →
        ChapterB.IsMinimalParabolicOver P ⊤ := by
  have h := minimal_replacement_consequences K₀ K L T z v hL hz hK hle hmin h14 e
  exact local_minimalParabolic_of_rankOne_image K₀ K L T z v hle hmin hL hz h.2.2.1
    (modelOfMinimal K₀ K L T z v hL hz hK hle hmin h14 e)

/-- All replacement geometry required by the actual pushing-up consumer.
The characteristic-two identity is relative to K₀T_v, and parabolicity holds
for every Sylow whose embedded subgroup is the literal T_v. -/
theorem minimal_local_geometry {𝒦 : GroupClass.{u}}
    (hG : IsSimpleQTKE 𝒦 G)
    (K₀ K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hle : K₀ ≤ K)
    (hmin : Minimal (fun D => D ∈ Chapter1.LIn (K ⊔ Tv T v) (Tv T v)) K₀)
    (h14 : ∀ D ∈ Yz L T z v, Tv T v ≤ normalizer (D : Set G))
    (hv : orderOf v = 2)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : plusImage K L T z v hL hz K ≃* SL(2, F)) :
    starImage z v K₀ = starImage z v K ∧ K₀ ∈ Yz L T z v ∧
      Tv T v ≤ normalizer (K₀ : Set G) ∧
      WK K₀ L T z v = WK K L T z v ∧
      ⁅WK K₀ L T z v, K₀⁆ = ⁅WK K L T z v, K⁆ ∧
      IsSQTK 𝒦 (K₀ ⊔ Tv T v : Subgroup G) ∧
      generalizedFitting (K₀ ⊔ Tv T v : Subgroup G) =
        pCore 2 (K₀ ⊔ Tv T v : Subgroup G) ∧
      ∀ P : Sylow 2 (K₀ ⊔ Tv T v : Subgroup G),
        (P : Subgroup (K₀ ⊔ Tv T v : Subgroup G)).map (K₀ ⊔ Tv T v).subtype = Tv T v →
          ChapterB.IsMinimalParabolicOver P ⊤ := by
  obtain ⟨he, hY, hn, hW, hU⟩ :=
    minimal_replacement_consequences K₀ K L T z v hL hz hK hle hmin h14 e
  exact ⟨he, hY, hn, hW, hU,
    local_join_sqtk hG K₀ T v hv hY.1.1,
    local_join_characteristic_two K₀ T v hY.1.1 hSylow hf,
    minimal_local_parabolic K₀ K L T z v hL hz hK hle hmin h14 e⟩

/-- Equal model coordinates act identically on corresponding vectors of the
two literal W subgroups. Together with `modelOfMinimal_mk`, this connects the
replacement's native quotient to the original marked representation. -/
theorem modelOfMinimal_action
    (K₀ K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hle : K₀ ≤ K)
    (hmin : Minimal (fun D => D ∈ Chapter1.LIn (K ⊔ Tv T v) (Tv T v)) K₀)
    (h14 : ∀ D ∈ Yz L T z v, Tv T v ≤ normalizer (D : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : plusImage K L T z v hL hz K ≃* SL(2, F))
    (a : plusImage K₀ L T z v hL hz K₀)
    (b : plusImage K L T z v hL hz K)
    (hab : modelOfMinimal K₀ K L T z v hL hz hK hle hmin h14 e a = e b)
    (w₀ : WK K₀ L T z v) (w : WK K L T z v) (hw : (w₀ : G) = (w : G)) :
    ((plusAction K₀ L T z v hL hz a w₀ : WK K₀ L T z v) : G) =
      ((plusAction K L T z v hL hz b w : WK K L T z v) : G) := by
  obtain ⟨k, rfl⟩ := componentMap_surjective K₀ L T z v hL hz a
  have hb : componentMap K L T z v hL hz (inclusion hle k) = b :=
    e.injective ((modelOfMinimal_mk K₀ K L T z v hL hz hK hle hmin h14 e k).symm.trans hab)
  rw [← hb]
  calc
    _ = (k : G) * (w₀ : G) * (k : G)⁻¹ :=
      plusAction_mk_apply K₀ L T z v hL hz (inclusion (K_le_plusActor K₀ L T v) k) w₀
    _ = (k : G) * (w : G) * (k : G)⁻¹ :=
      congrArg (fun x : G => (k : G) * x * (k : G)⁻¹) hw
    _ = _ := (plusAction_mk_apply K L T z v hL hz
      (inclusion (K_le_plusActor K L T v) (inclusion hle k)) w).symm

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
open HigherFieldParabolics

/-- Apply the independent C.1.26 theorem to the minimal replacement. The
earlier universal 13.6.16(2) is applied only after proving K₀ is local, invariant
and moves z. All additional geometric premises are discharged here. -/
theorem block_alternatives_of_minimal_source {𝒦 : GroupClass.{u}}
    (choices : DistinguishedPairs.{u}) (source : C126Source 𝒦 choices)
    (hG : IsSimpleQTKE 𝒦 G)
    (K₀ K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hle : K₀ ≤ K)
    (hmin : Minimal (fun D => D ∈ Chapter1.LIn (K ⊔ Tv T v) (Tv T v)) K₀)
    (h14 : ∀ D ∈ Yz L T z v, Tv T v ≤ normalizer (D : Set G))
    (h16 : ∀ D ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (D : Set G) → ¬ D ≤ centralizer ({z} : Set G) →
      CharacteristicNormalizerObstruction (Tv T v) D)
    (hv : orderOf v = 2)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : plusImage K L T z v hL hz K ≃* SL(2, F)) :
    ChapterC.IsBlock (K₀.subgroupOf (K₀ ⊔ Tv T v)) ∧
      ((∃ n, ChapterC.IsL2EvenBlock K₀ n) ∨ ChapterC.IsAlternatingBlock K₀ 5) := by
  obtain ⟨_, hY, hn, _, _, hsqtk, hf₀, hpar⟩ :=
    minimal_local_geometry hG K₀ K L T z v hL hz hK hle hmin h14 hv hSylow hf e
  have hmove : ¬ K₀ ≤ centralizer ({z} : Set G) := by
    intro hc
    exact (invariant_component_consequences K₀ L T z v hY hn).1.2
      ((starPreimage_starImage_centralizes_seed_iff z v K₀ hY.1.1).mpr hc)
  exact block_alternatives_of_C126 choices source (Tv T v) K₀ hY.1.2 hn
    (h16 K₀ hY.1 hn hmove) hsqtk hf₀ hpar

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MinimalGeometry

end
