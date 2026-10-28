module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.LocalGeometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Assembly
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.FlagTypes.Preparation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure.KernelControl
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure.Consequences

/-!
# The complete G₂ obstruction in source 13.6.19

A Sylow marking of the actual plus image is an equality, because the
intersection Tᵥ ∩ K is Sylow in K and its model map is surjective.
The intrinsic G₂ root-normalizer characterizations then make both pulled-back
parabolics Tᵥ-invariant. This discharges the invariance premise left by the
previous local-geometry interface.

The earlier reduced-module input and universal A.3.6 theorem give the literal
action kernel as a two-group. Its restriction to a parabolic residual makes
the intrinsic-to-plus core comparison injective. The existing rank-one
geometry therefore proves actual local-family membership and minimal
parabolicity. Root commutators prove non-shortness in the original extension,
while C.1.26 and 13.6.16(2) force shortness, excluding the G₂ model.

The argument uses the actual octonion group model and original quotient maps.
It does not need an additional module-recognition premise: its non-shortness
obstruction already occurs in the two-core of the matrix residual. The marked
natural representation remains available in G2.MarkedAction.Assembly.

The universal A.3.6 and C.1.26 results and the genuine earlier Y_z, invariance,
Sylow, characteristic-two, reduced-family and 13.6.16(2) conclusions remain
explicit. Their source discharge belongs to qt-13-06-centralizer-reduction.
The three-family assembly, with the Sp₄ branch still missing, remains with
qt-13-06-source-higher-field-parabolics.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.6.14,
13.6.16(2) and 13.6.19, printed pp.929–931; B.6.1 and C.1.26.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.G2
open ComponentSelection
open HigherFieldParabolics.G2
open Atlas.G2.HigherFieldResiduals
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
universe u
variable {G : Type u} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable (e : plusImage K L T z v hL hz K ≃* Atlas.G2.Model F)

/-- The aligned image of Tᵥ ∩ K is the full unipotent Sylow subgroup. -/
theorem marked_intersection_eq
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hmark : ((Tv T v ⊓ K).subgroupOf K).map
      (modelMap K L T z v hL hz e) ≤ Atlas.G2.unipotent) :
    ((Tv T v).subgroupOf K).map (modelMap K L T z v hL hz e) =
      Atlas.G2.unipotent := by
  obtain ⟨S, hS⟩ := sylow_intersection K L T z v hK hn
  have hS' : (S : Subgroup K) = (Tv T v).subgroupOf K := by
    have hh := congrArg (comap K.subtype) hS
    simpa only [comap_map_eq_self_of_injective K.subtype_injective,
      comap_inf, comap_subtype, subgroupOf_self, inf_top_eq] using hh
  let Q := S.mapSurjective (modelMap_surjective K L T z v hL hz e)
  have hQ : (Q : Subgroup (Atlas.G2.Model F)) =
      ((Tv T v).subgroupOf K).map (modelMap K L T z v hL hz e) := by
    change (S : Subgroup K).map _ = _
    rw [hS']
  have hm : ((Tv T v).subgroupOf K).map (modelMap K L T z v hL hz e) ≤
      Atlas.G2.unipotent := by
    have hi : (Tv T v ⊓ K).subgroupOf K = (Tv T v).subgroupOf K := by
      ext x
      exact ⟨fun h => h.1, fun h => ⟨h, x.property⟩⟩
    rwa [hi] at hmark
  exact le_antisymm hm ((Q.is_maximal'
    (Atlas.G2.LieParabolicSetup.unipotent_isTwoGroup (F := F)) (hQ ▸ hm)).le.trans_eq hQ)

/-- Both constructed parabolics are invariant under actual Tᵥ conjugation. -/
theorem parabolic_normalized
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hmark : ((Tv T v ⊓ K).subgroupOf K).map
      (modelMap K L T z v hL hz e) ≤ Atlas.G2.unipotent) (i : Fin 2) :
    Tv T v ≤ normalizer (liftedParabolic K L T z v hL hz e i : Set G) := by
  have hm := marked_intersection_eq K L T z v hL hz e hK hn hmark
  apply LinearThree.MarkedAction.preimage_normalized_of_modelAction K L T z v hL hz hn e
  intro t
  apply parabolic_stable
  rw [← hm]
  exact LinearThree.MarkedAction.modelAction_marked_subgroup K L T z v hL hz hn e t

omit e [Field F] [Finite F] [CharP F 2] in
/-- A two-group relative action kernel makes the literal residual core comparison injective. -/
theorem residual_coreComparison_ker_eq_bot (P : Subgroup G) (hP : P ≤ K)
    (hk : IsPGroup 2 ((centralizer (WK K L T z v : Set G)).subgroupOf K)) :
    (LinearThree.LocalStructure.coreComparison K L T (residualIn P) z v hL hz
      ((map_subtype_le _).trans hP)).ker = ⊥ := by
  let R := residualIn P
  have hR : R ≤ K := (map_subtype_le _).trans hP
  let f := LinearThree.LocalStructure.subgroupPlusMap K L T R z v hL hz hR
  have hkf : IsPGroup 2 f.ker := by
    rw [LinearThree.LocalStructure.subgroupPlusMap_ker]
    have he : (centralizer (WK K L T z v : Set G)).subgroupOf R =
        ((centralizer (WK K L T z v : Set G)).subgroupOf K).comap (inclusion hR) := rfl
    rw [he]
    exact hk.comap_of_injective _ (inclusion_injective hR)
  rw [LinearThree.LocalStructure.coreComparison_ker,
    f.comap_pCore_of_ker_isPGroup
      (LinearThree.LocalStructure.subgroupPlusMap_surjective K L T R z v hL hz hR) hkf]
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

/-- Construct every model-specific input to C.1.26 for the G₂ case. -/
theorem source_parabolic {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK κ D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v)) :
    ∃ (g : Atlas.G2.Model F) (i : Fin 2),
      let e' := e.trans (MulAut.conj g)
      let P := liftedParabolic K L T z v hL hz e' i
      P ≤ K ∧ IsCoatom (P.subgroupOf K) ∧ Tv T v ⊓ K ≤ P ∧
        Tv T v ≤ normalizer (P : Set G) ∧
        Tv T v ≤ normalizer (residualIn P : Set G) ∧
        ¬ residualIn P ≤ centralizer ({z} : Set G) ∧
        residualIn P ∈ Chapter1.LIn (Gv v) (Tv T v) ∧
        ¬ ChapterC.IsShort (residualIn P) ∧ ¬ ChapterC.IsBlock (residualIn P) ∧
        Nonempty ((plusImage K L T z v hL hz (residualIn P) ⧸
          pCore 2 (plusImage K L T z v hL hz (residualIn P))) ≃* PSL(2, F)) ∧
        IsQuasisimple (residualIn P ⧸ pCore 2 (residualIn P)) ∧
        IsSQTK κ (residualIn P ⊔ Tv T v : Subgroup G) ∧
        generalizedFitting (residualIn P ⊔ Tv T v : Subgroup G) =
          pCore 2 (residualIn P ⊔ Tv T v : Subgroup G) ∧
        ∀ S : Sylow 2 (residualIn P ⊔ Tv T v : Subgroup G),
          (S : Subgroup (residualIn P ⊔ Tv T v : Subgroup G)).map
            (residualIn P ⊔ Tv T v).subtype = Tv T v →
              ChapterB.IsMinimalParabolicOver S ⊤ := by
  have hcard : 4 ≤ Nat.card F := by
    have hp : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm
    omega
  have hq : 2 < Nat.card F := by omega
  have hk := HigherFieldParabolics.G2.MarkedAction.Assembly.relativeKernel_isPGroup
    K L T z v hL hz hG hA36 hF hm hv hK
    (LinearThree.LocalStructure.plus_twoCore_eq_bot_of_reduced K L T z v hL hz hW) e
  have hmove : ¬ K ≤ centralizer ({z} : Set G) := by
    intro hc
    exact (invariant_component_consequences K L T z v hK hn).1.2
      ((starPreimage_starImage_centralizes_seed_iff z v K hK.1.1).mpr hc)
  obtain ⟨g, hg⟩ := exists_aligned_marking K L T z v hL hz e hK
  let e' := e.trans (MulAut.conj g)
  obtain ⟨i, hPG, hPK, hinter, hmax, hmoveP⟩ :=
    exists_moving_maximal_parabolic K L T z v hL hz e' hq hK hg hmove
  let P := liftedParabolic K L T z v hL hz e' i
  have hnP := parabolic_normalized K L T z v hL hz e' hK hn hg i
  have hnR := LinearThree.residualIn_normalized (Tv T v) P hnP
  let eR := plusResidualCoreQuotientEquivPSL K L T z v hL hz e' hq i
  have hker : (LinearThree.LocalStructure.coreComparison K L T (residualIn P)
      z v hL hz ((map_subtype_le _).trans hPK)).ker ≤
      center (residualIn P ⧸ pCore 2 (residualIn P)) := by
    rw [residual_coreComparison_ker_eq_bot K L T z v hL hz P hPK hk]
    exact bot_le
  have hlocal := LinearThree.LocalStructure.residual_mem_LIn_of_central_kernel
    F hcard K L T P z v hL hz hPK hK.1.1 hnP hSyl hf eR hker
  have hquasi := LinearThree.LocalStructure.residual_core_quasisimple
    F hcard K L T P z v hL hz hPK eR hker
  have hshort := lifted_residual_not_short K L T z v hL hz e' hq hk i
  exact ⟨g, i, hPK, hmax, hinter, hnP, hnR, hmoveP, hlocal, hshort,
    fun hb => hshort hb.short, ⟨eR⟩, hquasi,
    LinearThree.residual_join_sqtk hG T P v hv hPG,
    LinearThree.residual_join_characteristic_two T P v hPG hSyl hf,
    LinearThree.LocalStructure.residual_minimal_of_central_kernel
      F K L T P z v hL hz hPK hnP eR hker⟩

omit e in
/-- The G₂ exclusion, retaining only genuine earlier ambient and universal inputs. -/
theorem not_g2_of_source {κ : GroupClass.{u}}
    (choices : DistinguishedPairs.{u}) (hC126 : C126Source κ choices)
    (hG : IsSimpleQTKE κ G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK κ D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    (h16 : ∀ D ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (D : Set G) → ¬ D ≤ centralizer ({z} : Set G) →
      CharacteristicNormalizerObstruction (Tv T v) D) :
    ¬ Nonempty (plusImage K L T z v hL hz K ≃* Atlas.G2.Model F) := by
  rintro ⟨e⟩
  obtain ⟨g, i, hPK, hmax, hinter, hnP, hnR, hmove, hlocal,
    hshort, hblock, he, hquasi, hsqtk, hfR, hpar⟩ :=
    source_parabolic K L T z v hL hz e hG hA36 hF hm hv hK hn hSyl hf hW
  let := hquasi
  exact false_of_moving_local_nonshort choices hC126 T _ z v
    hlocal hnR hmove h16 hsqtk hfR hpar hshort

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.G2
