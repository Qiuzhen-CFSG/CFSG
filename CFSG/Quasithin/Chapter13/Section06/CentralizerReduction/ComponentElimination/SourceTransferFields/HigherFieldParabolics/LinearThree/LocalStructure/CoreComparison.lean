module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy

/-!
# The intrinsic-to-plus core comparison for flag residuals

Restrict the literal plus quotient to an ambient subgroup of K, then descend
through its intrinsic two-core. The resulting map is surjective and its kernel
is the image of the full inverse image of the plus two-core. It is not identified
with the intrinsic two-core, nor assumed to be a two-group.

Centrality of this precise comparison kernel makes a flag residual's intrinsic
core quotient a perfect central cover of PSL₂. This implies quasisimplicity and,
with the actual Sylow and characteristic-two hypotheses, membership in L(Gᵥ,Tᵥ).
Deriving that centrality from the earlier source setup remains a separate input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.14–16 and 13.6.19, printed pp.929–931.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure
open ComponentSelection
variable {G : Type*} [Group G]

def subgroupPlusMap (K L T H : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hH : H ≤ K) :
    H →* plusImage K L T z v hL hz H :=
  ((plusMk K L T z v hL hz).comp
    (inclusion (hH.trans (K_le_plusActor K L T v)))).codRestrict _
      (fun x => mem_map.mpr
        ⟨inclusion (hH.trans (K_le_plusActor K L T v)) x, x.property, rfl⟩)

theorem subgroupPlusMap_surjective (K L T H : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hH : H ≤ K) :
    Function.Surjective (subgroupPlusMap K L T H z v hL hz hH) := by
  rintro ⟨x, y, hy, rfl⟩
  exact ⟨⟨y, hy⟩, rfl⟩

theorem subgroupPlusMap_ker (K L T H : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hH : H ≤ K) :
    (subgroupPlusMap K L T H z v hL hz hH).ker =
      (centralizer (WK K L T z v : Set G)).subgroupOf H := by
  ext x
  change subgroupPlusMap K L T H z v hL hz hH x = 1 ↔ _
  rw [Subtype.ext_iff]
  change inclusion (hH.trans (K_le_plusActor K L T v)) x ∈
    (plusMk K L T z v hL hz).ker ↔ _
  rw [plusMk_ker]
  rfl

theorem subgroupPlusMap_core_le (K L T H : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hH : H ≤ K) :
    pCore 2 H ≤ (pCore 2 (plusImage K L T z v hL hz H)).comap
      (subgroupPlusMap K L T H z v hL hz hH) := by
  apply map_le_iff_le_comap.mp
  exact le_sSup ⟨Subgroup.Normal.map inferInstance _
    (subgroupPlusMap_surjective K L T H z v hL hz hH), pCore_isPGroup.map _⟩

def coreComparison (K L T H : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hH : H ≤ K) :
    H ⧸ pCore 2 H →*
      plusImage K L T z v hL hz H ⧸ pCore 2 (plusImage K L T z v hL hz H) :=
  QuotientGroup.map _ _ (subgroupPlusMap K L T H z v hL hz hH)
    (subgroupPlusMap_core_le K L T H z v hL hz hH)

theorem coreComparison_surjective (K L T H : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hH : H ≤ K) :
    Function.Surjective (coreComparison K L T H z v hL hz hH) :=
  QuotientGroup.map_surjective_of_surjective _ _ _
    ((QuotientGroup.mk'_surjective _).comp
      (subgroupPlusMap_surjective K L T H z v hL hz hH)) _

theorem coreComparison_mk (K L T H : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hH : H ≤ K) (x : H) :
    coreComparison K L T H z v hL hz hH (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (subgroupPlusMap K L T H z v hL hz hH x) := rfl

theorem coreComparison_ker (K L T H : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hH : H ≤ K) :
    (coreComparison K L T H z v hL hz hH).ker =
      ((pCore 2 (plusImage K L T z v hL hz H)).comap
        (subgroupPlusMap K L T H z v hL hz hH)).map (QuotientGroup.mk' (pCore 2 H)) :=
  QuotientGroup.ker_map _ _ _ _

theorem residual_core_quasisimple [Finite G]
    (F : Type*) [Field F] [Finite F] [CharP F 2] (hcard : 4 ≤ Nat.card F)
    (K L T P : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hP : P ≤ K)
    (e : (plusImage K L T z v hL hz (residualIn P) ⧸
      pCore 2 (plusImage K L T z v hL hz (residualIn P))) ≃* PSL(2, F))
    (hk : (coreComparison K L T (residualIn P) z v hL hz
      ((map_subtype_le _).trans hP)).ker ≤ center (residualIn P ⧸ pCore 2 (residualIn P))) :
    IsQuasisimple (residualIn P ⧸ pCore 2 (residualIn P)) := by
  let : Group.IsPerfect (residualIn P) := Group.IsPerfect.map P.subtype
  let f := (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm).toMonoidHom.comp
    (coreComparison K L T (residualIn P) z v hL hz ((map_subtype_le _).trans hP))
  have hf : Function.Surjective f :=
    (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm).surjective.comp
      (coreComparison_surjective K L T (residualIn P) z v hL hz ((map_subtype_le _).trans hP))
  let : Group.IsPerfect SL(2, F) := Group.IsPerfect.ofSurjective hf
  let : IsQuasisimple SL(2, F) :=
    { toIsPerfect := inferInstance
      simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard }
  exact (show PerfectCentralCovering.Cover (residualIn P ⧸ pCore 2 (residualIn P))
    SL(2, F) from
      { toMonoidHom := f
        surjective := hf
        isPerfect := inferInstance
        ker_le_center := by
          intro x hx
          apply hk
          exact (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm).injective
            ((show f x = 1 from hx).trans (map_one _).symm) }).isQuasisimple

theorem residual_mem_LIn_of_central_kernel [Finite G]
    (F : Type*) [Field F] [Finite F] [CharP F 2] (hcard : 4 ≤ Nat.card F)
    (K L T P : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hP : P ≤ K) (hK : K ≤ Gv v)
    (hn : Tv T v ≤ normalizer (P : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (e : (plusImage K L T z v hL hz (residualIn P) ⧸
      pCore 2 (plusImage K L T z v hL hz (residualIn P))) ≃* PSL(2, F))
    (hk : (coreComparison K L T (residualIn P) z v hL hz
      ((map_subtype_le _).trans hP)).ker ≤ center (residualIn P ⧸ pCore 2 (residualIn P))) :
    residualIn P ∈ Chapter1.LIn (Gv v) (Tv T v) := by
  let R := residualIn P
  let H := R ⊔ Tv T v
  have hRG : R ≤ Gv v := (map_subtype_le _).trans (hP.trans hK)
  have hHG : H ≤ Gv v := sup_le hRG inf_le_right
  have hnR : Tv T v ≤ normalizer (R : Set G) := residualIn_normalized _ _ hn
  let : (R.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer (show R ≤ H from le_sup_left)).mpr
      (sup_le R.le_normalizer hnR)
  let : Group.IsPerfect R := Group.IsPerfect.map P.subtype
  let : IsQuasisimple (R ⧸ pCore 2 R) :=
    residual_core_quasisimple F hcard K L T P z v hL hz hP e hk
  let er : R ≃* R.subgroupOf H := (subgroupOfEquivOfLe (show R ≤ H from le_sup_left)).symm
  let : Group.IsPerfect (R.subgroupOf H) := Group.IsPerfect.ofSurjective (f := er.toMonoidHom) er.surjective
  let : IsQuasisimple ((R.subgroupOf H) ⧸ pCore 2 (R.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ er (pCore_map_iso 2 er))
  have hp : IsPPerfect 2 (R.subgroupOf H) := by
    intro N hN hquot
    let := hN
    by_contra htop
    let : Nontrivial ((R.subgroupOf H) ⧸ N) := QuotientGroup.nontrivial_iff.mpr htop
    exact Group.IsPerfect.not_isNilpotent _ hquot.isNilpotent
  have hcc : (R.subgroupOf H).IsCComponent :=
    isCComponent_of_isPPerfect_of_quasisimple_core_quotient
      (inferInstance : (R.subgroupOf H).Normal).isSubnormal hp
  have hRne : R ≠ ⊥ := by
    intro he
    have hh : R.subgroupOf H = ⊥ := by rw [he, bot_subgroupOf]
    exact hcc.ne_bot hh
  let : Nontrivial H := (nontrivial_iff_ne_bot H).mpr (by
    intro he
    exact hRne (le_bot_iff.mp (he ▸ (le_sup_left : R ≤ H))))
  have hcore : pCore 2 H ≠ ⊥ := by
    intro he
    have hc := centralizer_generalizedFitting_le H
    rw [residual_join_characteristic_two T P v (hP.trans hK) hSylow hf, he,
      show centralizer ((⊥ : Subgroup H) : Set H) = ⊤ from
        centralizer_eq_top_iff_subset.mpr (show (⊥ : Subgroup H) ≤ center H from bot_le)] at hc
    exact bot_ne_top (top_le_iff.mp hc)
  refine ⟨hRG, hcc, hSylow.restrict le_sup_right hHG, ?_⟩
  exact fun he => hcore ((map_eq_bot_iff_of_injective _ H.subtype_injective).mp he)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure

end
