module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.ShortImage
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure.CoreComparison
public import Theory.GroupTheory.PCoreCentralKernelCommutator

/-!
# Non-shortness with the actual central comparison kernel

LocalStructure allows odd central elements in the action kernel. Its precise
conclusion says that the intrinsic-to-plus map after removing both two-cores
has central kernel. Since an affine SL₂ group is generated on its core by
commutators, the new core-image lemma makes the source two-core map onto the
affine core. The irreducibility argument in ShortImage now applies unchanged.

The application uses LocalStructure.subgroupPlusMap and coreComparison
literally. W_K normalizes each original flag preimage, so [W_K,R] lies in
both W_K and O₂(R), with the original ambient embeddings. Movement is the
only flag-specific input besides its affine image. Neither a two-group
kernel, a natural-module assertion nor a nonzero core triple is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.19, printed p.931, and C.1.7, printed p.123.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction
open ComponentSelection
variable {G : Type*} [Group G]

/-- C.1.7 irreducibility obstructs a moving elementary action with affine
image and central kernel after removing the intrinsic two-cores. -/
theorem not_short_of_affine_action_of_central_coreMap [Finite G] (R W : Subgroup G)
    [Group.IsPerfect R] [IsElementaryAbelian 2 W]
    (hRW : R ≤ normalizer (W : Set G)) (hWR : W ≤ normalizer (R : Set G))
    (hm : ⁅W, R⁆ ≠ ⊥)
    {D F : Type*} [Group D] [Field F] [Finite F] [CharP F 2]
    (e : D ≃* Matrix.SL2.Affine F)
    (f : R →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (W : Set G)).subgroupOf R)
    (hc : pCore 2 R ≤ (pCore 2 D).comap f)
    (hcentral : (QuotientGroup.map (pCore 2 R) (pCore 2 D) f hc).ker ≤
      center (R ⧸ pCore 2 R)) : ¬ ChapterC.IsShort R := by
  apply not_short_of_action_image R W hRW hWR hm f hf hk
  have he := ChapterC.SL2Affine.blockU_eq_core e
  have hmap := f.map_pCore_eq_of_central_coreMap hf hc hcentral he
  rw [ChapterC.blockU, map_commutator, hmap, map_top_of_surjective f hf]
  change ¬ ChapterC.blockU D ≤ center D
  rw [he]
  exact ChapterC.SL2Affine.core_not_le_center e

/-- Either actual moving flag residual is non-short under exactly the
intrinsic core-comparison kernel bound provided by LocalStructure. -/
theorem flag_residual_not_short_of_central_kernel [Finite G]
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hcard : 4 ≤ Nat.card F)
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hW : WK K L T z v ≤ Tv T v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (P : Subgroup G)
    (hP : P ∈ ({pointPreimage F K L T z v hL hz e,
      linePreimage F K L T z v hL hz e} : Set (Subgroup G)))
    (hPK : P ≤ K)
    (hm : ¬ residualIn P ≤ centralizer ({z} : Set G))
    (hk : (LocalStructure.coreComparison K L T (residualIn P) z v hL hz
      ((map_subtype_le _).trans hPK)).ker ≤
        center (residualIn P ⧸ pCore 2 (residualIn P))) :
    ¬ ChapterC.IsShort (residualIn P) := by
  let R := residualIn P
  have hRK : R ≤ K := (map_subtype_le _).trans hPK
  let : Group.IsPerfect R := Group.IsPerfect.map P.subtype
  have hWR : WK K L T z v ≤ normalizer (R : Set G) := by
    apply residualIn_normalized _ P
    rcases hP with hP | hP
    · subst P
      exact WK_normalizes_preimage K L T z v hL hz hW hn e _
    · have he : P = linePreimage F K L T z v hL hz e := Set.mem_singleton_iff.mp hP
      subst P
      exact WK_normalizes_preimage K L T z v hL hz hW hn e _
  have hmove : ⁅WK K L T z v, R⁆ ≠ ⊥ := by
    intro he
    apply hm
    exact (commutator_eq_bot_iff_le_centralizer.mp
      ((commutator_comm R (WK K L T z v)).trans he)).trans
        (centralizer_le (Set.singleton_subset_iff.mpr
          (le_conjugateSpanBy _ _ (mem_zpowers z))))
  have ha : Nonempty (plusImage K L T z v hL hz R ≃* Matrix.SL2.Affine F) := by
    rcases hP with hP | hP
    · subst P
      exact ⟨(plusResidualEquiv K L T z v hL hz e
        (Matrix.PSL3.LinearThree.pointParabolicSL F)).trans
        ((MulEquiv.subgroupCongr (Matrix.PSL3.LinearThree.pointParabolicSL_residual F hcard)).trans
          (Matrix.PSL3.LinearThree.pointLocalAffineEquiv F))⟩
    · have he : P = linePreimage F K L T z v hL hz e := Set.mem_singleton_iff.mp hP
      subst P
      exact ⟨(plusResidualEquiv K L T z v hL hz e
        (Matrix.PSL3.LinearThree.lineParabolicSL F)).trans
        ((MulEquiv.subgroupCongr (Matrix.PSL3.LinearThree.lineParabolicSL_residual F hcard)).trans
          (Matrix.PSL3.LinearThree.lineLocalAffineEquiv F))⟩
  obtain ⟨a⟩ := ha
  exact not_short_of_affine_action_of_central_coreMap R (WK K L T z v)
    (hRK.trans ((K_le_plusActor K L T v).trans
      (plusActor_normalizes_WK K L T z v hL hz))) hWR hmove a
    (LocalStructure.subgroupPlusMap K L T R z v hL hz hRK)
    (LocalStructure.subgroupPlusMap_surjective K L T R z v hL hz hRK)
    (LocalStructure.subgroupPlusMap_ker K L T R z v hL hz hRK)
    (LocalStructure.subgroupPlusMap_core_le K L T R z v hL hz hRK) hk

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction
