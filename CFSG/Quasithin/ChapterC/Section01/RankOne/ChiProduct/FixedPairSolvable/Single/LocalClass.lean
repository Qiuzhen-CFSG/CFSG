module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Single.Minimal
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.CubicLocal.InLocalClass

/-!
# The fixed-pair cubic local group inside the original minimal parabolic

When the reduced solvable action has abelian Sylow image, its actual actor
is S₃. The original Baumann theorem puts Baum(T) as a Sylow subgroup of
N = O²(H) Baum(T). The cubic Frattini argument makes N a minimal parabolic.
The actual omega-center span contains the original canonical module, and
the original action kernel centralizes that span. These facts construct
C.1.17 on this normal N, without choosing an unrelated local subgroup.

Source: Aschbacher--Smith C.1.26--28, printed pp.132--134.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Single
open ChapterB GlaubermanNiles SelectedRankOne
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The intrinsic omega-center span of the Baumann Sylow is the full
original alpha span, under the literal normal-subgroup inclusion. -/
theorem omegaClosure_baumann_sylow_map
    (T : Sylow 2 G)
    (S : Sylow 2 (pResidual 2 G ⊔ baumann (T : Subgroup G) : Subgroup G))
    (hS : (S : Subgroup (pResidual 2 G ⊔ baumann (T : Subgroup G) : Subgroup G)).map (pResidual 2 G ⊔ baumann (T : Subgroup G)).subtype =
      baumann (T : Subgroup G)) :
    (normalClosure (omegaOneCenterAmbient (S : Subgroup (pResidual 2 G ⊔ baumann (T : Subgroup G) : Subgroup G)) : Set _)).map
      (pResidual 2 G ⊔ baumann (T : Subgroup G)).subtype =
        normalClosure (thompsonAlpha (T : Subgroup G) : Set G) := by
  let B := baumann (T : Subgroup G)
  let N := pResidual 2 G ⊔ B
  have hgen := pResidual_sup_sylow_eq_top T
  let : N.Normal := baumann_residual_join_normal (T : Subgroup G) (pResidual 2 G) hgen
  have hAN : thompsonAlpha (T : Subgroup G) ≤ N := by
    rw [←baumann_omega_eq_alpha]
    intro x hx
    exact (show B ≤ N from le_sup_right) ((mem_omegaOneCenterAmbient_iff _ x).mp hx).1
  have hNT : N ⊔ (T : Subgroup G) = ⊤ := by
    apply top_unique
    rw [←hgen]
    exact sup_le_sup le_sup_left le_rfl
  have hz : omegaOneCenterAmbient (S : Subgroup N) =
      (thompsonAlpha (T : Subgroup G)).subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [←omegaOneCenterAmbient_map_injective N.subtype N.subtype_injective,hS,
      baumann_omega_eq_alpha,map_subgroupOf_eq_of_le hAN]
  rw [hz]
  exact (normalClosure_eq_map_of_normal_supplement N (T : Subgroup G)
    (thompsonAlpha (T : Subgroup G)) hNT hAN (alpha_normalized _)).symm

/-- C.1.17 on the normal residual--Baumann join in the genuine solvable
single-factor branch. The full original action kernel is retained. -/
theorem selected_inLocalClass_of_abelian_action
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hfit : generalizedFitting G = pCore 2 G)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer
      (normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G))
    (hrank : primeRank 3 G ≤ 2)
    (hsolv : Group.IsSolvable (G ⧸ centralizer
      (normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G)))
    (habel : IsMulCommutative ((T : Subgroup G).map (QuotientGroup.mk' (centralizer
      (normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G))))) :
    InLocalClass (inclusion (show baumann (T : Subgroup G) ≤
      pResidual 2 G ⊔ baumann (T : Subgroup G) from le_sup_right)) := by
  let U := normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G)
  let q := QuotientGroup.mk' (centralizer (U : Set G))
  have hU : IsPReduced 2 U := omegaCenter_normalClosure_reduced T
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit)
  let : IsElementaryAbelian 2 U := hU.elementary
  obtain ⟨_,_,h3,_⟩ := CubicLocal.reduced_abelian_sylow_action T hP U hU hJ hsolv habel
  obtain ⟨d,hBY,hB,hker⟩ := solvable_baumann_kernel_and_layer T hP U hU q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hU.quotient_pCore_eq_bot
    hJ hrank hsolv
  have hcard : Nat.card ((pResidual 2 G).map q) = 3 := by
    rw [map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)]
    exact h3
  obtain ⟨S,hS,hunique⟩ := selected_baumann_unique_of_cubic_residual T hP U hU hJ q
    (QuotientGroup.ker_mk' _) hcard hB
  let B := baumann (T : Subgroup G)
  let N := pResidual 2 G ⊔ B
  let W := normalClosure (omegaOneCenterAmbient (S : Subgroup N) : Set N)
  have hfitN : generalizedFitting N = pCore 2 N :=
    selected_baumann_fitting (T : Subgroup G) (pResidual 2 G)
      (pResidual_sup_sylow_eq_top T) hfit
  have hW : IsPReduced 2 W := omegaCenter_normalClosure_reduced S
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfitN)
  let : IsElementaryAbelian 2 W := hW.elementary
  have hUW : U ≤ W.map N.subtype := by
    rw [omegaClosure_baumann_sylow_map T S hS]
    exact normalClosure_mono (omegaCenter_le_omegaCenter_maxJ (T : Subgroup G))
  have hJJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      (elementaryAbelianMaxJ (S : Subgroup N)).map N.subtype := by
    rw [←elementaryAbelianMaxJ_map_injective N.subtype N.subtype_injective,hS]
    have hlarge := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le
      (T : Subgroup G) B (elementaryAbelianMaxJ_le_baumann _)
    exact hlarge.2 (le_antisymm hlarge.1
      (elementaryAbelianMaxOrder_le_and_j_le_of_eq B (T : Subgroup G) inf_le_left).1)
  have hJN : ¬ elementaryAbelianMaxJ (S : Subgroup N) ≤ centralizer (W : Set N) := by
    intro hh
    have hm := map_mono (f := N.subtype) hh
    rw [map_centralizer_subtype] at hm
    exact hJ (hJJ.trans ((hm.trans inf_le_right).trans (centralizer_le hUW)))
  have hPN : IsMinimalParabolicOver S ⊤ := by
    refine ⟨hunique,?_⟩
    intro hn
    let : (S : Subgroup N).Normal := normalizer_eq_top_iff.mp (top_unique hn)
    have hSQ : (S : Subgroup N) ≤ pCore 2 N := le_sSup ⟨inferInstance,S.isPGroup'⟩
    exact hJN ((sSup_le fun _ hA => hA.1).trans
      (hSQ.trans (le_centralizer_iff.mp hW.le_centralizer_pCore)))
  have hsG := solvable_of_reduced_minimalParabolic_action T hP U hU hJ q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hsolv
  let : Group.IsSolvable G := hsG
  have hkW : (q.comp N.subtype).ker ≤ centralizer (W : Set N) :=
    restricted_kernel_centralizes_omegaClosure T q hker N le_rfl S hS
  have habq : IsMulCommutative ((S : Subgroup N).map (q.comp N.subtype)) := by
    rw [←Subgroup.map_map,hS]
    let : IsMulCommutative ((T : Subgroup G).map q) := habel
    have hle : B.map q ≤ (T : Subgroup G).map q := map_mono inf_le_left
    exact le_centralizer_iff_isMulCommutative.mp
      (hle.trans ((le_centralizer _).trans (centralizer_le hle)))
  have habW : IsMulCommutative ((S : Subgroup N).map
      (QuotientGroup.mk' (centralizer (W : Set N)))) := by
    apply commutator_self_eq_bot_iff.mp
    rw [←map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
    apply le_trans _ hkW
    apply (Subgroup.map_eq_bot_iff _).mp
    rw [map_commutator]
    exact commutator_self_eq_bot_iff.mpr habq
  exact CubicLocal.selected_inLocalClass T N S B le_sup_right hS hPN hfitN hJN
    inferInstance habW
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Single
