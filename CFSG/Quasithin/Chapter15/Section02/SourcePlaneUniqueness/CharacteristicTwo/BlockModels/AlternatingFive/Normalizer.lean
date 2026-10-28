module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.RankOne
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation
public import Theory.GroupTheory.OddSubgroupBlockNormalizer

/-!
# QI preserves each actual alternating-five constituent

The odd subgroup constructed in K intersect X normalizes QI. Distinct
conjugate blocks commute, while the center of X is a two-group. The
odd-subgroup normalization theorem therefore shows that QI cannot exchange
the two constituents, including when S does exchange them.

Source: Aschbacher--Smith preliminary15.2.23, printed p.1115.
The input contains no normality assumption on X in I.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
open Stellmacher Theory.GroupTheory Section01 Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

theorem a5_parabolic_core_normalizes_block
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    (hb : ChapterC.IsAlternatingBlock X 5) :
    (planeParabolicCore T H ZS).subgroupOf I ≤ normalizer (X : Set I) := by
  obtain ⟨D,hDX,ho,hd,hDK⟩ := d.chi_block_odd_intersection hI hfit
    ⟨hX,Or.inr ⟨5,by decide,hb⟩⟩
  let Q := planeParabolicCore T H ZS
  have hQI : Q ≤ I := (pCoreIn_le 2 _).trans
    ((d.residual_sup_planeSylow_le hI).trans inf_le_right)
  have hDQ : D ≤ normalizer (Q.subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq hQI]
    intro x hx
    exact d.planeParabolicCore_normalized hI
      (map_subtype_le (pResidual 2 H) (hDK (mem_map_of_mem I.subtype hx)))
  have hZ : IsPGroup 2 (center X) := pCore_isPGroup.to_le (by
    intro z hz
    apply hb.2.1.centralizer_blockU.le
    intro u hu
    exact mem_center_iff.mp hz u)
  apply normalizes_of_odd_subgroup_and_commuting_conjugates X (Q.subgroupOf I) D
    (isPGroup_pCoreIn 2 _).comap_subtype ho hd hDX hDQ hZ
  intro q hq hne
  have hqX : IsQuasisimple (X ⧸ pCore 2 X) := by
    obtain ⟨e⟩ := hb.2.2.quotient_iso
    let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup (X ⧸ pCore 2 X) := e.isSimpleGroup
    let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    let : IsQuasisimple (alternatingGroup (Fin 5)) := {
      toIsPerfect := inferInstance
      simple := ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
    exact IsQuasisimple.of_mulEquiv e.symm
  exact hX.commutator_eq_bot_of_quasisimple_quotient (hX.map_equiv (MulAut.conj q)) hqX hne
end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
