module

public import CFSG.Quasithin.MainConverse.Transport
public import Theory.GroupTheory.SelfCentralizingNormalPSubgroup
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Suzuki
public import Theory.SpecificGroups.Suzuki.AbelianSubgroups

/-!
# Even characteristic of the concrete Suzuki groups

A maximal 2-local is proper in a nonabelian simple group. Every proper
overgroup of a Suzuki Sylow 2-subgroup normalizes it, and the root group
is self-centralizing. The relative normal p-subgroup criterion then gives
a self-centralizing two-core in each local overgroup of a fixed Sylow subgroup.
Sylow conjugacy gives the source condition E.

Sources: Aschbacher–Smith, Theorem 0.1.2(1), printed p.4 and F.1.3(1),
printed pp.259–260; Huppert–Blackburn, *Finite Groups III*, XI.3.6 and XI.3.10.
-/

namespace CFSG.Quasithin.MainConverse

open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External

public theorem suzuki_evenCharacteristic {m : ℕ} (hm : 1 ≤ m) :
    IsEvenCharacteristic (SuzukiMatrixGroup m) := by
  have hmpos : 0 < m := by omega
  let := (huppert_blackburn_XI_3_6 m hmpos).1
  have hna : ¬ IsMulCommutative (SuzukiMatrixGroup m) := by
    intro hc
    exact suzukiMatrixGroup_not_isSolvable m hmpos
      (Group.isSolvable_of_comm (isMulCommutative_iff.mp hc))
  obtain ⟨T, hT⟩ := suzukiRootSubgroup_isSylow m hmpos
  apply IsEvenCharacteristicAt.all (T := T)
  intro M hM hTM
  apply centralizer_pCore_le_of_normalized 2 (T : Subgroup (SuzukiMatrixGroup m)) M
    T.isPGroup' hTM
  · exact (CFSG.Quasithin.ChapterF.Source.suzuki_rankOneSylowFacts m T).unique_maximal
      M hTM (lt_top_iff_ne_top.mpr (twoLocal_ne_top_of_nonabelian_simple hna hM.1))
  · rw [hT]
    have hcard : 1 < Nat.card (SuzukiRootSubgroup m) := by
      rw [suzukiRootSubgroup_card m hmpos]
      exact one_lt_pow₀ (one_lt_pow₀ (by decide) (by omega)) (by decide)
    let : Nontrivial (SuzukiRootSubgroup m) :=
      Finite.one_lt_card_iff_nontrivial.mp hcard
    obtain ⟨x, hx⟩ := exists_ne (1 : SuzukiRootSubgroup m)
    have hxne : (x : SuzukiMatrixGroup m) ≠ 1 := by
      intro h
      exact hx (Subtype.ext h)
    exact (centralizer_le (Set.singleton_subset_iff.mpr x.property)).trans
      (suzukiRootSubgroup_centralizer_le m hmpos x.property hxne)

public theorem suzuki_evenCharacteristic_of_iso {G : Type*} [Group G] [Finite G]
    {m : ℕ} (hm : 1 ≤ m) (e : G ≃* SuzukiMatrixGroup m) : IsEvenCharacteristic G :=
  evenCharacteristic_of_model_equiv e (suzuki_evenCharacteristic hm)

end CFSG.Quasithin.MainConverse
