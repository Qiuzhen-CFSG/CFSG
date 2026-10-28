module

public import CFSG.Quasithin.Chapter14.Section03.Prelim.ThompsonSource.Marking
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.PlaneNoncentralitySource
public import Theory.GroupTheory.Commutator.SmallNormalizedImage

/-!
# The original radical product in 14.7.4(4)

Both Q=O₂(LT) and Q_H=O₂(H) lie in R₁. In the full natural action on V,
R₁ has the point-translation image of order four. The Q_H image is
normalized by L₁. If it had order at most two, L₁ would centralize that
image. Since V=[V,L₁] and [V,Q_H] lies in the central point, the
three-subgroups lemma would make Q_H centralize V, contradicting its
movement of the flag plane. Hence Q_H has the full translation image,
whose kernel is Q, proving QQ_H=R₁ on the literal original subgroups.

The source application derives movement and the commutator identity from
the already explicit earlier 13.3.2 A₅ module classification and setup.
Source: Aschbacher–Smith 14.7.4(1),(4), printed p.1043.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

omit [Finite G] in
private theorem core_le_sylow (H : Subgroup G) (hT : (T : Subgroup G) ≤ H) :
    H.pCoreIn 2 ≤ (T : Subgroup G) :=
  (pCoreIn_le_sylow H (T.subtype hT)).trans_eq (map_subgroupOf_eq_of_le hT)

/-- The LT two-core lies in the point-parabolic two-core. -/
theorem Data.source_Q_le_Ri (_d : Data T L V F W) : Q T L ≤ F.Ri L 1 := by
  have hQ := core_le_sylow (L ⊔ (T : Subgroup G)) le_sup_right
  have hle : Rechoice.group F L ≤ L ⊔ (T : Subgroup G) := Rechoice.group_le_LT
  exact (le_inf (hQ.trans le_sup_right) le_rfl).trans (inf_pCoreIn_le_of_le 2 hle)

/-- The H two-core lies in the same point-parabolic two-core. -/
theorem Data.source_QH_le_Ri (_d : Data T L V F W) : F.H.pCoreIn 2 ≤ F.Ri L 1 := by
  have hQ := core_le_sylow F.H (F.invariant 1)
  exact (le_inf (hQ.trans le_sup_right) le_rfl).trans
    (inf_pCoreIn_le_of_le 2 Rechoice.group_le_H)

/-- The original two-cores generate the point-parabolic two-core. -/
theorem Data.source_core_product (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ ≤ F.Vi 1)
    (hmove : ¬ F.H.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G)) :
    Q T L ⊔ F.H.pCoreIn 2 = F.Ri L 1 := by
  let J := L ⊔ (T : Subgroup G)
  let R := (F.Ri L 1).subgroupOf J
  let N := (F.H.pCoreIn 2).subgroupOf J
  let D := (F.Li L 1).subgroupOf J
  have hRJ : F.Ri L 1 ≤ J := (pCoreIn_le 2 _).trans Rechoice.group_le_LT
  have hNJ : F.H.pCoreIn 2 ≤ J := (core_le_sylow F.H (F.invariant 1)).trans le_sup_right
  have hDJ : F.Li L 1 ≤ J := (F.Li_le L 1).trans (inf_le_left.trans le_sup_left)
  obtain ⟨e,q,hq,hq2,ha,hker,hT,hR⟩ :=
    Chapter14.Section03.ThompsonSource.exists_marking d.natural F structural
  have hkerMap : q.ker.map J.subtype = Q T L := by
    rw [hker, subgroupOf_map_subtype, inf_comm]
    exact d.natural.centralizer_LT structural
  have hNle : N.map q ≤ Matrix.PSL3Two.MarkedAutomorphisms.pointV := by
    rw [←hR]
    exact map_mono (subgroupOf_mono J (d.source_QH_le_Ri))
  have hn : D ≤ normalizer (N : Set J) := by
    intro a ha
    apply mem_normalizer_iff.mpr
    intro x
    change (x : G) ∈ F.H.pCoreIn 2 ↔
      (a : G) * (x : G) * (a : G)⁻¹ ∈ F.H.pCoreIn 2
    exact mem_normalizer_iff.mp
      ((F.H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H)))
          ((F.Li_le L 1 ha).2)) _
  have hlarge : 2 < Nat.card (N.map q) := by
    by_contra hc
    have hDN := commutator_le_ker_of_normalized_image_card_le_two q D N hn (by omega)
    have hDNQ : ⁅F.Li L 1,F.H.pCoreIn 2⁆ ≤ Q T L := by
      have hh := map_mono (f := J.subtype) hDN
      rw [map_commutator, map_subgroupOf_eq_of_le hDJ,
        map_subgroupOf_eq_of_le hNJ, hkerMap] at hh
      exact hh
    have hQV : Q T L ≤ centralizer (V : Set G) := by
      change (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ _
      rw [← d.natural.centralizer_LT structural]
      exact inf_le_right
    have hpoint : F.H ≤ centralizer (F.Vi 1 : Set G) :=
      normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
    have h1 : ⁅⁅F.Li L 1,F.H.pCoreIn 2⁆,V⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (hDNQ.trans hQV)
    have h2 : ⁅⁅F.H.pCoreIn 2,V⁆,F.Li L 1⁆ = ⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      have hp : ⁅F.H.pCoreIn 2,V⁆ ≤ F.Vi 1 := by
        rw [commutator_comm]
        exact (commutator_mono (V_le_U F) le_rfl).trans hcomm
      exact hp.trans (le_centralizer_iff.mp ((F.Li_le L 1).trans (inf_le_right.trans hpoint)))
    have hz := commutator_commutator_eq_bot_of_rotate h1 h2
    rw [←d.seed_eq_commutator_point_residual] at hz
    exact hmove ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)).trans
      (centralizer_le (F.le_seed 2)))
  have hc : Nat.card (N.map q) = 4 := by
    have hd := card_dvd_of_le hNle
    rw [Matrix.PSL3Two.MarkedAutomorphisms.card_pointV] at hd
    have hb := Nat.le_of_dvd (by decide : 0 < 4) hd
    interval_cases h : Nat.card (N.map q) <;> norm_num [h] at *
  have he : N.map q = R.map q := by
    rw [hR]
    exact eq_of_le_of_card_ge hNle (by rw [hc, Matrix.PSL3Two.MarkedAutomorphisms.card_pointV])
  have hRN : R ≤ N ⊔ q.ker := by
    rw [←comap_map_eq]
    exact (map_le_iff_le_comap).mp he.ge
  have hh := map_mono (f := J.subtype) hRN
  rw [map_subgroupOf_eq_of_le hRJ, Subgroup.map_sup, map_subgroupOf_eq_of_le hNJ, hkerMap] at hh
  exact le_antisymm (sup_le d.source_Q_le_Ri d.source_QH_le_Ri) (by simpa [sup_comm] using hh)


/-- The literal star quotient kills Q_H and preserves the product identity. -/
theorem Data.source_Q_star_eq_Ri (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ ≤ F.Vi 1)
    (hmove : ¬ F.H.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G)) :
    star F (Q T L) = star F (F.Ri L 1) := by
  have he := congrArg (fun A : Subgroup G => star F A)
    (d.source_core_product structural hcomm hmove)
  change ((Q T L ⊔ F.H.pCoreIn 2).subgroupOf F.H).map (starMap F) = _ at he
  rw [subgroupOf_sup (Q_le_H F) (pCoreIn_le 2 F.H), Subgroup.map_sup] at he
  have hz : ((F.H.pCoreIn 2).subgroupOf F.H).map (starMap F) = ⊥ := by
    change (((pCore 2 F.H).map F.H.subtype).comap F.H.subtype).map (starMap F) = ⊥
    rw [comap_map_eq_self_of_injective F.H.subtype_injective,
      Subgroup.map_eq_bot_iff, starMap, QuotientGroup.ker_mk']
  simpa only [star,hz,sup_bot_eq] using he

/-- The genuine earlier module classification discharges movement and commutator inputs. -/
theorem Data.source_core_product_of_source1332 (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (earlier : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u}) :
    Q T L ⊔ F.H.pCoreIn 2 = F.Ri L 1 ∧
      star F (Q T L) = star F (F.Ri L 1) := by
  have hc := d.sectionCentralizer_of_earlier_setup structural uniqueness
  have hm := d.plane_noncentrality_of_source1332 earlier hc
  have hcomm := (d.U_core_commutator_eq_point_of_source1332 earlier structural uniqueness).le
  exact ⟨d.source_core_product structural hcomm hm,d.source_Q_star_eq_Ri structural hcomm hm⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
