module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleHeld
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.TwoRank
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary
public import Theory.SpecificGroups.Rudvalis.Multiplier.Universe

/-!
# The original fixed line in the HS and Ru covering cases

The HS rank bound forces the image of the original order-32 moved subgroup
under the canonical central projection to have order sixteen. The kernel is
therefore its original fixed line. For Ru the involution-centralizer argument
already gives that kernel. The genuine multiplier bounds identify this line
with the entire center of the quasisimple residual in both cases.

These are the remaining double-cover cases of the source catalogue inspection.
The projection is the actual map out of K_v and the fixed line remains a
subgroup of the original V; no new ambient or module marking is introduced.
Source: Aschbacher--Smith, proof of 12.6.12, pp.825--826, and I.1.3, p.407.
The HS/Ru exclusions and the later block and splitting arguments remain open.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The literal moved subgroup has image of order sixteen in the HS row. -/
theorem SourceHypothesis.nonsingular_hs_moved_image_card
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hmodel : Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)) :
    let C := Kv (v : G)
    Nat.card (((Vv L V (v : G)).subgroupOf C).map (QuotientGroup.mk' (center C))) = 16 := by
  let C := Kv (v : G)
  let W := ((Vv L V (v : G)).subgroupOf C).map (QuotientGroup.mk' (center C))
  obtain ⟨e⟩ := hmodel
  obtain ⟨_,_,_,_,he,_,_⟩ := H.nonsingular_centralQuotient_local_marking D v hv
  let : IsElementaryAbelian 2 W := he
  have hb := (primeRank_le_iff_elementary_card_le Sporadic.LeechRelated.HS.Carrier).mp
    Sporadic.LeechRelated.HS.twoRank_le_four (W.map e.toMonoidHom)
    (IsElementaryAbelian.map e.toMonoidHom)
  rw [card_map_of_injective e.injective] at hb
  exact Nat.le_antisymm hb (H.nonsingular_centralQuotient_moved_card D v hv)

private theorem fixed_line_le_center_of_image_card
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hc : Nat.card (((Vv L V (v : G)).subgroupOf (Kv (v : G))).map
      (QuotientGroup.mk' (center (Kv (v : G))))) = 16) :
    (ZV (Lv L (v : G)) (Vv L V (v : G))).subgroupOf (Kv (v : G)) ≤
      center (Kv (v : G)) := by
  let C := Kv (v : G)
  let W := Vv L V (v : G)
  let Z := ZV (Lv L (v : G)) W
  have hWC : W ≤ C := (H.nonsingular_component_rank D v hv).1
  have hLC : Lv L (v : G) ≤ C := Lv_le_Kv_of_A6 L _
    (Classical.choice (D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv))
  let f := (QuotientGroup.mk' (center C)).comp (inclusion hWC)
  have hr : Nat.card f.range = 16 := by
    simpa only [f,MonoidHom.range_comp,inclusion_range] using hc
  have hk : Nat.card f.ker = 2 := by
    have hh := f.ker.card_mul_index
    rw [index_ker,hr,D.nonsingular_moved_card H.chosen v hv] at hh
    omega
  have hle : f.ker ≤ Z.subgroupOf W := by
    intro w hw
    have hz := (QuotientGroup.eq_one_iff _).mp (show f w = 1 from hw)
    refine ⟨w.property,?_⟩
    intro b hb
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨b,hLC hb⟩)
  have heq : f.ker = Z.subgroupOf W := eq_of_le_of_card_ge hle (by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe (show Z ≤ W from inf_le_left)).toEquiv,
      D.nonsingular_moved_fixed_card H.chosen v hv])
  intro z hz
  have hkz : (⟨(z : G),hz.1⟩ : W) ∈ f.ker := heq.symm ▸ hz
  exact (QuotientGroup.eq_one_iff _).mp hkz

private theorem fixed_line_eq_center_of_bound
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hle : (ZV (Lv L (v : G)) (Vv L V (v : G))).subgroupOf (Kv (v : G)) ≤
      center (Kv (v : G)))
    (hb : Nat.card (center (Kv (v : G))) ≤ 2) :
    (ZV (Lv L (v : G)) (Vv L V (v : G))).subgroupOf (Kv (v : G)) =
      center (Kv (v : G)) := by
  apply eq_of_le_of_card_ge hle
  have hz : ZV (Lv L (v : G)) (Vv L V (v : G)) ≤ Kv (v : G) :=
    inf_le_left.trans (H.nonsingular_component_rank D v hv).1
  rwa [Nat.card_congr (subgroupOfEquivOfLe hz).toEquiv,
    D.nonsingular_moved_fixed_card H.chosen v hv]

/-- The HS covering center is exactly the original local fixed line. -/
theorem SourceHypothesis.nonsingular_hs_fixed_line_eq_center
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hmodel : Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)) :
    (ZV (Lv L (v : G)) (Vv L V (v : G))).subgroupOf (Kv (v : G)) =
      center (Kv (v : G)) := by
  let := hK
  have hle := fixed_line_le_center_of_image_card H D v hv
    (H.nonsingular_hs_moved_image_card D v hv hmodel)
  apply fixed_line_eq_center_of_bound H D v hv hle
  obtain ⟨e⟩ := hmodel
  let c := PerfectCentralCovering.centralQuotientCover e
  have hp := Theory.SpecificGroups.J2HSMultipliers.HS.kernel_isPGroup
    c.toMonoidHom c.surjective c.ker_le_center
  have hh := Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.not_four_dvd_card_kernel
    c.toMonoidHom c.surjective c.ker_le_center hp
  have hb := Theory.SpecificGroups.J2HSMultipliers.HS.card_kernel_le_two_of_not_four_dvd
    c.toMonoidHom c.surjective c.ker_le_center hh
  rwa [PerfectCentralCovering.centralQuotientCover_ker] at hb

/-- The Ru covering center is exactly the original local fixed line. -/
theorem SourceHypothesis.nonsingular_ru_fixed_line_eq_center
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hmodel : Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Rudvalis.Model)) :
    (ZV (Lv L (v : G)) (Vv L V (v : G))).subgroupOf (Kv (v : G)) =
      center (Kv (v : G)) := by
  let := hK
  apply fixed_line_eq_center_of_bound H D v hv
    (H.nonsingular_ru_fixed_line_le_center D v hv hmodel)
  obtain ⟨e⟩ := hmodel
  have hb := Rudvalis.Multiplier.cover_kernel_card_le_two_any_universe
    (PerfectCentralCovering.centralQuotientCover e)
  rwa [PerfectCentralCovering.centralQuotientCover_ker] at hb

/-- Both remaining covering cases have center of order two, obtained from the
actual fixed line rather than supplied as a multiplier hypothesis. -/
theorem SourceHypothesis.nonsingular_hs_ru_center_card
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hmodel : Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Rudvalis.Model)) :
    Nat.card (center (Kv (v : G))) = 2 := by
  have heq : (ZV (Lv L (v : G)) (Vv L V (v : G))).subgroupOf (Kv (v : G)) =
      center (Kv (v : G)) := by
    rcases hmodel with h | h
    · exact H.nonsingular_hs_fixed_line_eq_center D v hv hK h
    · exact H.nonsingular_ru_fixed_line_eq_center D v hv hK h
  have hZ : ZV (Lv L (v : G)) (Vv L V (v : G)) ≤ Kv (v : G) :=
    inf_le_left.trans (H.nonsingular_component_rank D v hv).1
  rw [←heq,Nat.card_congr (subgroupOfEquivOfLe hZ).toEquiv]
  exact D.nonsingular_moved_fixed_card H.chosen v hv

end CFSG.Quasithin.Chapter12.Section06
