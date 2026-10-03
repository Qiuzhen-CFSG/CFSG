module
public import Stellmacher.SectionNine.NineTenFiveResidualDisplacement
public import Stellmacher.SectionNine.NineTenDistanceTwoNeighborhood
/-!
# Residual neighborhood displacement escapes the first module

At length five, retain the actual terminal wreath classification. Every
subgroup containing [W_first,O₂(E_first)] meets the third module outside
the first module. The literal distance-two neighborhood is used throughout.

The third module lies in W_first by critical-path distance. The subgroup
O₂(E_first)∩Q_second lies in the third stabilizer, so its commutator with
V_third lies simultaneously in the supplied overgroup and V_third. If that
intersection lay in V_first, it would contradict the established actual
first/third residual displacement theorem. No stronger edge-generation
assertion or new extraction is used.

This is the obstruction (12) in Stellmacher (9.10), printed p.59, valid for
every overgroup of the indicated residual commutator, including the source's
normal-layer join.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_residual_neighborhood_intersection_not_le_first
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 5)
    (hcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^5)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2)
    (hinter : Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G) = 2^3)
    (Wnew : Subgroup G)
    (hcomm : ⁅DistanceTwoNeighborhoodV ctx.Γ ctx.criticalPath.firstStep,
      twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)⁆ ≤ Wnew) :
    ¬ Wnew ⊓ VAt ctx.Γ (ctx.criticalPath.path ⟨3,by omega⟩) ≤
      VAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : cp.length = 5 := hb
  let second := cp.path ⟨2,by omega⟩
  let third := cp.path ⟨3,by omega⟩
  let Q := twoCoreIn (EAt Γ cp.firstStep)
  let D := Q ⊓ QAt Γ second
  have hthirdW : VAt Γ third ≤ DistanceTwoNeighborhoodV Γ cp.firstStep := by
    apply v_le_distance_two_neighborhood Γ
    have hupper := path_distance_le Γ cp 1 3 (by omega) (by omega)
    rw [cp.path_first] at hupper
    change Γ.distance cp.firstStep third ≤ 2 at hupper
    have htail := path_distance_le Γ cp 3 cp.length (by omega) le_rfl
    rw [cp.path_end] at htail
    have hprefix := nine_eight_adjacent_distance_le Γ (target := cp.a') cp.firstStep_adj
    rw [cp.endpoint_distance] at hprefix
    by_cases hzero : Γ.distance cp.firstStep third = 0
    · have heq := (Γ.distance_zero_iff _ _).mp hzero
      rw [heq] at hprefix
      change Γ.distance third cp.a' ≤ cp.length-3 at htail
      omega
    by_cases hone : Γ.distance cp.firstStep third = 1
    · have hh := nine_eight_adjacent_distance_le Γ (target := cp.a')
        ((adjacent_iff_distance_eq_one Γ).mpr hone)
      change Γ.distance third cp.a' ≤ cp.length-3 at htail
      omega
    omega
  have hDthird : D ≤ GAt Γ third := inf_le_right.trans
    (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core second third
      ((mem_neighborhood_iff_adjacent Γ).mpr (cp.path_adj ⟨2,by omega⟩)) default).2.2)
  have hthirdComm : ⁅VAt Γ third,D⁆ ≤ VAt Γ third :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hDthird.trans (stabilizer_le_normalizer_v Γ third))
  have hnewComm : ⁅VAt Γ third,D⁆ ≤ Wnew :=
    (Subgroup.commutator_mono hthirdW inf_le_left).trans hcomm
  intro hle
  exact nine_ten_five_residual_core_displacement_not_le_intersection ctx hb hcard hmodel hinter
    (le_inf ((le_inf hnewComm hthirdComm).trans hle) hthirdComm)

end Stellmacher.SectionNine
