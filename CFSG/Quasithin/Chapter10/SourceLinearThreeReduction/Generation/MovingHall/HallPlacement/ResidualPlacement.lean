module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.SemilinearRigidity
public import Theory.GroupTheory.Hall.ReverseNormalizer
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Original Hall placement from Borel normalization of O²(H)

The actual odd Hall B lies in the two-residual of H. Once the original
orbit Borel normalizes that residual, its B-invariant odd torus C also
normalizes B: the odd intersection CB ∩ O²(H) lies in H ∩ M and equals B
by Hall maximality. The same torus then removes both field factors in the
literal quotient action, and coprime lifting places B in the original Borel.

This discharges all algebra following the claim B₀ ≤ N_G(O²(H)) on
printed p.746. That geometric claim remains with the moving-Hall source
owner and is explicit in the final consumer; this is not unconditional
`NaturalHallPlacementAt`.
Source: Aschbacher–Smith 10.2.3, printed pp.745–746.
-/

public section

namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Subgroup Theory.GroupTheory Chapter3.Section02
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The source claim B₀ ≤ N_G(O²(H)) gives reverse normalization of the
chosen invariant torus. This is the actual two-residual, not the two-core. -/
theorem invariant_torus_normalizes_hall_of_borel_normalizes_residual
    {H : Subgroup G} {B : Subgroup H} (c : MovingHall.Context D H B)
    (hnorm : sourceOrbitBorel T L ≤ normalizer ((pResidual 2 H).map H.subtype : Set G))
    (C : Subgroup G) (hC : C ≤ sourceOrbitBorel T L)
    (hHall : IsHallSubgroup Subgroup.OddHall.oddPrimes
      (C.subgroupOf (sourceOrbitBorel T L)))
    (hBC : B.map H.subtype ≤ normalizer (C : Set G)) :
    C ≤ normalizer (B.map H.subtype : Set G) := by
  let X := B.map H.subtype
  let A := H ⊓ D.maximalLocal
  let R := (pResidual 2 H).map H.subtype
  have hXA : X ≤ A := le_inf (map_subtype_le B) (map_le_iff_le_comap.mpr c.hall_le)
  have hXHall : IsHallSubgroup Subgroup.OddHall.oddPrimes (X.subgroupOf A) := by
    have hc : Nat.card (X.subgroupOf A) =
        Nat.card (B.subgroupOf (D.maximalLocal.subgroupOf H)) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hXA).toEquiv,
        card_map_of_injective H.subtype_injective,
        Nat.card_congr (subgroupOfEquivOfLe c.hall_le).toEquiv]
    have hi : (X.subgroupOf A).index =
        (B.subgroupOf (D.maximalLocal.subgroupOf H)).index := by
      change X.relIndex A = B.relIndex (D.maximalLocal.subgroupOf H)
      have hm : (D.maximalLocal.subgroupOf H).map H.subtype = A := by
        rw [subgroupOf_map_subtype,inf_comm]
      rw [←hm]
      exact relIndex_map_map_of_injective B _ H.subtype_injective
    exact ⟨fun p hp => c.hall.p_in_pi_of_p_dvd_card p (hc ▸ hp),
      fun p hp => c.hall.p_in_pi_of_p_dvd_index p (hi ▸ hp)⟩
  have hoC : Odd (Nat.card C) := by
    have hh := Subgroup.OddHall.odd_hall_odd hHall
    rwa [Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv] at hh
  have hBR : B ≤ pResidual 2 H := by
    apply le_pResidual_of_isPPerfect
    intro N hn htwo
    let := hn
    apply index_eq_one.mp
    change Nat.card (B ⧸ N) = 1
    apply htwo.card_eq_or_dvd.resolve_right
    intro hd
    exact (Nat.not_even_iff_odd.mpr c.hall_odd)
      (even_iff_two_dvd.mpr (hd.trans N.card_quotient_dvd_card))
  have hCM : C ≤ D.maximalLocal :=
    (((hC.trans (map_subtype_le _)).trans inf_le_left).trans (localOrbit T L).le_normalizer)
  exact Subgroup.OddHall.reverse_normalizes_of_normalizes_intersection A X C R hXA hXHall
    hoC hBC (map_mono hBR) (hC.trans hnorm)
    (le_inf (inf_le_right.trans (map_subtype_le _))
      (inf_le_left.trans (sup_le hCM (map_le_iff_le_comap.mpr c.hall_le))))

/-- The original Borel-normalization claim suffices for the complete literal
Hall placement, including field elimination and coprime-kernel lifting. -/
theorem hall_le_borel_of_borel_normalizes_residual
    {H : Subgroup G} {B : Subgroup H} (c : MovingHall.Context D H B)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hnorm : sourceOrbitBorel T L ≤ normalizer ((pResidual 2 H).map H.subtype : Set G)) :
    B.map H.subtype ≤ sourceOrbitBorel T L :=
  hall_le_borel_of_invariant_tori_normalize D c e
    (invariant_torus_normalizes_hall_of_borel_normalizes_residual D c hnorm)

end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
