module

public import Theory.GroupTheory.Hall.NormalizedOddActors
public import Theory.SpecificGroups.SL2.PairSylowSolvability
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Borel

/-!
# An invariant odd Hall subgroup of the original Borel

The actual exchanged SL₂ pair quotient has solvable Sylow normalizer;
solvability lifts through the two-core to the literal source Borel
`O²(N_{L₀}(T ∩ L₀))`. The original Hall actor normalizes that Borel.
A Hall subgroup in their solvable join containing the actor intersects the
Borel in an actor-invariant odd Hall subgroup containing the actor's orbit
intersection. No additional choice or invariance hypothesis is required.

Source: Aschbacher--Smith, 10.2.3, printed p.745, the construction of a
`B_H`-invariant odd Hall subgroup of `B₀` containing `B⁺`.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
include D

omit D [Finite G] in
/-- The ambient normalizer restricted to the orbit is its intrinsic Sylow normalizer. -/
theorem source_orbit_sylow_normalizer_eq
    (S : Sylow 2 (localOrbit T L))
    (hS : (S : Subgroup (localOrbit T L)) = (T : Subgroup G).subgroupOf (localOrbit T L)) :
    (sourceOrbitSylowNormalizer T L).subgroupOf (localOrbit T L) =
      normalizer (S : Set (localOrbit T L)) := by
  let R := localOrbit T L
  change (R ⊓ normalizer ((T : Subgroup G) ⊓ R : Set G)).subgroupOf R = _
  rw [inf_comm R,inf_subgroupOf_right]
  change (normalizer (((T : Subgroup G) ⊓ R : Subgroup G) : Set G)).subgroupOf R = _
  rw [subgroupOf_normalizer_eq (show (T : Subgroup G) ⊓ R ≤ R from inf_le_right),
    inf_subgroupOf_right,←hS]
  rfl

theorem source_sl2_sylow_normalizer_solvable
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Group.IsSolvable (sourceOrbitSylowNormalizer T L) := by
  let := D.quasisimple
  let : IsQuasisimple SL(2,F) := IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup (SL(2,F) ⧸ center SL(2,F)) := IsQuasisimple.simple
  let : IsSimpleGroup SL(2,F) :=
    ((QuotientGroup.quotientMulEquivOfEq
      (Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot (F := F))).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  let R := localOrbit T L
  obtain ⟨S,hS⟩ := source_orbit_sylow_intersection D
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp hn
  obtain ⟨q,hq,hk,_,_⟩ := marked_pair_projection D e hn ht htn
  let Sb := S.mapSurjective hq
  let : Group.IsSolvable (normalizer (Sb : Set (SL(2,F) × SL(2,F)))) :=
    Matrix.SpecialLinearGroup.pair_sylow_normalizer_solvable Sb
  let : Group.IsNilpotent (pCore 2 R) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable q.ker := hk.symm ▸ inferInstance
  let K := (normalizer (Sb : Set (SL(2,F) × SL(2,F)))).comap q
  let : Group.IsSolvable K := isSolvable_comap_of_solvable_ker q _
  have hSK : normalizer (S : Set R) ≤ K :=
    map_le_iff_le_comap.mp (le_normalizer_map q)
  have he := source_orbit_sylow_normalizer_eq S hS
  let : Group.IsSolvable ((sourceOrbitSylowNormalizer T L).subgroupOf R) :=
    Group.isSolvable_of_isSolvable_injective
      (inclusion_injective (he.symm ▸ hSK))
  exact Group.isSolvable_of_surjective
    (f := (subgroupOfEquivOfLe (show sourceOrbitSylowNormalizer T L ≤ R from inf_le_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show sourceOrbitSylowNormalizer T L ≤ R from inf_le_left)).surjective

theorem source_sl2_borel_solvable
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Group.IsSolvable (sourceOrbitBorel T L) := by
  let := source_sl2_sylow_normalizer_solvable D e hn
  exact Group.isSolvable_of_surjective
    ((sourceOrbitSylowNormalizer T L).subtype.subgroupMap_surjective
      (pResidual 2 (sourceOrbitSylowNormalizer T L)))

theorem hall_normalizes_source_borel {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    B.map H.subtype ≤ normalizer (sourceOrbitBorel T L : Set G) := by
  have hBN : B.map H.subtype ≤ normalizer (sourceOrbitSylowNormalizer T L : Set G) := by
    exact (le_inf (map_le_iff_le_comap.mpr c.hall_le)
      ((hall_normalizes_orbit_sylow D c e).trans
        (normalizer ((T : Subgroup G) ⊓ localOrbit T L : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact hBN.trans (normalizer_le_normalizer_characteristic_image
    (sourceOrbitSylowNormalizer T L) (pResidual 2 (sourceOrbitSylowNormalizer T L)))

theorem exists_hall_invariant_source_borel {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    ∃ C : Subgroup G, C ≤ sourceOrbitBorel T L ∧
      IsHallSubgroup Subgroup.OddHall.oddPrimes (C.subgroupOf (sourceOrbitBorel T L)) ∧
      B.map H.subtype ≤ normalizer (C : Set G) ∧
      B.map H.subtype ⊓ localOrbit T L ≤ C := by
  let A := B.map H.subtype
  let : Group.IsSolvable B := Group.isSolvable_of_comm (isMulCommutative_iff.mp c.abelian)
  let : Group.IsSolvable A := Group.isSolvable_of_surjective
    (H.subtype.subgroupMap_surjective B)
  let : Group.IsSolvable (sourceOrbitBorel T L) := source_sl2_borel_solvable D e c.nonnormal
  have ho : Odd (Nat.card A) := by
    rw [card_map_of_injective H.subtype_injective]
    exact hall_odd D c
  obtain ⟨C,hC,hHall,hAC,hcontain⟩ := Subgroup.OddHall.exists_actor_invariant_hall
    (sourceOrbitBorel T L) A (hall_normalizes_source_borel D c e) ho
  refine ⟨C,hC,hHall,hAC,?_⟩
  exact (le_inf inf_le_left (hall_orbit_intersection_le_borel D c e)).trans hcontain

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
