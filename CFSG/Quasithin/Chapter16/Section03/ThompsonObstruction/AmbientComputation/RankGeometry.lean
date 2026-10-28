module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.Contracts
public import Theory.GroupTheory.CyclicIndexTwoElementary
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ElementaryRank

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.RankGeometry.ComponentGeometry
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.RankGeometry.MarkedAction

/-!
# Rank geometry for the ambient Thompson calculation

The dihedral or semidihedral shape of T_C bounds its elementary subgroups
by four. An actual identification L ≃ A₆ bounds elementary action images
by eight. Kernel–image counting and the rank-five local Sylow input then
force all three ranks and the orders of both parts of every maximum
elementary subgroup. The relative Sylow intersection identifies T_L with
D₈; its characteristic center of order two is centralized by T.

The marked S₈ identification supplies the compatible A₆ identification
and identifies the preimage of its natural S₆ with T₀. Thus `rankGeometry`
constructs all these conclusions from `Prepared` and the local rank-five
input. The Thompson decomposition in 16.3.12 is a separate calculation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.3.12 and the following paragraph, printed pp.1181–1182 / PDF pp.1198–1199.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
open Subgroup Stellmacher ChapterB
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

private theorem elementary_bound_of_cyclic_index_two
    {H K : Type*} [Group H] [Group K] (e : H ≃* K)
    (C : Subgroup K) [IsCyclic C] (hC : C.index = 2)
    (A : Subgroup H) [IsElementaryAbelian 2 A] : Nat.card A ≤ 4 := by
  let : IsElementaryAbelian 2 (A.map e.toMonoidHom) := IsElementaryAbelian.map _
  have hb := card_le_four_of_pow_two_of_cyclic_index_two C hC (A.map e.toMonoidHom)
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (A.map e.toMonoidHom)))
  rwa [card_map_of_injective e.injective] at hb

omit [Finite G] in
theorem centralizer_elementary_card_le_four (d : Prepared T z t L)
    (A : Subgroup G) (hA : A ≤ commutingSylow T L) [IsElementaryAbelian 2 A] :
    Nat.card A ≤ 4 := by
  let B := A.subgroupOf (commutingSylow T L)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hA
  have hc : Nat.card B = Nat.card A := Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv
  rw [← hc]
  rcases d.shape.model with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · let C := zpowers (DihedralGroup.r (1 : ZMod (2 ^ n)))
    have hi : C.index = 2 := by
      have h := C.card_mul_index
      rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one, DihedralGroup.nat_card] at h
      nlinarith [pow_pos (by decide : 0 < (2 : ℕ)) n]
    exact elementary_bound_of_cyclic_index_two e C hi B
  · let C := zpowers (Semidihedral.standardRotation n hn)
    have hi : C.index = 2 := by
      have h := C.card_mul_index
      rw [Nat.card_zpowers, Semidihedral.standardRotation_order, Semidihedral.standardModel_card] at h
      have hp : 2 ^ n = 2 ^ (n - 1) * 2 := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hp] at h
      nlinarith [pow_pos (by decide : 0 < (2 : ℕ)) (n - 1)]
    exact elementary_bound_of_cyclic_index_two e C hi B

omit [Finite G] in
theorem card_intersection_mul_actionImage (d : Prepared T z t L)
    (A : Subgroup G) (hA : A ≤ (T : Subgroup G)) :
    Nat.card ↥(A ⊓ commutingSylow T L) * Nat.card (actionImage d A) = Nat.card A := by
  let f := (componentAction d).comp (inclusion hA)
  have hker (a : A) : a ∈ f.ker ↔ (a : G) ∈ commutingSylow T L := by
    change inclusion hA a ∈ (componentAction d).ker ↔ _
    rw [componentAction_ker]
    rfl
  let e : f.ker ≃* ↥(A ⊓ commutingSylow T L) := {
    toFun a := ⟨a.val, a.val.property, (hker a.val).mp a.property⟩
    invFun a := ⟨⟨a.val, a.property.1⟩, (hker _).mpr a.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  have hr : f.range = actionImage d A := by
    rw [MonoidHom.range_comp, inclusion_range]
    rfl
  have h := f.ker.card_mul_index
  rw [index_ker, hr, Nat.card_congr e.toEquiv] at h
  exact h

omit [Finite G] in
/-- Transporting automorphisms along an actual A₆ identification bounds every
 elementary two-subgroup of the action codomain. -/
theorem action_elementary_card_le_eight (e : L ≃* AlternatingSix.ShadowLocal.A6)
    (E : Subgroup (MulAut L)) [IsElementaryAbelian 2 E] : Nat.card E ≤ 8 := by
  let a := MulAut.congr e
  let : IsElementaryAbelian 2 (E.map a.toMonoidHom) := IsElementaryAbelian.map _
  have h := AlternatingSix.ShadowLocal.elementary_card_le_eight (E.map a.toMonoidHom)
  rwa [card_map_of_injective a.injective] at h

private theorem rank_le_of_card_bound {H : Type*} [Group H] [Finite H]
    (S : Subgroup H) (n : ℕ)
    (h : ∀ A : Subgroup H, A ≤ S → IsElementaryAbelian 2 A → Nat.card A ≤ 2 ^ n) :
    twoRank S ≤ n := by
  obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty S
  have hh := Nat.log_mono_right (h A hA.1 hA.2.1) (b := 2)
  rw [Nat.log_pow (by decide : 1 < 2)] at hh
  rwa [card_eq_elementaryAbelianMaxOrder S A hA] at hh

private theorem card_witness_le_rank {H : Type*} [Group H] [Finite H]
    (S A : Subgroup H) (hAS : A ≤ S) [IsElementaryAbelian 2 A] (n : ℕ)
    (hc : Nat.card A = 2 ^ n) : n ≤ twoRank S := by
  obtain ⟨B, hB⟩ := elementaryAbelianMaxSubgroups_nonempty S
  have hh := Nat.log_mono_right (hB.2.2 A hAS inferInstance) (b := 2)
  rwa [hc, Nat.log_pow (by decide : 1 < 2), card_eq_elementaryAbelianMaxOrder S B hB] at hh

theorem rank_and_maximal_cards (d : Prepared T z t L)
    (hP : twoRank (localSylow d.P) = 5) (e : L ≃* AlternatingSix.ShadowLocal.A6) :
    twoRank (T : Subgroup G) = 5 ∧
    twoRank (commutingSylow T L) = 2 ∧
    twoRank (componentAction d).range = 3 ∧
    ∀ A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G),
      Nat.card ↥(A ⊓ commutingSylow T L) = 4 ∧ Nat.card (actionImage d A) = 8 := by
  have hbound (A : Subgroup G) (hAT : A ≤ (T : Subgroup G))
      (hEA : IsElementaryAbelian 2 A) : Nat.card A ≤ 32 := by
    let : IsElementaryAbelian 2 A := hEA
    let : IsElementaryAbelian 2 (A ⊓ commutingSylow T L : Subgroup G) :=
      IsElementaryAbelian.of_le inf_le_left
    let : IsElementaryAbelian 2 (A.subgroupOf (T : Subgroup G)) :=
      IsElementaryAbelian.subgroupOf hAT
    let : IsElementaryAbelian 2 (actionImage d A) := IsElementaryAbelian.map _
    have hc := centralizer_elementary_card_le_four d (A ⊓ commutingSylow T L) inf_le_right
    have hi := action_elementary_card_le_eight e (actionImage d A)
    have hm := card_intersection_mul_actionImage d A hAT
    nlinarith
  have hr : twoRank (T : Subgroup G) = 5 := le_antisymm
    (rank_le_of_card_bound (T : Subgroup G) 5 hbound) (five_le_rank d hP)
  have hcards (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G)) :
      Nat.card ↥(A ⊓ commutingSylow T L) = 4 ∧ Nat.card (actionImage d A) = 8 := by
    let : IsElementaryAbelian 2 A := hA.2.1
    let : IsElementaryAbelian 2 (A ⊓ commutingSylow T L : Subgroup G) :=
      IsElementaryAbelian.of_le inf_le_left
    let : IsElementaryAbelian 2 (A.subgroupOf (T : Subgroup G)) :=
      IsElementaryAbelian.subgroupOf hA.1
    let : IsElementaryAbelian 2 (actionImage d A) := IsElementaryAbelian.map _
    have hc := centralizer_elementary_card_le_four d (A ⊓ commutingSylow T L) inf_le_right
    have hi := action_elementary_card_le_eight e (actionImage d A)
    have hm := card_intersection_mul_actionImage d A hA.1
    have ha : Nat.card A = 32 := by
      rw [card_eq_elementaryAbelianMaxOrder _ _ hA, maxOrder_eq_two_pow_rank, hr]
      rfl
    constructor <;> nlinarith
  obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty (T : Subgroup G)
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 (A ⊓ commutingSylow T L : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 (A.subgroupOf (T : Subgroup G)) :=
    IsElementaryAbelian.subgroupOf hA.1
  let : IsElementaryAbelian 2 (actionImage d A) := IsElementaryAbelian.map _
  refine ⟨hr, le_antisymm ?_ ?_, le_antisymm ?_ ?_, hcards⟩
  · apply rank_le_of_card_bound _ 2
    intro B hB he
    let := he
    exact centralizer_elementary_card_le_four d B hB
  · exact card_witness_le_rank _ _ inf_le_right 2 (hcards A hA).1
  · apply rank_le_of_card_bound _ 3
    intro B _ he
    let := he
    exact action_elementary_card_le_eight e B
  · exact card_witness_le_rank (componentAction d).range (actionImage d A) (map_le_range _ _) 3 (hcards A hA).2

/-- Once the actual natural action has been identified, the rank-three image
places each maximum elementary subgroup in T₀. -/
theorem maximal_le_smallGroup_of_natural_preimage (d : Prepared T z t L)
    (hP : twoRank (localSylow d.P) = 5) (e : L ≃* AlternatingSix.ShadowLocal.A6)
    (hnatural : AlternatingSix.ShadowLocal.natural.comap
      ((MulAut.congr e).toMonoidHom.comp (componentAction d)) =
        (smallGroup d).subgroupOf (T : Subgroup G)) :
    ∀ A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G), A ≤ smallGroup d := by
  intro A hA
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 (A.subgroupOf (T : Subgroup G)) :=
    IsElementaryAbelian.subgroupOf hA.1
  let : IsElementaryAbelian 2 (actionImage d A) := IsElementaryAbelian.map _
  let a := MulAut.congr e
  let E := (actionImage d A).map a.toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hcard : Nat.card E = 8 := by
    rw [card_map_of_injective a.injective]
    exact (rank_and_maximal_cards d hP e).2.2.2 A hA |>.2
  have hE := AlternatingSix.ShadowLocal.elementary_le_natural_of_eight_le E hcard.ge
  intro x hx
  have hm : a (componentAction d ⟨x, hA.1 hx⟩) ∈ E :=
    mem_map_of_mem _ (mem_map_of_mem _ hx)
  have hn := hE hm
  have hp : (⟨x, hA.1 hx⟩ : T) ∈ AlternatingSix.ShadowLocal.natural.comap
      (a.toMonoidHom.comp (componentAction d)) := hn
  rw [hnatural] at hp
  exact hp

/-- All rank-geometry conclusions from a compatible natural-action
identification, supplied by the marked enlargement in `rankGeometry`. -/
theorem rankGeometry_of_natural_preimage (d : Prepared T z t L)
    (hP : twoRank (localSylow d.P) = 5) (e : L ≃* AlternatingSix.ShadowLocal.A6)
    (hnatural : AlternatingSix.ShadowLocal.natural.comap
      ((MulAut.congr e).toMonoidHom.comp (componentAction d)) =
        (smallGroup d).subgroupOf (T : Subgroup G)) : RankGeometry d := by
  obtain ⟨hr, hc, ha, hcards⟩ := rank_and_maximal_cards d hP e
  have hD := component_dihedral_of_equiv d e
  exact {
    rank := hr
    centralizer_rank := hc
    action_rank := ha
    maximal_le := maximal_le_smallGroup_of_natural_preimage d hP e hnatural
    maximal_intersection := fun A hA => (hcards A hA).1
    maximal_image := fun A hA => (hcards A hA).2
    component_dihedral := hD
    component_center_central := component_center_central_of_dihedral d hD }

/-- The marked A₆ action and local rank-five input give the complete rank
geometry, including maximum elementary subgroup placement in T₀. -/
theorem rankGeometry (d : Prepared T z t L)
    (hP : twoRank (localSylow d.P) = 5) : RankGeometry d := by
  obtain ⟨e, hn⟩ := exists_marked_natural_preimage d
  exact rankGeometry_of_natural_preimage d hP e hn

end CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
