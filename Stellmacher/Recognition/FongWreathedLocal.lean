module

public import ABG.ChapterII.Section3.CharacteristicPower
public import ABG.ChapterII.Section3.SolvableCharacteristicPower
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Local reduction for Fong's wreathed order-32 recognition

A finite simple group with a wreathed Sylow two-subgroup of height two is
a QD-group. If one involution centralizer is solvable, its source
characteristic power is three, as is that of every involution centralizer.
Each centralizer has a wreathed Sylow subgroup of the original height.

Simplicity excludes a normal subgroup of index two. ABG's wreathed fusion
theorem then gives QD fusion, and the Q-group characteristic-power theorem
applies to the involution centralizers. Solvability forces field order three.
Conjugating the central Sylow involution to any given involution retains
the Sylow height on restriction to its centralizer.

Sources: ABG II.1--3, article pp. 10--23; Fong, *Some Sylow subgroups of
order 32 and a characterization of U(3,3)*, J. Algebra 6 (1967), 65--76,
DOI 10.1016/0021-8693(67)90014-2, for the intended recognition application.
The ambient isomorphism with PSU₃(3) is a separate, unproved step; the
source characteristic datum here only describes an SL₂ constituent of
an involution centralizer modulo its odd core.
-/

namespace Stellmacher.Recognition

open ABG

/-- The wreathed order-32 hypothesis in a simple group gives full QD fusion. -/
public theorem isQDGroup_of_simple_wreathed32
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsWreathedOfHeight S 2) : IsQDGroup G := by
  apply (isQDGroup_iff_no_normal_index_two S (Or.inr ⟨2, hS⟩)).mpr
  intro K hKn hKi
  rcases hKn.eq_bot_or_eq_top with rfl | rfl
  · rw [Subgroup.index_bot] at hKi
    have hdvd := (S : Subgroup G).card_subgroup_dvd_card
    rw [hS.2.1, hKi] at hdvd
    norm_num at hdvd
  · simp at hKi

/-- One solvable involution centralizer forces source characteristic power three. -/
public theorem sourceCharacteristicPower_three_of_simple_wreathed32
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsWreathedOfHeight S 2)
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    HasSourceCharacteristicPower G 3 := by
  have hQD := isQDGroup_of_simple_wreathed32 S hS
  obtain ⟨q, hq, _⟩ := exists_sourceCharacteristicPower hQD
  have hqx := hq.at_involution hQD x hx
  exact hqx.eq_three_of_isSolvable ▸ hq

/-- Full local data at every involution, without an N₂ or local odd-core hypothesis. -/
public theorem involutionCentralizer_data_of_simple_wreathed32
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsWreathedOfHeight S 2)
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))]
    (y : G) (hy : orderOf y = 2) :
    IsQGroup (Subgroup.centralizer ({y} : Set G)) ∧
      HasSourceQCharacteristicPower (Subgroup.centralizer ({y} : Set G)) 3 ∧
      ∃ T : Sylow 2 (Subgroup.centralizer ({y} : Set G)), IsWreathedOfHeight T 2 := by
  classical
  have hQD := isQDGroup_of_simple_wreathed32 S hS
  have hq := sourceCharacteristicPower_three_of_simple_wreathed32 S hS x hx
  refine ⟨(qd_involutionCentralizer_isQGroup hQD y hy).1,
    hq.at_involution hQD y hy, ?_⟩
  obtain ⟨P⟩ := Wreathed.nonempty_presentation hS
  have hclass : HasElementConjugacyClassCount G 2 1 := by
    rcases hQD with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h.2.1
  obtain ⟨r, _, _, hcov⟩ := hclass
  obtain ⟨i, hzi⟩ := hcov P.x ((Subgroup.orderOf_coe P.x).trans P.x_orderOf)
  obtain ⟨j, hyj⟩ := hcov y hy
  have hzy : IsConj (P.x : G) y := hzi.trans ((Subsingleton.elim i j) ▸ hyj.symm)
  obtain ⟨g, hg⟩ := isConj_iff.mp hzy
  let e := S.equivSMul g
  have hT : IsWreathedOfHeight (g • S : Sylow 2 G) 2 := wreathed_equiv e hS
  have hzc : e P.x ∈ Subgroup.center (g • S : Sylow 2 G) := by
    apply Subgroup.mem_center_iff.mpr
    intro t
    obtain ⟨s, rfl⟩ := e.surjective t
    simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp P.x_mem_center s)
  have he : ((e P.x : (g • S : Sylow 2 G)) : G) = y := hg
  have hTC : ((g • S : Sylow 2 G) : Subgroup G) ≤ Subgroup.centralizer {y} := by
    intro t ht
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hh := congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hzc (⟨t, ht⟩ : (g • S : Sylow 2 G)))
    change t * (e P.x).val = (e P.x).val * t at hh
    simpa only [he] using hh
  let T := (g • S : Sylow 2 G).subtype hTC
  let eT : T ≃* (g • S : Sylow 2 G) := Subgroup.subgroupOfEquivOfLe hTC
  exact ⟨T, wreathed_equiv eT.symm hT⟩

end Stellmacher.Recognition
