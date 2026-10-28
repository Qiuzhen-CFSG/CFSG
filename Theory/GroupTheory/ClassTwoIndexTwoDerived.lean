module
public import Theory.GroupTheory.ClassTwoCommutator
public import Mathlib.Algebra.Group.Subgroup.Finite
/-!
# Derived subgroups of index-two subgroups in class-two groups

An abelian subgroup of index at most two in a group with central derived
subgroup of order at most two forces the center to have index at most four:
intersect the abelian subgroup with one outside element's centralizer.
Consequently, when the central quotient has order greater than four and the
derived subgroup has order two, every subgroup of index at most two has the
same derived subgroup. This is the binary hyperplane step in
Meierfrankenfeld--Stellmacher (1993), (3.10)(i), printed pp.880--881.
-/

public noncomputable section
namespace Subgroup.ClassTwo
open Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G]

/-- An abelian subgroup of index at most two bounds the central quotient. -/
theorem center_index_le_four_of_abelian_index_le_two
    (hc : _root_.commutator G≤center G)
    (hcard : Nat.card (_root_.commutator G)≤2)
    (A : Subgroup G) [IsMulCommutative A] (hi : A.index≤2) :
    (center G).index≤4 := by
  by_cases htop : A=⊤
  · have hz : (⊤:Subgroup G)≤center G := by
      intro a _
      apply mem_center_iff.mpr
      intro y
      exact A.le_centralizer (htop ▸ mem_top a) y (htop ▸ mem_top y)
    rw [top_unique hz,index_top]
    decide
  have hi2 : A.index=2 := by
    have hl := one_lt_index_of_ne_top htop
    omega
  have hex : ∃t:G,t∉A := by
    by_contra hn
    push Not at hn
    exact htop (top_unique (fun t _ => hn t))
  obtain ⟨t,ht⟩ := hex
  have hz : A⊓centralizer ({t}:Set G)≤center G := by
    rintro a ⟨ha,hac⟩
    apply mem_center_iff.mpr
    intro y
    by_cases hy : y∈A
    · exact A.le_centralizer ha y hy
    · have hd : y*t⁻¹∈A :=
        (A.mul_mem_iff_of_index_two hi2).mpr (by simpa using iff_of_false hy ht)
      have hh : Commute a (y*t⁻¹) := A.le_centralizer hd a ha
      have hat : Commute a t := mem_centralizer_singleton_iff.mp hac
      simpa using (hh.mul_right hat).symm.eq
  have hci : (centralizer ({t}:Set G)).index≤2 := by
    rw [centralizer_index hc t]
    exact (card_le_of_le (commutator_mono le_top le_rfl)).trans hcard
  exact (index_antitone hz).trans ((index_inf_le (H:=A) (K:=centralizer ({t}:Set G))).trans
    (Nat.mul_le_mul hi hci))

/-- A subgroup of index at most two retains the nontrivial central derived line. -/
theorem commutator_eq_of_index_le_two_of_center_index_gt_four
    (hc : _root_.commutator G≤center G)
    (hcard : Nat.card (_root_.commutator G)=2)
    (hlarge : 4<(center G).index)
    (A : Subgroup G) (hi : A.index≤2) :
    ⁅A,A⁆=_root_.commutator G := by
  have hle : ⁅A,A⁆≤_root_.commutator G := commutator_mono le_top le_top
  have hne : ⁅A,A⁆≠⊥ := by
    intro hz
    let : IsMulCommutative A := le_centralizer_iff_isMulCommutative.mp
      (commutator_eq_bot_iff_le_centralizer.mp hz)
    have hb := center_index_le_four_of_abelian_index_le_two hc hcard.le A hi
    omega
  have hl := (one_lt_card_iff_ne_bot (⁅A,A⁆:Subgroup G)).mpr hne
  exact eq_of_le_of_card_ge hle (by omega)
end Subgroup.ClassTwo
