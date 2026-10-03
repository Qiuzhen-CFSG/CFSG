module
public import Theory.GroupTheory.NormalCenterQuotient
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.IntervalCases

/-!
# A commuting point in a four-subgroup of D8

Let B be any subgroup of order four in the dihedral group of order eight,
and let Z be a normal subgroup of order two. If a point of B commutes with
an element outside B, it lies in Z. No order assumption on either element
or containment assumption between Z and B is required.

The prime-square order theorem makes B abelian, so the point's centralizer
contains B. The additional outside element makes this centralizer larger
than four; Lagrange's theorem then gives the whole group. Thus the point
is central. A normal subgroup of order two is central, and the actual
dihedral center has order two by finite computation, identifying it with Z.

This concrete-group fact is used after the terminal-edge quotient in
Stellmacher (10.1)(a3)(11), Journal of Algebra 190 (1997), printed p.62.
Its statement is independent of the campaign and retains the supplied
four-subgroup and normal two-subgroup.
-/

namespace DihedralGroup

/-- A point in a four-subgroup commuting with an outside element lies in a normal subgroup of order two. -/
public theorem mem_normal_two_of_commuting_outside_four
    (B Z : Subgroup (DihedralGroup 4)) [Z.Normal]
    (hB : Nat.card B = 4) (hZ : Nat.card Z = 2)
    (a u : DihedralGroup 4) (ha : a ∈ B) (hu : u ∉ B) (hcomm : Commute u a) :
    a ∈ Z := by
  let _ : IsMulCommutative B := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hB
  let C := Subgroup.centralizer ({a} : Set (DihedralGroup 4))
  have hBC : B ≤ C := by
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.mpr (setLike_mul_comm (s := B) hb ha)
  have huC : u ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq
  have hlarge : 4 < Nat.card C := by
    have hle := Subgroup.card_le_of_le hBC
    rw [hB] at hle
    apply lt_of_le_of_ne hle
    intro heq
    have hequal : B = C := Subgroup.eq_of_le_of_card_ge hBC (by omega)
    exact hu (hequal.ge huC)
  have hupper : Nat.card C ≤ 8 := by
    simpa only [nat_card] using C.card_le_card_group
  have hdiv : Nat.card C ∣ 8 := by
    simpa only [nat_card] using C.card_subgroup_dvd_card
  have hcard : Nat.card C = 8 := by
    interval_cases h : Nat.card C <;> norm_num at hdiv
    all_goals rfl
  have htop : C = ⊤ := C.eq_top_of_card_eq (by simpa only [nat_card] using hcard)
  have haCenter : a ∈ Subgroup.center (DihedralGroup 4) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ C := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  have hcenterCard : Nat.card (Subgroup.center (DihedralGroup 4)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hZcenter : Z = Subgroup.center (DihedralGroup 4) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.central_of_normal_card_two Z hZ)
      (by rw [hcenterCard, hZ])
  exact hZcenter.ge haCenter

end DihedralGroup
