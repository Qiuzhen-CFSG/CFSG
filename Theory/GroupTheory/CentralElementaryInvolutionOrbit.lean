module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Elementary groups covered by a central subgroup and an involution orbit

Let K be a central elementary abelian two-subgroup of a group V. If the
cosets outside K are covered by automorphism translates of a specified
involution, then V itself is elementary abelian. The orbit coverage is
an explicit hypothesis; centrality and index four alone do not imply it.
No finiteness or nontriviality assumption is required.

Every element of K has square one. Every other element is a product of
an automorphic image of the involution and a commuting element of K, so
also has square one. A group of exponent dividing two is abelian, which
gives the elementary abelian structure.

This is the elementary-group argument in the critical-distance-two part
of Stellmacher (8.2), Journal of Algebra 190 (1997), p.38. The geometric
application must separately establish orbit coverage from the actual
stabilizer action; see refs/latex/stellmacher-n-group.tex and the journal scan.
-/

/-- A central elementary subgroup and a covering involution orbit force exponent two. -/
public theorem isElementaryAbelian_of_central_involution_orbit
    {GroupType : Type*} [Group GroupType]
    (centralSubgroup : Subgroup GroupType)
    (hcentral : centralSubgroup ≤ Subgroup.center GroupType)
    (helementary : IsElementaryAbelian 2 centralSubgroup)
    (involution : GroupType) (hinvolution : involution ^ 2 = 1)
    (horbit : ∀ element : GroupType, element ∉ centralSubgroup →
      ∃ automorphism : MulAut GroupType, ∃ centralElement : centralSubgroup,
        element = automorphism involution * centralElement) :
    IsElementaryAbelian 2 GroupType := by
  let : IsElementaryAbelian 2 centralSubgroup := helementary
  have hsquare : ∀ element : GroupType, element ^ 2 = 1 := by
    intro element
    by_cases hmem : element ∈ centralSubgroup
    · exact elemPow_eq_one_of_isElementaryAbelian element hmem
    · obtain ⟨automorphism, centralElement, rfl⟩ := horbit element hmem
      have hcomm : Commute (automorphism involution) (centralElement : GroupType) :=
        Subgroup.mem_center_iff.mp (hcentral centralElement.property) _
      rw [hcomm.mul_pow, ← map_pow, hinvolution, map_one,
        elemPow_eq_one_of_isElementaryAbelian _ centralElement.property, mul_one]
  exact {
    is_comm := ⟨fun first second =>
      (Commute.of_orderOf_dvd_two
        (fun element => orderOf_dvd_of_pow_eq_one (hsquare element)) first second).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsquare
  }

