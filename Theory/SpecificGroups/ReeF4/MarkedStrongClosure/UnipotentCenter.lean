module

public import Theory.SpecificGroups.ReeF4.MarkedStrongClosure
public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.UnipotentCenter

/-!
# The marked returning pair for every large Ree parameter

The proved standard-unipotent center theorem identifies the original central
involution with a nonzero y₅(t), exactly in the convention used by the marked
pair. It discharges the sole premise of the existing Sylow transport argument.
Both noncommuting conjugates lie in the original Sylow and belong to the class
of its original marked involution. The field parameter satisfies m ≥ 1; the
derived binary/Tits group remains a separate family.

Source: Aschbacher--Smith 16.1.6 and 16.5.13, pp.1172,1201--1202, for the
standard center; 1.1.5(3)(a) and Proposition 2.2.2, pp.501--503,519--520,
for the Bender inspection. Root conventions: GLS3 Table 2.4 and 2.4.5(d).
-/

public section
namespace ReeF4.MarkedStrongClosure

/-- The standard-U producer has exactly the marker contract used by the
returning-pair argument, with the same actual group, subgroup and root curve. -/
theorem standardCentralInvolutions (m : ℕ) (hm : 1 ≤ m) :
    StandardCentralInvolutions m :=
  EvenInvolutionGeometry.central_involution_eq_longRootElement m hm

/-- Every large Ree Sylow contains noncommuting conjugates of its actual
central involution, with no extra model-local premise. -/
theorem sylow_noncommuting_conjugates (m : ℕ) (hm : 1 ≤ m)
    (R : Sylow 2 (Model m)) (v : Model m)
    (hvR : v ∈ R) (hv : orderOf v = 2) (hc : ∀ x ∈ R, Commute v x) :
    ∃ a b : R, IsConj v (a : Model m) ∧ IsConj v (b : Model m) ∧ ¬Commute a b :=
  sylow_noncommuting_conjugates_of_central_involutions
    m (standardCentralInvolutions m hm) R v hvR hv hc

end ReeF4.MarkedStrongClosure
