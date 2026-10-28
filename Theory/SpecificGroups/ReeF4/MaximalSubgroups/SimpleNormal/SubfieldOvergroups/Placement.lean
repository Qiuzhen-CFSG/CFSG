module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SubfieldOvergroups.Placement.Basic

/-!
# Conditional placement of a Ree-derived socle

Split F4 conjugacy compares the supplied embedding with a coefficient image
of the smaller Ree derived group. Field descent identifies the target with the
intrinsic standard derived subfield. The split centralizer calculation then
forces the conjugator to be a Ree element.

The representation geometry and binary centralizer inputs remain explicit.
This module does not yet prove `derivedSubfieldPlacement_of_descent`.

Source: Malle, J. Algebra 139 (1991), 52–69, subfield case;
arXiv:0910.4758, proof of Theorem 5, case 10.
-/

public section

namespace ReeF4.MaximalSubgroups.SimpleNormal

open ReeF4.Subfield

/-- Reduce the placement contract to conjugacy in split F4 and the independent
binary centralizer calculation. Every additional premise remains explicit. -/
theorem derivedSubfieldPlacement_of_splitConjugacy (hdesc : SubfieldDescent)
    (hsplit : Placement.SplitConjugacy) (hC : BinaryDerivedSplitCentralizer) :
    DerivedSubfieldPlacement := by
  intro m hm M hM hsolv hR S hSn hSs hSa hCS k hlt hdiv e
  obtain ⟨f, a, ha⟩ := hsplit m hm M hM hsolv hR S hSn hSs hSa hCS k hlt hdiv e
  rw [Placement.map_commutator_splitMap_of_descent hdesc hdiv f] at ha
  exact Placement.exists_ree_conjugator_of_split (S.map M.subtype) (derivedSubfield m k)
    (Placement.derived_splitCentralizer_eq_bot hC hm k) a ha

end ReeF4.MaximalSubgroups.SimpleNormal
