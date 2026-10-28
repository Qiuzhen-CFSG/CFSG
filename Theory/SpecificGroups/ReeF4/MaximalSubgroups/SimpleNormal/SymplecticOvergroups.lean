module

public import Theory.GroupTheory.CoatomNormalizerIndex
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SymplecticOvergroups.Inputs

/-!
# Reduction of the symplectic Ree overgroup calculation

Relative normality places `M` in the normalizer of the actual ambient image
of `S`. An element outside the normalizer makes it proper, hence equal to
`M` by maximality. A normalizing element outside `S` makes the quotient
nontrivial. The independent upper bound of two then determines its cardinal.

This is conditional assembly. The two concrete normalizer obligations remain
unproved here, so this module does not export
`symplecticOvergroups : SymplecticOvergroups`.

Source: G. Malle, J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E, Sections 2.2 and 2.11. Section 2.2
constructs the generic symplectic subgroup and its graph extension; Section
2.11 places an arbitrary subgroup of the given symplectic type. Malle writes
the ambient field size as `q²`; it is `2^(2*m+1)` here. The resulting
`Sp₄(q):2` entry is also case 9 in the proof of Theorem 5 of
Himstedt–Nguyen–Tiep, arXiv:0910.4758, p.3.
-/

public section

namespace ReeF4.MaximalSubgroups.SimpleNormal

open Subgroup

/-- The normalizer bound and concrete inside/outside witnesses suffice for
the original quotient calculation, with the supplied subgroup unchanged. -/
theorem symplecticOvergroups_of_normalizer_bound_and_witnesses
    (hbound : SymplecticNormalizerBound)
    (hwitness : SymplecticNormalizerWitnesses) : SymplecticOvergroups := by
  intro m hm M hM hsolv hR S hSn hSs hSa hC F _ _ hcard e
  let := hSn
  obtain ⟨t, u, ht, htS, hu⟩ :=
    hwitness m hm M hM hsolv hR S hSn hSs hSa hC F hcard e
  have hproper : normalizer (S.map M.subtype : Set (Model m)) ≠ ⊤ := by
    intro htop
    exact hu (htop ▸ mem_top u)
  exact quotient_card_eq_two_of_normalizer_bound M hM S
    (hbound m hm M hM hsolv hR S hSn hSs hSa hC F hcard e hproper) t ht htS hproper

end ReeF4.MaximalSubgroups.SimpleNormal
