module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SubfieldOvergroups.PrimeDegree
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SubfieldOvergroups.NormalizerReduction

/-!
# Assembly of the Ree subfield overgroup calculation

Relative normality puts the maximal subgroup in the normalizer of its socle.
After conjugating that socle to the standard derived subfield group, the
concrete normalizer bound places the whole maximal subgroup in the full
subfield fixed group. Properness and maximality give equality. Field descent
identifies that whole group with `Model k`, including `k = 0`; strict subfield
inclusions rule out a composite extension degree.

The four geometric inputs remain explicit. This conditional assembly does
not assert `subfieldOvergroups : SubfieldOvergroups` until all of them have
been proved. In particular neither recognition nor ambient simplicity is
assumed as a substitute for the placement and normalizer calculations.

Source: Malle, J. Algebra 139 (1991), 52–69; arXiv:0910.4758,
proof of Theorem 5, case 10 of its unconditional maximal-subgroup list.
-/

public section

namespace ReeF4.MaximalSubgroups.SimpleNormal

open Subgroup ReeF4.Subfield

/-- Conditional assembly of the source subfield case. All four extra inputs
are concrete geometric obligations and remain to be discharged here. -/
theorem subfieldOvergroups_of_geometry
    (hdesc : SubfieldDescent) (hstrict : StrictSubfieldInclusions)
    (hplace : DerivedSubfieldPlacement) (hCsplit : BinaryDerivedSplitCentralizer) :
    SubfieldOvergroups := by
  have hnorm := derivedSubfieldNormalizer_of_binarySplitCentralizer hCsplit
  intro m hm M hM hsolv hR S hSn hSs hSa hC k hlt hdiv e
  let := hSn
  obtain ⟨g, hg⟩ := hplace m hm M hM hsolv hR S hSn hSs hSa hC k hlt hdiv e
  have hMN : M ≤ normalizer (S.map M.subtype : Set (Model m)) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      S.le_normalizer_map M.subtype
  have hconj : M.map (MulAut.conj g).toMonoidHom ≤ fixedSubfield m k := by
    have h := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hMN
    rw [map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective, hg] at h
    exact h.trans (hnorm m hm k hlt hdiv)
  have hproper : fixedSubfield m k ≠ ⊤ := by
    have h := hstrict m k m hlt le_rfl hdiv dvd_rfl
    rw [fixedSubfield_self] at h
    exact h.ne
  have hMc : IsCoatom (M.map (MulAut.conj g).toMonoidHom) :=
    (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup M).mpr hM
  have heq : M.map (MulAut.conj g).toMonoidHom = fixedSubfield m k :=
    ((hMc.le_iff_eq hproper).mp hconj).symm
  have hmax : IsCoatom (fixedSubfield m k) := heq ▸ hMc
  obtain ⟨a, ha, hfield⟩ := prime_degree_of_isCoatom_fixedSubfield hstrict hlt hdiv hmax
  obtain ⟨f⟩ := nonempty_fixedSubfield_equiv_of_descent hdesc hdiv
  exact ⟨a, ha, hfield, ⟨((MulAut.conj g).subgroupMap M).trans
    ((MulEquiv.subgroupCongr heq).trans f)⟩⟩

end ReeF4.MaximalSubgroups.SimpleNormal
