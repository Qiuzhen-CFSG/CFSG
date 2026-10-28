module

public import CFSG.KnownSimple.UnitaryRankOne
public import Theory.SpecificGroups.PSL2.InvolutoryTwoComponents

/-!
# Linear and unitary contributions to the known-simple B₂ condition

This module supplies every even-field rank-one linear and unitary case.
Transport acts on the actual automorphisms, fixed subgroups and two-components.
The unitary branch uses the proved PSU₂(q)–PSL₂(q) comparison over the fixed
field, retaining coefficient-field order q² and conjugation x ↦ x^q.

The odd-field linear and higher-dimensional linear and unitary branches are
still needed for the full linear/unitary catalogue theorem. The uniform rank-one
comparison also reduces odd-field PSU₂ to the corresponding PSL₂ case.

Source: GLS II, Definition 2.4 (`refs/KGroup/GLS2/ChapterA.tex`), and GLS III,
§§2.7 and 4.9. These are contributions to the known-simple input in I.3.
-/

public section

open Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section03.KnownSimpleB2
variable {S : Type*} [Group S] {q : ℕ}

/-- The even-field PSL₂ branch, for every involutory automorphism. -/
theorem of_psl_two_even (hq : Even q) (hS : ClassicalGroup.IsPSL S 2 q) :
    HasInvolutoryB2 S := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hS
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := ringChar.of_eq (FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hc]
    exact Nat.mod_eq_zero_of_dvd (even_iff_two_dvd.mp hq)))
  exact (Theory.PSL2.charTwo_hasInvolutoryB2 (F := F)).of_mulEquiv e

/-- The even-field PSU₂ alias retains the coefficient field of order q². -/
theorem of_psu_two_even (hp : KnownSimple.UnitaryParameters 2 q)
    (hq : Even q) (hS : ClassicalGroup.IsPSU S 2 q) : HasInvolutoryB2 S :=
  of_psl_two_even hq (hS.isPSL_two hp.1)

end CFSG.Quasithin.ChapterI.Section03.KnownSimpleB2
