module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Obstructions
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Symplectic.SevenElements
public import Theory.SpecificGroups.SymplecticFour.SevenNormalizer
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# The even symplectic rank-two branch of the seven-component inspection

Neither A₇ nor its central three-cover embeds in Sp₄ over a field of
characteristic two. Both contain a nonidentity seven-element conjugate to its
square. In symplectic dimension four, the eigenvalues are closed under inversion;
squaring conjugacy would therefore force six distinct eigenvalues.

The supplied finite-field isomorphism is composed with the actual equivalence
PSp₄(F) ≃ Sp₄(F) in characteristic two. Applying the obstruction to the literal
subgroup inclusion excludes every seven subgroup. In particular it excludes an
ordinary component of the common fixed subgroup of any actual two-subgroup of
automorphisms. No upward transfer of component membership, restriction to a
single involution, or additional automorphism-classification premise is needed.
The finite, simple, strongly quasithin source case follows from this stronger
embedding obstruction.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, E.6.18, printed p.252 (PDF p.263); Theorem C and
Remark A.2.4, printed p.33. The separate Sp₄(2)′ endpoint belongs to
`BinaryLie.RankAndOrder`.
-/

public section

open Subgroup Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie
variable {S : Type*} [Group S] [Finite S]

/-- The genuine finite-field model has no subgroup of either exceptional
seven type; this retains the actual subgroup embedding. -/
theorem symplectic_no_seven_subgroup {f : ℕ}
    (h : ClassicalGroup.IsPSp S 2 (2 ^ f)) (L : Subgroup S) : ¬ IsSeven L := by
  intro hL
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  let a : S ≃* Sp F := e.trans EvenProjective.equiv.symm
  let j : L →* Sp F := a.toMonoidHom.comp L.subtype
  have hj : Function.Injective j := a.injective.comp L.subtype_injective
  obtain ⟨x, y, hx7, hxne, hxy⟩ := Symplectic.seven_square_conjugate hL
  apply SevenNormalizer.seven_not_conjugate_square (j x) (j y)
  · rw [← map_pow, hx7, map_one]
  · exact fun he => hxne (hj (he.trans j.map_one.symm))
  · simpa only [map_mul, map_inv, map_pow] using congrArg j hxy

/-- The full PSp₄(2^f) constructor of Theorem C, for arbitrary actual
 two-subgroups of the automorphism group and both seven-component models. -/
theorem symplectic {f : ℕ} (_hf : 2 ≤ f)
    (h : ClassicalGroup.IsPSp S 2 (2 ^ f)) : SevenActionInspection S := by
  intro P _ L _ _ hL
  exact (symplectic_no_seven_subgroup h L hL).elim

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie
