module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveCharacters

/-!
# The local generalized characters in Brauer's degree formula

Each signed central-section column of the genuine local character table
is a linear combination of its ordinary irreducible characters. We retain
that function, and its inflation through a specified quotient, so that
induction and involution counting use exactly the same local column.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), p. 381,
the definition of R(d) and the central-section rows in the proof of Lemma 4.
-/

public section
noncomputable section
namespace Stellmacher.Recognition.LyonsU3Four
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    {α : FiveComplement →* MulAut S}

/-- The genuine ordinary generalized character defined by one signed section column. -/
@[expose] def LocalFiveCharacterTable.sectionClassFunction
    (T : LocalFiveCharacterTable S α) (w : QuarticCentralIndex S)
    (j : FiveLinearIndex) : ClassFunction (LocalFiveGroup S α) :=
  ∑ i : LocalFiveRowIndex S, (localFiveSectionRow S w i j : ℂ) •
    ofConjClassFunction (T.row i)

@[simp] theorem LocalFiveCharacterTable.sectionClassFunction_apply
    (T : LocalFiveCharacterTable S α) (w : QuarticCentralIndex S)
    (j : FiveLinearIndex) (a : LocalFiveGroup S α) :
    T.sectionClassFunction w j a = ∑ i : LocalFiveRowIndex S,
      (localFiveSectionRow S w i j : ℂ) * T.row i (ConjClasses.mk a) := by
  simp only [sectionClassFunction, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    ofConjClassFunction_apply]

/-- The same column on a group mapping onto the local model, in particular
on the actual centralizer with its actual odd core as kernel. -/
@[expose] def LocalFiveCharacterTable.inflatedSectionClassFunction
    (T : LocalFiveCharacterTable S α) (w : QuarticCentralIndex S)
    {H : Type*} [Group H] (N : Subgroup H) [N.Normal]
    (e : (H ⧸ N) ≃* LocalFiveGroup S α) (j : FiveLinearIndex) : ClassFunction H :=
  fun a => T.sectionClassFunction w j (e (QuotientGroup.mk' N a))

end Stellmacher.Recognition.LyonsU3Four
