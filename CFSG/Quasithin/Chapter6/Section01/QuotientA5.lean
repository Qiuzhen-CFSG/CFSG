module

public import CFSG.Quasithin.Chapter6.Section01.SourceBasic
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# The marked A₅ quotient at the terminal exponent

The parameter-one branch of the source reduction reaches `n = 2` before its
M₂₂ analysis.  At that point the quotient model carried by the *actual*
`Hypothesis611` is a PSL₂ model over a field of order four.  The checked
projective-line comparison identifies that same quotient with the literal
alternating group on five letters.  This bridge preserves the displayed
quotient `L ⧸ pCore 2 L`; it does not identify the ambient group or its module.

Source: Aschbacher–Smith, §6.2, printed pp.686–691, together with the
exceptional isomorphism PSL₂(4) ≅ A₅.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611

open Subgroup

universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G}
  {L M V : Subgroup G} {n : ℕ}

/-- The actual source quotient becomes the marked A₅ quotient once the
preceding reduction has established the terminal exponent `n = 2`. -/
public theorem quotient_a5_of_n_eq_two
    (h : Hypothesis611 K T L M V n) (hn : n = 2) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) := by
  subst n
  have hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4 := by
    simpa using h.quotient_model
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  exact ⟨e.trans
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hcard).some⟩

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
end
