module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Survivors
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.FullSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DihedralEight.SmallFieldLocals
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The four terminal quotients from the actual F source alternatives

The offender action restricts the added dihedral PSL₂ branch to PSL₂(7) or
PSL₂(9). Only after that restriction do the genuine original vertices become
S₄, by the small-field local theorem. The existing strict-core obstruction
therefore excludes this branch on the original first vertex. The added
square-field branch gives S₆ through its actual Frobenius action. Together
with the original marked rows, this recovers the same four terminal quotients.
Source: Aschbacher–Smith F.6.18 and the final proof of 15.3.1, printed p.1155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
namespace Intersection.SourceInput
variable {H : Type u} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- The full action supplies the small ambient model before proving the
original S₄ marking. No arbitrary PSL₂ local-pair assertion is used. -/
theorem source_dihedral_psl_excluded
    (r : FSource.DihedralPSL2Row d.quotientSylow)
    (hB : SourceFFAlternative d.offenderAction) : False := by
  obtain ⟨c⟩ := d.source_offender_quasisimple_of_classifications r.quasisimple hB
  obtain ⟨_,_,hres⟩ := d.source_dihedral_psl_intersection r hB
  have ht := goldschmidt_twoCore_quotient d.G1 d.G2 d.goldschmidt
  have hc : pCore 2 (coreQuotient H) = ⊥ := pCore_quotient_pCore_eq_bot 2
  have h8 : Nat.card (d.G1.map coreProjection ⊓ d.G2.map coreProjection :
      Subgroup (coreQuotient H)) = 8 := by
    rw [d.quotient_intersection, Nat.card_congr r.sylow.some.toEquiv, DihedralGroup.nat_card]
  rcases d.source_component_dihedral_pslTwo_models r.quasisimple c
    r.field r.degree r.congruence r.model r.component r.sylow with ha | he
  · apply MarkedElimination.source_symmetricFour_quotient_excluded (d.toActionInput hres)
    exact (ChapterF.SourceAssembly.alternatingSix_symmetricFour_vertices ht hc h8 ha.some).1.some
  · apply MarkedElimination.source_symmetricFour_quotient_excluded (d.toActionInput hres)
    exact (ChapterF.SourceAssembly.binaryThree_symmetricFour_vertices ht hc h8 he.some).1.some

/-- Both corrected rank-one source branches preserve the exact four
terminal quotient models, with the original local labels retained. -/
theorem source_surviving_quotient_of_source_alternatives
    (hF : FSource.SourceAlternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.SourceAlternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow)
    (hB : SourceFFAlternative d.offenderAction)
    (hnot : ¬ Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3))) :
    Cases.SurvivingQuotientAlternative (coreQuotient H) := by
  rcases hF with hF | hF <;> rcases hF with ha | hr
  · rcases ha with ha | hr
    · exact d.source_surviving_quotient_of_classifications (Or.inl ha) hB hnot
    · exact (d.source_dihedral_psl_excluded hr.some hB).elim
  · exact .symmetricSix (d.source_square_field_symmetricSix hr.some hB).some
  · rcases ha with ha | hr
    · exact d.source_surviving_quotient_of_classifications (Or.inr ha) hB hnot
    · exact (d.source_dihedral_psl_excluded hr.some hB).elim
  · exact .symmetricSix (d.source_square_field_symmetricSix hr.some hB).some

include d in
/-- Universal source application on the original terminal quotient. -/
theorem source_surviving_quotient_of_full_source_classifications {K : GroupClass.{u}}
    (hH : IsSQTK K H)
    (classificationF : FSource.SourceClassificationInput K)
    (classificationB : SourceFFClassificationInput.{u,u} K)
    (hnot : ¬ Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3))) :
    Cases.SurvivingQuotientAlternative (coreQuotient H) :=
  d.source_surviving_quotient_of_source_alternatives
    (d.source_goldschmidt_alternative hH classificationF)
    (classificationB _ _ _ (d.offender_hypothesis hH)) hnot

end Intersection.SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
