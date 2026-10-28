module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.SourceSurvivors

/-!
# Complete terminal cases from the corrected source alternatives

The actual classification intersection and original marked exclusions give
all fields of the existing non-S₃ conclusion, including the four unchanged
quotients, residual embedding, module commutator and strict core inequality.
The S₃ argument retains its original centralizer and singular-span inputs.
Source: Aschbacher–Smith, final proof of 15.3.1, printed p.1155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
namespace Intersection.SourceInput
variable {H : Type u} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

theorem source_nonS3_cases_of_source_alternatives
    (hF : FSource.SourceAlternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.SourceAlternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow)
    (hB : SourceFFAlternative d.offenderAction)
    (hnot : ¬ Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3))) :
    Cases.NonS3Conclusion d := by
  rcases d.source_intersection_of_source_alternatives hF hB with h | ⟨hX,_,hres⟩
  · exact (hnot h).elim
  · obtain ⟨hY,hV⟩ := d.source_moduleClosure_commutator_of_source_alternatives hF hB hnot
    exact ⟨hX, d.source_surviving_quotient_of_source_alternatives hF hB hnot,
      hres, hY, hV, d.local_core_strict, d.vector_fixed, (d.toActionInput hres).vector_finrank⟩

theorem source_terminal_cases_of_source_alternatives
    (E Z : Subgroup H) (hZE : Z ≤ E)
    (hXE : d.XE ≤ centralizer (E : Set H))
    (hZT : Z ≤ centralizer (d.T : Set H))
    (hFspan : d.F = conjugateSpanBy Z d.YF)
    (hF : FSource.SourceAlternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.SourceAlternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow)
    (hB : SourceFFAlternative d.offenderAction) :
    Cases.SymmetricThreeConclusion d Z ∨ Cases.NonS3Conclusion d := by
  by_cases hs : Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3))
  · obtain ⟨hres,hZ,hspan⟩ := symmetricThree_branch d.T d.XE E Z d.YF
      d.second_commutator d.second_escape d.second_perfect
      ((d.second_local.symm ▸ le_sup_right).trans d.second_normalized)
      hZE hXE hZT hs.some
    exact Or.inl ⟨hs,hres,hZ,hspan,hFspan.symm ▸ hspan⟩
  · exact Or.inr (d.source_nonS3_cases_of_source_alternatives hF hB hs)

theorem source_nonS3_cases_of_source_classifications {K : GroupClass.{u}}
    (hH : IsSQTK K H)
    (classificationF : FSource.SourceClassificationInput K)
    (classificationB : SourceFFClassificationInput.{u,u} K)
    (hnot : ¬ Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3))) :
    Cases.NonS3Conclusion d :=
  d.source_nonS3_cases_of_source_alternatives
    (d.source_goldschmidt_alternative hH classificationF)
    (d.full_sourceFF_alternative hH classificationB) hnot

theorem source_terminal_cases_of_source_classifications {K : GroupClass.{u}}
    (hH : IsSQTK K H)
    (classificationF : FSource.SourceClassificationInput K)
    (classificationB : SourceFFClassificationInput.{u,u} K)
    (E Z : Subgroup H) (hZE : Z ≤ E)
    (hXE : d.XE ≤ centralizer (E : Set H))
    (hZT : Z ≤ centralizer (d.T : Set H))
    (hFspan : d.F = conjugateSpanBy Z d.YF) :
    Cases.SymmetricThreeConclusion d Z ∨ Cases.NonS3Conclusion d :=
  d.source_terminal_cases_of_source_alternatives E Z hZE hXE hZT hFspan
    (d.source_goldschmidt_alternative hH classificationF)
    (d.full_sourceFF_alternative hH classificationB)

end Intersection.SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
