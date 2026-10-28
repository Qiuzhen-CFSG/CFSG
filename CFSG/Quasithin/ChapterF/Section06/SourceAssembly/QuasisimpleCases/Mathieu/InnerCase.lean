module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.InnerSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.LargeGoldschmidt.MarkedMathieu

/-!
# The actual marked Mathieu source row of F.6.18

The genuine Theorem A/C and SQTK quotient hypotheses, together with the
original ambient Sylow amalgam and quasisimple residual, identify the
component central quotient as M₁₂. The center and ambient arguments then
produce M₁₂ itself, and transport all three local extension clauses along
the exact marked amalgam. No ambient model or classification conclusion
is an extra premise.

The source's marked-amalgam case is supplied separately by the F.6.5
amalgam enumeration. Source: Aschbacher–Smith, F.6.18(12), printed p.310.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu
open InnerSquare
universe u
variable {D H : Type u} [Group D] [Finite D] [Group H] [Finite H]
    {κ : GroupClass.{u}} {D₁ D₂ : Subgroup D}

/-- All literal conclusions of row (12) from its genuine earlier source hypotheses. -/
theorem source_twelve_of_marked_mathieu
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ ((pResidual 2 D) ⧸ center (pResidual 2 D)))
    (hH : IsSQTK κ H)
    (e : D ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple D₁ D₂)
    (hFstar : pResidual 2 D = generalizedFitting D)
    (hq : IsQuasisimple (pResidual 2 D))
    (hM : GreenBook.MathieuTwelve.IsM12Amalgam
      (RankTwoAmalgam.ofSubgroups D₁ (D₁ ⊓ D₂) D₂ inf_le_left inf_le_right)) :
    ∃ S : Sylow 2 D, D₁ ⊓ D₂ = (S : Subgroup D) ∧ Nonempty (D ≃* M12) ∧
      IsQuasisimple (generalizedFitting D) ∧
      (∃ N : Subgroup S, ∃ _ : N.Normal,
        Nonempty (N ≃* C4Square) ∧ Nonempty ((S ⧸ N) ≃* E4)) ∧
      (∃ N : Subgroup D₁, ∃ _ : N.Normal,
        Nonempty (QuaternionCentralProductData N) ∧
        Nonempty ((D₁ ⧸ N) ≃* Equiv.Perm (Fin 3))) ∧
      (∃ N : Subgroup D₂, ∃ _ : N.Normal,
        Nonempty (N ≃* C4Square) ∧ Nonempty ((D₂ ⧸ N) ≃* DihedralGroup 6)) := by
  obtain ⟨j⟩ := residual_quotient_mathieu_of_marked_mathieu hA hC hH e h hM hq
  exact source_twelve_of_mathieu_quotient e h hFstar hq hM j

end CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu
