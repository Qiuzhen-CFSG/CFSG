module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.OuterSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.LargeGoldschmidt.MarkedOuterMathieu
/-!
# The actual marked outer Mathieu source row of F.6.18

The original SQTK quotient, ambient Sylow and exact marked amalgam identify
the quasisimple residual central quotient via the full earlier Theorem C
catalogue. The center-removal and ambient-extension arguments then give
the actual full automorphism group, with all local assertions on the source's
original vertices and common Sylow subgroup. No ambient model conclusion
is assumed.

Source: Aschbacher–Smith, F.6.18(13), printed p.310. The marked source case
is supplied separately by the F.6.5 amalgam enumeration.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu
universe u
variable {D H : Type u} [Group D] [Finite D] [Group H] [Finite H]
    {κ : GroupClass.{u}} {D₁ D₂ : Subgroup D}

/-- All literal conclusions of row (13) under its genuine source hypotheses. -/
theorem source_thirteen_of_marked_aut_mathieu
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ ((pResidual 2 D) ⧸ center (pResidual 2 D)))
    (hH : IsSQTK κ H)
    (e : D ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple D₁ D₂)
    (hFstar : pResidual 2 D = generalizedFitting D)
    (hq : IsQuasisimple (pResidual 2 D))
    (hM : GreenBook.AutMathieuTwelve.IsAutM12Amalgam
      (RankTwoAmalgam.ofSubgroups D₁ (D₁ ⊓ D₂) D₂ inf_le_left inf_le_right)) :
    ∃ S : Sylow 2 D, D₁ ⊓ D₂ = (S : Subgroup D) ∧
      Nonempty (D ≃* MulAut M12) ∧ Nonempty (generalizedFitting D ≃* M12) ∧
      IsQuasisimple (generalizedFitting D) ∧
      (∃ N : Subgroup S, ∃ _ : N.Normal,
        Nonempty (N ≃* InnerSquare.C4Square) ∧ Nonempty ((S ⧸ N) ≃* DihedralGroup 4)) ∧
      (∃ N : Subgroup D₁, ∃ _ : N.Normal,
        Nonempty (QuaternionCentralProductData N) ∧
        Nonempty ((D₁ ⧸ N) ≃* DihedralGroup 6)) ∧
      (∃ N : Subgroup D₂, ∃ _ : N.Normal,
        Nonempty (N ≃* InnerSquare.C4Square) ∧
        ∃ K : Subgroup (D₂ ⧸ N), ∃ _ : K.Normal,
          Nonempty (K ≃* OuterSquare.C3 × InnerSquare.E4) ∧
            Nonempty (((D₂ ⧸ N) ⧸ K) ≃* OuterSquare.C2)) := by
  obtain ⟨j⟩ := residual_quotient_mathieu_of_marked_aut_mathieu hA hC hH e h hM hq
  exact source_thirteen_of_mathieu_quotient e h hFstar hq hM j
end CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu
