module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.LowRows.Reduction
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.LowRows.ExtraspecialFFComparison

/-!
# Removing the extraspecial row from the terminal comparison

The exhaustive low-row reduction either identifies the Thompson image with
S₃ or retains an extraspecial extension or a prime-field product. The actual
offender action's FF alternative excludes the extraspecial extension by
`no_extraspecial_row_of_adequateSourceAlternative`. Applying that exclusion
leaves the entire prime-field product witness, including its Sylow group,
local embeddings in either labeling, residual and outer actions.

The full source alternative implies the adequate alternative, so the original
conditional source contract is retained. The general FF classification and
the remaining prime-field product comparison belong to their source owners.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), final proof
of 15.3.1, printed p.1155; F.6.16–18, pp.308–310; B.5.6, p.105.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- The adequate FF alternative removes the extraspecial constructor from
the actual low-row reduction, preserving every clause of the product row. -/
theorem symmetricThree_or_product_low_row_of_adequateSourceAlternative
    (hF : FSource.Alternative (d.G1.map coreProjection) (d.G2.map coreProjection) d.quotientSylow ∨
      FSource.Alternative (d.G2.map coreProjection) (d.G1.map coreProjection) d.quotientSylow)
    (hn : ¬ IsQuasisimple (generalizedFitting (coreQuotient H)))
    (hB : AdequateSourceAlternative d.offenderAction) :
    Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3)) ∨
      ∃ _ : FSource.ProductRow d.quotientSylow,
        Nonempty (d.quotientSylow ≃* DihedralGroup 4) ∧
          ((Nonempty (d.G1.map coreProjection ≃* DihedralGroup 12) ∧
            Nonempty (d.G2.map coreProjection ≃* Equiv.Perm (Fin 4))) ∨
           (Nonempty (d.G2.map coreProjection ≃* DihedralGroup 12) ∧
            Nonempty (d.G1.map coreProjection ≃* Equiv.Perm (Fin 4)))) := by
  rcases d.symmetricThree_or_remaining_low_rows hF hn with he | h
  · exact Or.inl he
  · cases h with
    | extraspecial N hnormal hextraspecial hcard _ hquotient =>
      let : N.Normal := hnormal
      let : IsExtraspecial 3 N := hextraspecial
      exact (d.no_extraspecial_row_of_adequateSourceAlternative N hcard hquotient hB).elim
    | product data hs hl => exact Or.inr ⟨data, hs, hl⟩

/-- The original full FF input gives the same terminal low-row reduction. -/
theorem symmetricThree_or_product_low_row_of_sourceAlternative
    (hF : FSource.Alternative (d.G1.map coreProjection) (d.G2.map coreProjection) d.quotientSylow ∨
      FSource.Alternative (d.G2.map coreProjection) (d.G1.map coreProjection) d.quotientSylow)
    (hn : ¬ IsQuasisimple (generalizedFitting (coreQuotient H)))
    (hB : SourceAlternative d.offenderAction) :
    Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3)) ∨
      ∃ _ : FSource.ProductRow d.quotientSylow,
        Nonempty (d.quotientSylow ≃* DihedralGroup 4) ∧
          ((Nonempty (d.G1.map coreProjection ≃* DihedralGroup 12) ∧
            Nonempty (d.G2.map coreProjection ≃* Equiv.Perm (Fin 4))) ∨
           (Nonempty (d.G2.map coreProjection ≃* DihedralGroup 12) ∧
            Nonempty (d.G1.map coreProjection ≃* Equiv.Perm (Fin 4)))) :=
  d.symmetricThree_or_product_low_row_of_adequateSourceAlternative hF hn (hB.toAdequate _)

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
