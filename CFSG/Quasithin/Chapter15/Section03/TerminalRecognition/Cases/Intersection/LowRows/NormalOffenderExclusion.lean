module

public import Theory.GroupTheory.NormalSymmetricThreeExtraspecial
public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.LowRows.Reduction

/-!
# The normal offender obstruction in the extraspecial terminal row

The source offender subgroup is normal by its actual representation
construction. In the extraspecial F.6.18 row, its S3 and S3 × S3 alternatives
are impossible. The quotient equivalence to the source E4 supplies the
2-group hypothesis; neither an extension-action identification nor equality
between the offender group and the ambient quotient is needed.

The full B.5.6 comparison still must reduce its other alternatives to these
cases. Source: Aschbacher–Smith, final proof of15.3.1, printed p.1155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

omit [Finite H] in
private theorem quotient_isTwoGroup_of_E4 (N : Subgroup (coreQuotient H)) [N.Normal]
    (q : Nonempty ((coreQuotient H ⧸ N) ≃* FSource.E4)) :
    IsPGroup 2 (coreQuotient H ⧸ N) := by
  obtain ⟨e⟩ := q
  have hE : IsPGroup 2 FSource.E4 := IsPGroup.of_card (n := 2) (by
    simp [FSource.E4, FSource.C])
  exact hE.of_equiv e.symm

/-- Apply the S3 obstruction to the actual normal offender group. -/
theorem no_symmetricThree_offender_of_extraspecial_row
    (N : Subgroup (coreQuotient H)) [N.Normal] [IsExtraspecial 3 N]
    (q : Nonempty ((coreQuotient H ⧸ N) ≃* FSource.E4))
    (e : d.offenderGroup ≃* Equiv.Perm (Fin 3)) : False := by
  let : d.offenderGroup.Normal := Representation.BinaryOffender.offenderSubgroup_normal _
  exact NormalSymmetricThreeExtraspecial.no_normal_symmetricThree N d.offenderGroup
    (quotient_isTwoGroup_of_E4 N q) e

/-- Apply the two-axis obstruction without assuming an extension action. -/
theorem no_symmetricThreePair_offender_of_extraspecial_row
    (N : Subgroup (coreQuotient H)) [N.Normal] [IsExtraspecial 3 N]
    (q : Nonempty ((coreQuotient H ⧸ N) ≃* FSource.E4))
    (e : d.offenderGroup ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) : False := by
  let : d.offenderGroup.Normal := Representation.BinaryOffender.offenderSubgroup_normal _
  exact NormalSymmetricThreeExtraspecial.no_normal_symmetricThreePair N d.offenderGroup
    (IsExtraspecial.isPGroup 3 N) (IsExtraspecial.center_order_p 3 N)
    (quotient_isTwoGroup_of_E4 N q) e

/-- The actual order-108 row also excludes the outer A6–C3 group shape. -/
theorem no_outerSixThreeShape_of_extraspecial_row
    (N : Subgroup (coreQuotient H)) [N.Normal] (hN : Nat.card N = 27)
    (q : Nonempty ((coreQuotient H ⧸ N) ≃* FSource.E4))
    (hshape : ChapterB.OuterSixThreeShape d.offenderGroup) : False := by
  obtain ⟨e⟩ := q
  have hD : Nat.card (coreQuotient H) = 108 := by
    rw [card_eq_card_quotient_mul_card_subgroup N, Nat.card_congr e.toEquiv, hN]
    norm_num [FSource.E4, FSource.C]
  have hi := Nat.card_le_card_of_injective d.offenderGroup.subtype d.offenderGroup.subtype_injective
  have hlo := hshape.card_ge
  omega

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
