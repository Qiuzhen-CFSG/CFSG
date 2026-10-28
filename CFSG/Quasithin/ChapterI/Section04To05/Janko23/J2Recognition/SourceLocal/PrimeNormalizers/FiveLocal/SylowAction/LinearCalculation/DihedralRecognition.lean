module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction.Reduction
public import Theory.ElementaryAbelian.FivePlaneTwelveActor

/-!
# Dihedral recognition of the actual five-plane actor

The elementary four-group of the source frame identifies an order-twelve
actor with D₁₂ by a multiplicative equivalence. This supplies the recognition
premise of `FourLineFrame.twoOrbitConclusion_of_plane_geometry_and_recognition`;
the order itself is derived there from the congruence and the line-stabilizer
bound.

The source is the final paragraph of Aschbacher, *Sporadic Groups* (1994),
47.2, printed p.261 (PDF page 136). Only the frame's actual four-group and
its elementary-abelian and cardinality fields enter the recognition.
-/

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction

variable {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 5 E]
variable {H : Subgroup (MulAut E)}

/-- The frame's elementary four-group recognizes the supplied order-twelve actor. -/
public theorem FourLineFrame.dihedral_of_card_twelve (F : FourLineFrame H)
    (hE : Nat.card E = 25) (hH : Nat.card H = 12) :
    Nonempty (H ≃* DihedralGroup 6) := by
  let : IsElementaryAbelian 2 F.four := F.four_elementary
  exact IsElementaryAbelian.nonempty_mulEquiv_dihedral_six_of_card_twelve
    hE H hH F.four F.four_card

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction
