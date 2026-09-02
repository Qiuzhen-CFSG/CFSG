module
import Stellmacher.SectionThree.LemmaThreeSix
open scoped BigOperators Pointwise
open Stellmacher
namespace Stellmacher.SectionThree
universe u
variable {G : Type u} [Group G] [Finite G]
variable (S L : Subgroup G)
noncomputable example : Prop :=
  ⁅fittingSubgroup (L ⧸ pCore 2 L),
      (S.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L))⁆ =
    ⨆ P : {P : Subgroup G // P ∈ PStarSet L S},
      twoResidualImageInQuotient L (P : Subgroup G)
end Stellmacher.SectionThree
