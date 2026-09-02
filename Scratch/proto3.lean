module
import Stellmacher.SectionsOneToFourDefs
open scoped BigOperators Pointwise
open Stellmacher
namespace Stellmacher.SectionThree
universe u
variable {G : Type u} [Group G] [Finite G]
variable (P L S : Subgroup G)
#check twoResidualAmbient
#check twoPrimeResidualAmbient
#check Subgroup.subgroupOf
#check QuotientGroup.mk'
#check fittingSubgroup
example : Subgroup (L ⧸ pCore 2 L) := fittingSubgroup (L ⧸ pCore 2 L)
example : Subgroup (L ⧸ pCore 2 L) :=
  ((twoResidualAmbient P).subgroupOf L).map (QuotientGroup.mk' (pCore 2 L))
example : Subgroup (L ⧸ pCore 2 L) :=
  ((S.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L)))
example : Subgroup (L ⧸ pCore 2 L) :=
  (frattini (twoResidualSubgroup (⊤ : Subgroup (L ⧸ pCore 2 L)))).map
    (twoResidualSubgroup (⊤ : Subgroup (L ⧸ pCore 2 L))).subtype
example : Prop := IsIrreducibleSection S P (twoResidualAmbient L)
example : Prop := IsConjugateInvariantBy P S
example : Prop := ∀ A : Subgroup G, A.Normal → True
end Stellmacher.SectionThree
