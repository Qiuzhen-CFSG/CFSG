module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoFour

/-!
# The J₄ outer inspection from actual full innerness

The literal matrix model now has inner automorphism group equal to its full
automorphism group. Transport its outer two-group conclusion along the actual
carrier equivalence used by Chapter 1. The stronger companion is available for
Chapter 16, where it must be combined with the genuine centralizer rows and
marked involution fusion.

Source: Aschbacher--Smith, Theorem C, printed p.33 and the inspection on p.510;
GLS3 Table 5.3i. The inherited simple/perfect interfaces remain available.
-/
public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
open Theory.GroupTheory

/-- The adequate two-group endpoint on the exact source carrier. -/
theorem jankoFour_outer_isPGroup_two
    [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model] :
    IsPGroup 2 (MulAut.Outer Janko4.Model) :=
  Janko4.AdequateLocal.outer_isPGroup_two

/-- Full innerness companion for the intrinsic Chapter 16 source assembly. -/
theorem jankoFour_conj_surjective
    [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model] :
    Function.Surjective (MulAut.conj : Janko4.Model →* MulAut Janko4.Model) :=
  Janko4.AdequateLocal.conj_surjective

end CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
