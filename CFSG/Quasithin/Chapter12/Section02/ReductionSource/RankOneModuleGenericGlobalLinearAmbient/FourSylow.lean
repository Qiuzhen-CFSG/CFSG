module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.FourSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLinearAmbient.CoreContainment

/-!
# The exceptional linear Sylow in the original Chapter12 row

The unchanged chosen-module Input constructs the actual exceptional Sylow
UT₃(F₄)⋊C₂ when the original degree is two and S is proper in T. A single
isomorphism marks S, both original root planes, their common center and a
central involution. It uses the original whole-Borel comparison in either
orientation and introduces no model-realization premise.

The exceptional ambient centralizer argument, full-normalizer realization,
completion recognition and GlobalExit remain separate source obligations.
Source: Aschbacher--Smith §5.3.7, printed pp.660--661, used in §12.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (d : Global.Preparation T L H A B (residual H))
  (hp : Group.IsPerfect (residual H))
  (F : Type) [Field F] [Finite F] [CharP F 2]
  {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
  (he : Nonempty (RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
    (LinearThree.amalgam F)) ∨
    Nonempty (RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
    (LinearThree.amalgam F).reverse))
  (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include D h hmany hn hpsl hH d hp hm hF he hmax

/-- The original degree-two row constructs all marks on the same Sylow group. -/
theorem rankOne_global_linear_four_marked_sylow
    (hn2 : n=2) (hne : Global.sourceS L H ≠ (T : Subgroup G)) :
    ∃ c : Chapter5.Section03ExceptionalSylowModel.MarkedCopy G,
      c.carrier=(T : Subgroup G) ∧ c.S=Global.sourceS L H ∧
      ((c.V₁=L.pCoreIn 2 ∧ c.V₂=(residual H).pCoreIn 2) ∨
       (c.V₁=(residual H).pCoreIn 2 ∧ c.V₂=L.pCoreIn 2)) ∧
      c.Z=centerIn (Global.sourceS L H) ∧ orderOf c.z=2 ∧
      (T : Subgroup G) ≤ centralizer ({c.z} : Set G) :=
  d.linear_four_marked_sylow (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax hn2 hne

/-- The original degree-two row has the full Sylow alternative with no
extra marking or splitting premise. -/
theorem rankOne_global_linear_four_sylow_alternative (hn2 : n=2) :
    Global.sourceS L H=(T : Subgroup G) ∨
    ∃ c : Chapter5.Section03ExceptionalSylowModel.MarkedCopy G,
      c.carrier=(T : Subgroup G) ∧ c.S=Global.sourceS L H ∧
      ((c.V₁=L.pCoreIn 2 ∧ c.V₂=(residual H).pCoreIn 2) ∨
       (c.V₁=(residual H).pCoreIn 2 ∧ c.V₂=L.pCoreIn 2)) ∧
      c.Z=centerIn (Global.sourceS L H) ∧ orderOf c.z=2 ∧
      (T : Subgroup G) ≤ centralizer ({c.z} : Set G) :=
  d.linear_four_sylow_alternative (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax hn2

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
