module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.MarkedCentralizers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticExtensionOrder.FixedQuotient

/-!
# Chapter 12 marked symplectic centralizers

Both root centralizers and the nonroot square centralizer are identified
with the full centralizers in the same genuine extension. The pure and full
amalgam comparisons remain coherent, in both orientations and including n=2.
These applications retain the original Hypothesis 12.2.1, many-locals and
PSL2 quotient hypotheses, using W=wholeReduced T L. Fusion inside these
centralizers is still needed for the ambient order comparison.

Source: Aschbacher--Smith F.4.39,42--43 through 5.3.3 and Chapter 12,
printed pp.294--296,659,795 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F=2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
include D h hmany hn hpsl hH d hp hm hF he

/-- All three full centralizer comparisons retain the prescribed coherent marking. -/
theorem rankOne_global_symplectic_marked_centralizers
    (a : Global.SymplecticNormalizerMarking L (residual H) (Global.sourceS L H) F) :
    Global.SymplecticMarkedCentralizers a :=
  d.symplectic_marked_centralizers
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he a

/-- The canonical prepared extension has the same full centralizer comparisons. -/
theorem rankOne_global_symplectic_chosen_marked_centralizers :
    Global.SymplecticMarkedCentralizers
      (d.symplecticNormalizerMarking
        (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he) :=
  D.rankOne_global_symplectic_marked_centralizers h hmany hn hpsl hH d hp F hm hF he _

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
