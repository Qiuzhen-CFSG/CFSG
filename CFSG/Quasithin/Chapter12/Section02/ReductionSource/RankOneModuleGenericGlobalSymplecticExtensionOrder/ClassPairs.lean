module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.ClassPairs
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticExtensionOrder.OuterDegree

/-!
# Chapter 12 three-representative involution coverage

The three pinned Sylow-center involutions cover all ambient involutions
and their native images cover every involution in the same full extension.
The source proof transports actual parabolic conjugators through the pure
amalgam, in either orientation. The native proof uses its Sylow subgroup
in the full extension. Distinctness of these classes and preservation of
class membership inside full centralizers remain separate obligations.

The original Hypothesis 12.2.1, many locals, PSL2 quotient, HStar,
Preparation and perfect whole residual remain in force, with
W=wholeReduced T L. Source: Aschbacher--Smith F.4.27,30,35,38,43,
printed pp.288--296, through 5.3.3 and Chapter 12 of refs/quasithin.pdf.
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

open Theory.SpecificGroups.SymplecticFour.SourceFusionOrder

/-- Three marked involutions in the original Sylow center cover all ambient involutions. -/
theorem rankOne_global_symplectic_three_class_cover :
    ∃ a : Global.sourceS L H≃*unipotent (F := F),
      (∀ i : Fin 3, orderOf (a.symm (centralRepresentative i)).val=2 ∧
        a.symm (centralRepresentative i)∈center (Global.sourceS L H)) ∧
      ∀ x : G, orderOf x=2 → ∃ i : Fin 3,
        IsConj (a.symm (centralRepresentative i)).val x :=
  d.symplectic_three_class_cover
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he

/-- The same full extension is covered by the three pinned native images. -/
theorem rankOne_global_symplectic_extension_three_class_cover
    (a : Global.SymplecticNormalizerMarking L (residual H) (Global.sourceS L H) F) :
    ∀ x : a.extension.carrier, orderOf x=2 → ∃ i : Fin 3,
      IsConj (a.extension.innerMap (centralRepresentative i).val) x :=
  d.symplectic_extension_three_class_cover
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he a

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
