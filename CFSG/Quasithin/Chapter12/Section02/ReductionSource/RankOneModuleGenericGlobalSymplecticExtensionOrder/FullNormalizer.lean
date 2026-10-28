module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.FullNormalizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticCompletion

/-!
# The constructed full-normalizer extension in Chapter 12

With W = wholeReduced T L, the original prepared source pair constructs the
full automorphism extension and the compatible whole-normalizer comparison.
Both pure parabolics and their whole Borel retain their actual markings,
including the reversed orientation and n = 2. The same constructed extension
is used in the existing completion and GlobalExit applications.

Those applications now retain only the ambient order bound against this
fixed full extension. Its remaining fusion and order proof is not asserted
here; the extension itself uses no order or recognition premise on G.

Source: Aschbacher–Smith 5.3.2, printed p.659, and its Chapter 12 application,
p.795 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.SourceCompletion.SymplecticFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original source inputs give the full extension with both pure endpoint
maps and the entire common Borel marking retained. -/
theorem rankOne_global_symplectic_full_normalizer_marking
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)) :
    m = n ∧ Nonempty (Global.SymplecticNormalizerMarking L (residual H) (Global.sourceS L H) F) :=
  d.symplectic_full_normalizer_marking
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he

/-- The actual full-normalizer comparison is constructed, in either orientation. -/
theorem rankOne_global_symplectic_full_normalizer_extension
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)) :
    m = n ∧ ∃ E : SourceExtension F,
      Nonempty (RankTwoAmalgam.Iso (Global.SymplecticCompletion.diagram L (residual H)) E.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso (Global.SymplecticCompletion.diagram L (residual H)) E.amalgam.reverse) :=
  d.symplectic_full_normalizer_extension
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he

/-- The literal prepared completion uses the constructed full extension;
only its ambient order comparison is still required. -/
theorem rankOne_global_symplectic_prepared_extension_completion_of_order
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (hcard : Nat.card G ≤ Nat.card
      (d.symplecticNormalizerMarking
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he).extension.carrier) :
    let E := (d.symplecticNormalizerMarking
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he).extension
    m = n ∧ Nat.card F = 2^n ∧
      Chapter5.Section03GreenExtension.SourceLocalConditions
        (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∧
      ∃ c : Completion E (Global.SymplecticCompletion.join L (residual H)),
        c.middle.range = (normalizer (L : Set G) ⊓ normalizer (residual H : Set G)).subgroupOf
          (Global.SymplecticCompletion.join L (residual H)) ∧
        c.left.range ⊓ c.right.range = c.middle.range ∧
        Nat.card (Global.SymplecticCompletion.join L (residual H)) ≤ Nat.card E.carrier ∧
        c.middle.range.normalCore = ⊥ ∧
        Function.Injective (MulAction.toPermHom (Global.SymplecticCompletion.join L (residual H))
          (Subgroup.CosetGeometry.RankTwo.Vertex c.cosetFamily)) ∧
        Nat.card c.unipotentMap.range = Nat.card F ^ 4 ∧
        Nat.card c.torusMap.range = (Nat.card F - 1)^2 ∧
        c.torusMap.range ≤ normalizer (c.unipotentMap.range : Set (Global.SymplecticCompletion.join L (residual H))) ∧
        c.unipotentMap.range ⊓ centralizer
          (c.torusMap.range : Set (Global.SymplecticCompletion.join L (residual H))) = ⊥ :=
  d.symplectic_prepared_extension_completion_of_order
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hcard

/-- The prepared row reaches GlobalExit once the remaining order comparison
is proved for the same extension constructed from its original source inputs. -/
theorem rankOne_globalExit_of_symplectic_prepared_extension_order
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (hcard : Nat.card G ≤ Nat.card
      (d.symplecticNormalizerMarking
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he).extension.carrier) :
    RankOneModule.GlobalExit G :=
  D.rankOne_globalExit_of_symplectic_extension h hmany hn hpsl hH d hp F hm hF he
    (d.symplecticNormalizerMarking
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he).extension
    (d.symplecticNormalizerMarking
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he).full_comparison hcard

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
