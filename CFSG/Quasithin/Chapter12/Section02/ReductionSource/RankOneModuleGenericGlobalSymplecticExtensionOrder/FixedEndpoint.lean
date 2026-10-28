module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.FixedEndpoint
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticExtensionOrder.OuterConjugacy

/-!
# Chapter 12 compatible binary fixed endpoints

The original outer involution fixes a pair isomorphic to the actual binary
symplectic parabolic amalgam, including its whole common Borel. Both fixed
endpoint two-residuals are A4, with minimal normal Klein four cores.

These literal applications keep Hypothesis 12.2.1, many locals, the original
n>1 and PSL2 quotient, HStar, Preparation, and the perfect whole residual,
with W=wholeReduced T L and both amalgam orientations.

Source: Aschbacher--Smith F.4.37, printed p.293, applied through 5.3.3 and
Chapter 12, pp.659,795 of refs/quasithin.pdf. The D8 quotient obstruction,
S=T at q=4, and the same-extension ambient order comparison remain required.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The fixed original pair has the compatible binary matrix amalgam. -/
theorem rankOne_global_symplectic_outer_fixed_binary_amalgam
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
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ Global.sourceS L H) :
    Nonempty (RankTwoAmalgam.Iso
      (Global.sourceFixedParabolicAmalgam L (residual H) (Global.sourceS L H) f.val)
      (SourceNormalizerExtension.diagram (ZMod 2))) ∨
    Nonempty (RankTwoAmalgam.Iso
      (Global.sourceFixedParabolicAmalgam L (residual H) (Global.sourceS L H) f.val)
      (SourceNormalizerExtension.diagram (ZMod 2)).reverse) :=
  d.symplectic_outer_fixed_binary_amalgam
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he f hf ho

/-- Both original fixed endpoint two-residuals are A4. -/
theorem rankOne_global_symplectic_outer_fixed_endpoint_twoResidual
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
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ Global.sourceS L H) (i : Fin 2) :
    Nonempty (pResidual 2 (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i ⊓
      centralizer ({f.val} : Set G) : Subgroup G) ≃* alternatingGroup (Fin 4)) :=
  d.symplectic_outer_fixed_endpoint_twoResidual
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he f hf ho i

/-- The actual fixed endpoint residual cores are minimal normal Klein fours. -/
theorem rankOne_global_symplectic_outer_fixed_endpoint_core
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
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ Global.sourceS L H) (i : Fin 2) :
    let E := pResidual 2 (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i ⊓
      centralizer ({f.val} : Set G) : Subgroup G)
    IsKleinFour (pCore 2 E) ∧
      ∀ U : Subgroup E, U.Normal → U≤pCore 2 E → U=⊥ ∨ U=pCore 2 E :=
  d.symplectic_outer_fixed_endpoint_core
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he f hf ho i

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
