module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.OuterDegree
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticExtensionOrder.MarkedCentralizers

/-!
# Chapter 12 odd outer degree and native involution lifts

For the original prepared row, including n=2 and both orientations, the
same marked extension has odd outer degree. Its native unipotent subgroup
is Sylow and all its involutions lift to the native group. The original
Hypothesis 12.2.1, many locals, PSL2 quotient, HStar and perfect whole
residual are retained, with W=wholeReduced T L.

Source: Aschbacher--Smith F.4.38,43 through 5.3.3 and Chapter 12,
printed pp.294,296,659,795 of refs/quasithin.pdf.
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

variable (a : Global.SymplecticNormalizerMarking L (residual H) (Global.sourceS L H) F)

/-- The full extension has odd outer degree over its native inner image. -/
theorem rankOne_global_symplectic_extension_outer_odd :
    ¬2∣a.extension.innerMap.range.index :=
  d.symplectic_extension_outer_odd
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp hm hF he a

/-- The native unipotent subgroup remains Sylow in the full marked extension. -/
theorem rankOne_global_symplectic_extension_native_sylow :
    ∃ Q : Sylow 2 a.extension.carrier,
      (Q : Subgroup _)=(unipotent (F := F)).map a.extension.innerMap :=
  d.symplectic_extension_native_sylow
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp hm hF he a

/-- Every full-extension involution lifts through the same literal inner map. -/
theorem rankOne_global_symplectic_extension_involution_lift
    (x : a.extension.carrier) (hx : orderOf x=2) :
    ∃ v : Sp F, orderOf v=2 ∧ a.extension.innerMap v=x :=
  d.symplectic_extension_involution_lift
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp hm hF he a x hx

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
