module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Marking
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalM23.Local

/-!
# The actual exceptional-local marking at the Chapter 12 consumer

Specialize the generic input with the ChosenModule's whole reduced subgroup.
The original nonmaximal linear branch selects J, and source 5.2.17 identifies
J with the native M₂₃ heptad stabilizer. The same equivalence maps its entire
two-core, the original H, and the whole residual K to the native kernel,
heptad–pair intersection, and pointwise pair fixer. No local recognition or
splitting premise is added.

Source: Aschbacher–Smith 5.2.11(1), 5.2.17, printed pp.653,655
(`refs/quasithin.pdf`). The compatible linear-completion marking and ambient
M₂₃ recognition remain necessary for the final GlobalExit application.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
open Sporadic.Mathieu.M23Geometry
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original exceptional local, core, and pair subgroups share one
actual native heptad marking. -/
theorem rankOne_global_linear_nonmaximal_exceptional_heptad_marking
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
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G))
    : ∃ J ∈ Chapter1.LStar G (T : Subgroup G), residual H < J ∧
      ∃ ζ : J ≃* heptadStabilizer,
        (pCore 2 J).map ζ.toMonoidHom = heptadKernel ∧
        ((residual H).subgroupOf J).map ζ.toMonoidHom =
          (fixingSubgroup (Equiv.Perm (Fin 7)) ({5,6} : Set (Fin 7))).comap heptadAction ∧
        (H.subgroupOf J).map ζ.toMonoidHom = pairStabilizer.subgroupOf heptadStabilizer := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨_,hc⟩ := d.linear_maximal_or_exceptional hi hH hp F hm hF he
  obtain ⟨_,J,hJ,hKJ,_⟩ := hc.resolve_left hnonmax
  exact ⟨J,hJ,hKJ,d.linear_exceptional_pair_heptad_marking hi hH hp F hm hF he hJ hKJ⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
