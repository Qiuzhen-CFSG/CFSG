module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Pair
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Original Chapter 12 application of the exceptional local geometry

For the chosen module and its prepared whole-residual linear comparison,
nonmaximality selects the actual exceptional A₇ overcomponent. The source
local argument proves it is maximal two-local, contains the original T
and H, and is the full normalizer of its self-centralizing two-core.
In one seven-point quotient marking, the original K = O²(H) is the
pointwise pair fixer and H is the setwise pair stabilizer. The second
application records both original elementary sixteen-cores and |T:S| = 2.

These are local steps of 5.2.11 at the literal Chapter 12 consumer. They
do not yet identify G with M₂₃ or establish GlobalExit. Perfectness and
Preparation retain the existing whole-residual data, including unique_left.
Source: Aschbacher–Smith 5.2.11, pp.653–654, and 12.2.22, p.795
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original pair and the maximal exceptional local share one actual
seven-point quotient marking; neither original factor is replaced by a model. -/
theorem rankOne_global_linear_nonmaximal_local_marking
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
      (LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    ∃ J ∈ Chapter1.LStar G (T : Subgroup G), residual H < J ∧
      ChapterC.IsExceptionalA7Block J ∧ (T : Subgroup G) ≤ J ∧ H ≤ J ∧
      IsMaximalTwoLocal J ∧ normalizer (J : Set G) = J ∧
      normalizer (J.pCoreIn 2 : Set G) = J ∧
      centralizer (J.pCoreIn 2 : Set G) = J.pCoreIn 2 ∧
      H.pCoreIn 2 = J.pCoreIn 2 ∧ Nat.card J = 40320 ∧
      ∃ e : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 7),
        ∃ i j : Fin 7, i ≠ j ∧
          let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
          (residual H).subgroupOf J =
            (fixingSubgroup (alternatingGroup (Fin 7)) ({i,j} : Set (Fin 7))).comap q ∧
          H.subgroupOf J =
            (MulAction.stabilizer (alternatingGroup (Fin 7)) ({i,j} : Set (Fin 7))).comap q ∧
          IsCoatom (H.subgroupOf J) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨_,hc⟩ := d.linear_maximal_or_exceptional hi hH hp F hm hF he
  obtain ⟨_,J,hJ,hKJ,hblock⟩ := hc.resolve_left hnonmax
  obtain ⟨hTJ,hHJ,hmax,hNJ,hNU,hCU,hcore,hcard⟩ :=
    d.linear_exceptional_local hi hH hp F hm hF he hJ hKJ
  exact ⟨J,hJ,hKJ,hblock,hTJ,hHJ,hmax,hNJ,hNU,hCU,hcore,hcard,
    d.linear_exceptional_pair_marking hi hH hp F hm hF he hJ hKJ⟩

/-- Both original cores and the Sylow-index clause of 5.2.11 on the
prepared Chapter 12 whole-residual pair. -/
theorem rankOne_global_linear_nonmaximal_core_geometry
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
      (LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    m = 2 ∧ n = 2 ∧ Nat.card F = 4 ∧
      (∀ i : Fin 2, IsElementaryAbelian 2 (pCore 2 (![L,residual H] i)) ∧
        Nat.card (pCore 2 (![L,residual H] i)) = 16) ∧
      (normalizer (L : Set G)).pCoreIn 2 = L.pCoreIn 2 ∧
      normalizer (L.pCoreIn 2 : Set G) = normalizer (L : Set G) ∧
      centralizer (L.pCoreIn 2 : Set G) = L.pCoreIn 2 ∧
      Nat.card T = 128 ∧ Nat.card (Global.sourceS L H) = 64 ∧
      (Global.sourceS L H).relIndex (T : Subgroup G) = 2 :=
  d.linear_nonmaximal_core_geometry (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hnonmax

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
