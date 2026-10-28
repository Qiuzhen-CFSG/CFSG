module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.CentralLine
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# The central line of the original prepared linear row

The affine pointwise-fixer argument gives C_T(Z(S)) = S. Characteristic-two
inheritance and the abelian quotient S/Z(S) give O₂(C_G(Z(S))) = S. Thus
N_G(Z(S)) = N_G(S) is the actual intersection of the factor normalizers.
These are the literal Chapter12 groups, including field four and both
orientations. Individual involution centralizers and ambient recognition
remain obligations of the same linear-row argument.

Source: Aschbacher–Smith 5.3.5, printed p.660, applied in Chapter12 on p.795
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
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

/-- Source §5.3.5 on the original Chapter12 central line, with all local
Sylow and core hypotheses discharged from the prepared linear comparison. -/
theorem rankOne_global_linear_center_normalizer :
    (T : Subgroup G) ⊓ centralizer (centerIn (Global.sourceS L H) : Set G) =
      Global.sourceS L H ∧
    (centralizer (centerIn (Global.sourceS L H) : Set G)).pCoreIn 2 =
      Global.sourceS L H ∧
    normalizer (centerIn (Global.sourceS L H) : Set G) =
      normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.linear_sylow_center_centralizer hi hH hp F hm hF he hmax,
    d.linear_center_centralizer_core hi hH hp F hm hF he hmax,
    d.linear_center_normalizer hi hH hp F hm hF he hmax⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
