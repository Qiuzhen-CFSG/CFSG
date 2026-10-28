module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.CoreContainment
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLinearAmbient.CoreDisplacement

/-!
# The original Chapter12 linear centralizers outside field four

The chosen module supplies the unchanged generic Input. The actual whole
parabolic comparison now proves the centralizer bound and exact two-core
for every involution on Z(S), for every original degree n>2, including
even degrees. Distinct ambient conjugates of this line are disjoint.
No local core, torus-action, or centralizer callback is required.
The field-four exception and terminal PSL₃ recognition remain open.
Source: Aschbacher–Smith §5.3.7, p.660, used in §12.2, p.795.
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


/-- The literal original linear row has the source centralizer bound and exact
core at every degree greater than two. -/
theorem rankOne_global_linear_centralizers_of_large (hlarge : 2 < n)
    (z : G) (hz2 : orderOf z = 2) (hz : z ∈ centerIn (Global.sourceS L H)) :
    centralizer ({z} : Set G) ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ∧
      (centralizer ({z} : Set G)).pCoreIn 2 = Global.sourceS L H := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.linear_centralizer_le_inter_of_large hi hH hp F hm hF he hmax hlarge z hz2 hz,
    d.linear_centralizer_core_eq_of_large hi hH hp F hm hF he hmax hlarge z hz2 hz⟩

/-- The actual central line has trivial intersection with each distinct
ambient conjugate, retaining the original chosen module and exponent. -/
theorem rankOne_global_linear_center_TI_of_large (hlarge : 2 < n) (g : G) :
    (centerIn (Global.sourceS L H)).map (MulAut.conj g).toMonoidHom = centerIn (Global.sourceS L H) ∨
      Disjoint (centerIn (Global.sourceS L H))
        ((centerIn (Global.sourceS L H)).map (MulAut.conj g).toMonoidHom) :=
  d.linear_center_TI_of_large (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax hlarge g

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
