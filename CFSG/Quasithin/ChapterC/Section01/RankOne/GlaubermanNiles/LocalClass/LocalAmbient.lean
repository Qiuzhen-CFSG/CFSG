module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.Marking
public import Stellmacher.BaumannMap
public import CFSG.Quasithin.ChapterB.Section02.Thompson
/-!
# One original Baumann source in different local ambient groups

The canonical subgroup image identifies the Baumann subgroup computed inside
an overgroup with the original ambient Baumann subgroup. Re-marking a local
class embedding along this identification retains the literal ambient
inclusion. Thus one universal C.1.18 characteristic pair applies in both
original local groups without changing the source two-group.

Source: Aschbacher–Smith C.1.17–19 and 10.2.3(4), pp.126–127,746.
-/

public noncomputable section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
open ChapterB
variable {G : Type*} [Group G] [Finite G]
/-- Re-mark the local-class embedding by the original ambient Baumann group. -/
theorem original_baumann_embedding (R X : Subgroup G) (hRX : R ≤ X)
    (N : Subgroup X) (hBN : baumann (R.subgroupOf X) ≤ N)
    (hlocal : InLocalClass (inclusion hBN)) :
    ∃ f : baumann R →* N, InLocalClass f ∧
      (X.subtype.comp N.subtype).comp f = (baumann R).subtype := by
  let B := baumann (R.subgroupOf X)
  have hm : B.map X.subtype = baumann R := by
    dsimp only [B,baumann,thompsonAlpha]
    rw [baumann_map_injective X.subtype X.subtype_injective,map_subgroupOf_eq_of_le hRX]
  let a : B ≃* baumann R :=
    (B.equivMapOfInjective X.subtype X.subtype_injective).trans (MulEquiv.subgroupCongr hm)
  let f : baumann R →* N := (inclusion hBN).comp a.symm.toMonoidHom
  refine ⟨f,hlocal.precomp_equiv a.symm,?_⟩
  ext b
  exact congrArg (baumann R).subtype (a.apply_symm_apply b)
end CFSG.Quasithin.ChapterC.GlaubermanNiles
