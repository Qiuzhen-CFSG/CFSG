module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.SourceSmallCompletion
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.ExtensionInvolutionRecognition
/-!
# The marked F.5.5 fixed-endpoint recognition consumer

The two source involutions in the literal ordinary fixed endpoints retain
their overlap escape under the original embedding. Their order-four product
therefore supplies the quadrangle metric of the actual doubled completion.
The resulting comparison preserves both full marked endpoint ranges.

Source: Aschbacher--Smith F.5.5(4), printed p.302, applying F.4.26, p.288.
The independent D≈S₆ branch supplies the two fixed-endpoint witnesses.
-/
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0)) (i : G0 →* G)

theorem source_parabolic_preserving_equiv_of_fixed_endpoints (hi : Function.Injective i)
    (s t : G) (hs : s∈Dendpoint c i false) (ht : t∈Dendpoint c i true)
    (hsout : s∉Dendpoint c i false⊓Dendpoint c i true)
    (htout : t∉Dendpoint c i false⊓Dendpoint c i true)
    (hs2 : orderOf s=2) (ht2 : orderOf t=2) (hst : orderOf (s*t)=4) :
    ∃ e : G0≃*Extension.ProjectiveExtension 1 hn,
      c.left.range.map e.toMonoidHom=Extension.point 1 hn ∧
      c.right.range.map e.toMonoidHom=Extension.plane 1 hn := by
  let : Finite G0 := Finite.of_injective i hi
  exact SourceCompletion.UnitaryTwo.Extension.Completion.exists_parabolic_preserving_equiv_of_diameter c
    (source_quadrangle_metric_of_fixed_endpoints c i hi s t hs ht hsout htout hs2 ht2 hst)
end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
