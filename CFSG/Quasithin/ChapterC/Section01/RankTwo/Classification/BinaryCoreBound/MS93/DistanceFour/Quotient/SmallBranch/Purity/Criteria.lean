module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ModuleData

/-!
# The marked parabolic calculations needed for the small branch

The two conditions concern the same actual parabolic: a nonzero natural
coordinate fixed by its source-ordered rank-one residual, and a codimension
bound for its embedded intrinsic two-core on the original representation.
The marking is retained. These conditions neither assert a multiplicity nor
remove the representation's fixed space, and no constructor is asserted here.

They separate the geometric argument in MS93 (4.6.11), printed p.909, from
the binary model calculation needed to select one of the two multiplicities
allowed by (1.4), printed p.842. The geometric constructor must use the real
parabolic preimages and establish both conditions for the same side of the flag.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
open Subgroup Representation.BinaryOffender

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- Two concrete calculations at one marked parabolic, before applying any
multiplicity deduction. The rank-one residual is O²(O^{2′}(P)). -/
structure ParabolicBounds (ρ : Representation (ZMod 2) SL W)
    (marking : SL ≃* SL) (g : SL) (i : Bool) : Prop where
  fixed_vector : ∃ w : Fin 3 → ZMod 2, w ≠ 0 ∧
    ∀ k ∈ rankOne (modelParabolic g i), (marking k).val.mulVec w = w
  codimension : fixedCodim ρ
    ((pCore 2 (modelParabolic g i)).map (modelParabolic g i).subtype) ≤ 2

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
