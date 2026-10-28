module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.Transport

/-!+# The remaining local geometry in the two Z-cases

These are the three geometric assertions at the bottom of MS93 p.899.
The products are literal setwise products in their printed order. The
moving second layer is the conjugate of the original layer, and its first
layer uses both transported vertices. No independence of path choices is
postulated. This is an output contract, not a constructor from the source.

`TwoCases` proves the equal-case kernel argument and consumes all three
assertions in the existing (4.5.5) assembly. Their source proof remains a
prerequisite, independently of the opening noncentrality assertion.
Source: Meierfrankenfeld--Stellmacher (1993), (4.5.5), printed p.899.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases
open NormalizerTransfer
variable {M : Type*} [Group M] {R : Subgroup M}

/-- Literal geometric obligations for beta=a+1, gamma=beta^g and delta=(a+2)^g.
The opening noncentrality assertion is separate. -/
structure ZCaseGeometry {a : Vertex R} (p : Higher.SourcePath a) : Prop where
  equal_Z_span : ∀ g : stabilizer R a,
    Z R (p.walk.getVert 5) = Z R (act R g (p.walk.getVert 5)) →
    (Z R (p.walk.getVert 6) : Set (FreeAmalgam R)) ⊆
      (Z R a : Set (FreeAmalgam R)) *
        (Z R (act R g (p.walk.getVert 6)) : Set (FreeAmalgam R))
  unequal_Z_commutator : ∀ g : stabilizer R a,
    Z R (p.walk.getVert 5) ≠ Z R (act R g (p.walk.getVert 5)) →
    ((⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      rightConjugate (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) g⁆ :
        Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) ⊆
      ((hatV R a (p.walk.getVert 6) : Set (FreeAmalgam R)) *
        (hatV R (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R))) ∩
      ((hatV R (act R g (p.walk.getVert 6)) (act R g (p.walk.getVert 8)) :
          Set (FreeAmalgam R)) * (hatV R a (p.walk.getVert 6) : Set (FreeAmalgam R)))
  unequal_Z_intersection : ∀ g : stabilizer R a,
    Z R (p.walk.getVert 5) ≠ Z R (act R g (p.walk.getVert 5)) →
      ((hatV R a (p.walk.getVert 6) : Set (FreeAmalgam R)) *
        (hatV R (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R))) ∩
      ((hatV R (act R g (p.walk.getVert 6)) (act R g (p.walk.getVert 8)) :
          Set (FreeAmalgam R)) * (hatV R a (p.walk.getVert 6) : Set (FreeAmalgam R))) =
      (hatV R a (p.walk.getVert 6) : Set (FreeAmalgam R))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases
