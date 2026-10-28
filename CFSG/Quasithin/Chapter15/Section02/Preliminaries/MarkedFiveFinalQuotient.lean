module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveQuotientExclusions
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveSymmetricThreeDistance
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveS3ThreeExclusion

/-!
# The original marked-five H-star wreath quotient

The S₃ branch has critical distance three by the source small-alpha and
binary-alpha exclusions. The original central involution of the full
second parabolic instead forces distance one. Thus the literal Chapter 15
S₃ branch is impossible. The already proved single-S₅ and wreath-five
exclusions leave precisely the S₃ wreath C₂ quotient of 15.2.8.

All quotient markings and the original H-star subgroup are retained. This
argument uses the additional Chapter 15 center, so it does not exclude the
genuine generic Ree/Tits rank-two pairs or assume their enumeration.
Source: Aschbacher--Smith 15.2.4,15.2.8, printed pp.1106--1110;
DGS (1985), 8.1,8.6,11.4--11.5 and 12.1.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

/-- The original marked-five H-star subgroup cannot have the single S₃
quotient. Its literal full-parabolic center is essential to the proof. -/
theorem ChosenSmallSource.marked_five_HStar_not_symmetricThree
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ¬ Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) := by
  intro he
  have h1 := h.marked_five_symmetricThree_distance_one hd hH he
  have h3 := h.marked_five_symmetricThree_distance_three hd hH he
  omega

/-- Original 15.2.8 in the marked-five row, with every small-parabolic
recognition premise discharged on the actual H-star subgroup. -/
theorem ChosenSmallSource.HStar_wreath_of_marked_five
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) :=
  h.HStar_wreath_of_marked_five_of_not_symmetricThree hd hH
    (h.marked_five_HStar_not_symmetricThree hd hH)

end CFSG.Quasithin.Chapter15.Section02
