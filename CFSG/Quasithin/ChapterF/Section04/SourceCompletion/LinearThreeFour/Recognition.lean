module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeFour.Smallness
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeFour.PlaneRecognition

/-!
# Recognition of finite PSL₃(4) completions from endpoint involutions

Two endpoint involutions outside the whole marked Borel, whose product has
order three, force the completion's coset geometry to be a plane of order four.
The plane recognition theorem then identifies the completion with the actual
matrix group PSL₃(4), simultaneously preserving its point and line parabolics.
The whole overlap, geometric bounds and action comparison are all proved from
the original completion and involutions.

This is the finite PSL₃(4) specialization of the equality case in
Aschbacher–Smith F.4.26 (printed p.288), using F.3.6 and F.4.8(2).
-/

public section

namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour.Completion

variable {G : Type*} [Group G] [Finite G] (c : Completion G)

/-- The finite PSL₃(4) case of F.4.26, with both actual endpoint ranges
preserved and no geometric or recognition premise. -/
theorem exists_parabolic_preserving_equiv_of_involutions (s t : G)
    (hs : s ∈ c.left.range) (ht : t ∈ c.right.range)
    (hsout : s ∉ c.middle.range) (htout : t ∉ c.middle.range)
    (hs2 : orderOf s = 2) (ht2 : orderOf t = 2) (hst : orderOf (s * t) = 3) :
    ∃ e : G ≃* Matrix.PSL3Four.PSL,
      c.left.range.map e.toMonoidHom =
        Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F ∧
      c.right.range.map e.toMonoidHom =
        Matrix.PSL3.LinearThree.lineParabolic Matrix.PSL3Four.F := by
  obtain ⟨ho, hu, hd, hv⟩ := c.smallness_of_involutions s t hs ht hsout htout hs2 ht2 hst
  exact c.exists_parabolic_preserving_equiv_of_plane_geometry ho hu hd hv

end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour.Completion
