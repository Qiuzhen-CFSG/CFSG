module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Local.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Local.Linear.Group
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Local.Linear.Span

/-!
# The local seed plane from its displacement line

For the two parabolic preimages of one incident flag, a seed fixed by the
second intrinsic core is a module for the actual binary rank-one quotient.
Two conjugate transvections generate this quotient, and the first core
supplies one of them. A one-dimensional bound on the first core's moved
space therefore bounds the seed dimension by two. Nonzero full-actor
commutator generation excludes dimensions zero and one. The displacement
space fills the given line, whose conjugates span the seed.

This proves precisely the conditional linear step in the first paragraph
after MS93 (4.6.12)(3), printed p.910. The midpoint displacement bound and
construction of the geometric seed remain with the Local assembly.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), printed p.910.
-/

public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

/-- The actual incident parabolics recognize a seed plane from a line bound
on its opposite-core displacements, with no natural-module premise. -/
theorem parabolic_plane_of_line_bound (f : Frame source)
    (ρ : Representation (ZMod 2) SL W) (A T : Submodule (ZMod 2) W)
    (hA : ∀ m ∈ f.parabolic true, ∀ v ∈ A, ρ (source.projection m) v ∈ A)
    (hfix : A ≤ fixedSpace ρ ((f.core true).map source.projection))
    (hA0 : A ≠ ⊥)
    (hmoved : movedSpace ρ ((f.actor true).map source.projection) A = A)
    (hT : Module.finrank (ZMod 2) T = 1)
    (hbound : movedSpace ρ ((f.core false).map source.projection) A ≤ T) :
    Module.finrank (ZMod 2) A = 2 ∧
      movedSpace ρ ((f.core false).map source.projection) A = T ∧
      orbitSpace ρ ((f.parabolic true).map source.projection) T = A := by
  obtain ⟨hQP, t, s, ht, hs, hgen⟩ := frame_transvection_generators f
  have hKP : (f.core true).map source.projection ≤
      (f.parabolic true).map source.projection :=
    map_mono (map_subtype_le _)
  have hstable : ∀ g ∈ (f.parabolic true).map source.projection,
      ∀ v ∈ A, ρ g v ∈ A := by
    rintro _ ⟨m, hm, rfl⟩ v hv
    exact hA m hm v hv
  rw [f.actor_eq] at hmoved
  exact plane_of_two_transvections ρ ((f.parabolic true).map source.projection) A
    ((f.core false).map source.projection) ((f.core true).map source.projection)
    hQP hKP t s ht hs hgen T hstable hfix hA0 hmoved hT hbound

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
