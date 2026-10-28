module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.G2Three.Hexagon
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.Pair
public import Theory.GroupAction.RankTwoCosetCover.SmallCover

/-!
# Comparing ternary completions with a common hexagon relation

Form the image of the universal amalgam in the product of the two given
completions. A matching pair of endpoint involutions supplies a twelve-cycle
in this paired completion, hence its diameter is at most six. Each projection
is a coset covering onto a graph of girth at least twelve. The short-cover
injectivity theorem therefore makes both projections group isomorphisms.

This is a conditional comparison step toward Aschbacher–Smith F.4.26,
printed p.288. The matching relation must still be derived from the original
arbitrary involution pair before applying this theorem to recognition.
-/

@[expose] public noncomputable section
open Theory.GroupTheory Subgroup Subgroup.CosetGeometry.RankTwo
open Atlas.G2 Atlas.G2.LieParabolicSetup
namespace CFSG.Quasithin.ChapterF.SourceCompletion.G2Three.Completion
variable {G H : Type*} [Group G] [Group H] (c : Completion G) (d : Completion H)

private theorem pair_cover_fst :
    CoverData (c.pairCompletion d).cosetFamily c.cosetFamily (c.pairFst d) :=
  RankTwoAmalgam.FaithfulCompletion.coverData_of_hom _
    (by ext x; exact c.pairFst_left d x) (by ext x; exact c.pairFst_right d x)
    (overlap (c.pairCompletion d)) c.overlap
private theorem pair_cover_snd :
    CoverData (c.pairCompletion d).cosetFamily d.cosetFamily (c.pairSnd d) :=
  RankTwoAmalgam.FaithfulCompletion.coverData_of_hom _
    (by ext x; exact c.pairSnd_left d x) (by ext x; exact c.pairSnd_right d x)
    (overlap (c.pairCompletion d)) d.overlap

/-- A common pair of marked endpoint involutions satisfying the hexagon relation
in both completions identifies the actual ambient groups. -/
theorem nonempty_mulEquiv_of_matching_involutions
    (s : parabolic₁ (F := ZMod 3)) (t : parabolic₂ (F := ZMod 3))
    (hs : s^2=1) (ht : t^2=1)
    (hsout : c.left s∉c.middle.range) (htout : c.right t∉c.middle.range)
    (hc : (c.left s*c.right t)^6=1) (hd : (d.left s*d.right t)^6=1) :
    Nonempty (G ≃* H) := by
  let e : Completion (c.Pair d) := c.pairCompletion d
  have hes : e.left s∉e.middle.range := by
    rintro ⟨b,hb⟩
    apply hsout
    refine ⟨b,?_⟩
    have hh := congrArg (c.pairFst d) hb
    simpa only [RankTwoAmalgam.FaithfulCompletion.middle, MonoidHom.comp_apply,
      e, RankTwoAmalgam.FaithfulCompletion.pairFst_left] using hh
  have het : e.right t∉e.middle.range := by
    rintro ⟨b,hb⟩
    apply htout
    refine ⟨b,?_⟩
    have hh := congrArg (c.pairFst d) hb
    simpa only [RankTwoAmalgam.FaithfulCompletion.middle, MonoidHom.comp_apply,
      e, RankTwoAmalgam.FaithfulCompletion.pairFst_left,
      RankTwoAmalgam.FaithfulCompletion.pairFst_right] using hh
  have he6 : (e.left s*e.right t)^6=1 := by
    apply Subtype.ext
    apply Prod.ext
    · have h : c.pairFst d ((e.left s*e.right t)^6)=c.pairFst d 1 := by
        simpa only [map_pow,map_mul,map_one,e,
          RankTwoAmalgam.FaithfulCompletion.pairFst_left,
          RankTwoAmalgam.FaithfulCompletion.pairFst_right] using hc
      exact h
    · have h : c.pairSnd d ((e.left s*e.right t)^6)=c.pairSnd d 1 := by
        simpa only [map_pow,map_mul,map_one,e,
          RankTwoAmalgam.FaithfulCompletion.pairSnd_left,
          RankTwoAmalgam.FaithfulCompletion.pairSnd_right] using hd
      exact h
  have hdiam := (e.hexagon_metric_of_involutions (e.left s) (e.right t)
    ⟨s,rfl⟩ ⟨t,rfl⟩ hes het (by rw [←map_pow,hs,map_one])
      (by rw [←map_pow,ht,map_one]) he6).2.1
  have hif := (pair_cover_fst c d).injective_of_diameter_lt_girth e.connected hdiam
    (fun v p hp => (show (6 : ℕ) < 12 by decide).trans_le (c.cycle_length_ge_twelve v p hp))
  have his := (pair_cover_snd c d).injective_of_diameter_lt_girth e.connected hdiam
    (fun v p hp => (show (6 : ℕ) < 12 by decide).trans_le (d.cycle_length_ge_twelve v p hp))
  exact ⟨(MulEquiv.ofBijective (c.pairFst d) ⟨hif,(pair_cover_fst c d).surjective⟩).symm.trans
    (MulEquiv.ofBijective (c.pairSnd d) ⟨his,(pair_cover_snd c d).surjective⟩)⟩
end CFSG.Quasithin.ChapterF.SourceCompletion.G2Three.Completion
