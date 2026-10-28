module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityTwo.Hexagon
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.Pair
public import Theory.GroupAction.RankTwoCosetCover.SmallCover

/-!
# Marked recognition from a shared triality hexagon relation

Pair two faithful completions in their product. Matching endpoint involutions
satisfy the hexagon relation in that paired completion, whose graph consequently
has diameter at most six. Each projection is a coset covering onto a graph of
girth at least twelve, so both are injective. The resulting group equivalence
preserves both original endpoint maps, hence their common Borel marking.

Source: Aschbacher--Smith F.3.3--6 and F.4.8, pp.270--272,278. This conditional
recognition result does not derive the relation required by F.4.31.
-/

@[expose] public noncomputable section
open Theory.GroupTheory Subgroup Subgroup.CosetGeometry.RankTwo
open _root_.Triality.Standard.Parabolics
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.Completion
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
theorem exists_mulEquiv_of_matching_involutions
    (s : parabolic parameters .arms) (t : parabolic parameters .central)
    (hs : s^2=1) (ht : t^2=1)
    (hsout : c.left s∉c.middle.range) (htout : c.right t∉c.middle.range)
    (hc : (c.left s*c.right t)^6=1) (hd : (d.left s*d.right t)^6=1) :
    ∃ f : G ≃* H, (∀ x, f (c.left x) = d.left x) ∧
      (∀ x, f (c.right x) = d.right x) := by
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
  let ef := MulEquiv.ofBijective (c.pairFst d) ⟨hif,(pair_cover_fst c d).surjective⟩
  let es := MulEquiv.ofBijective (c.pairSnd d) ⟨his,(pair_cover_snd c d).surjective⟩
  refine ⟨ef.symm.trans es,?_,?_⟩
  · intro x
    change es (ef.symm (c.left x)) = d.left x
    have he : ef (e.left x) = c.left x := c.pairFst_left d x
    rw [←he,ef.symm_apply_apply]
    exact c.pairSnd_left d x
  · intro x
    change es (ef.symm (c.right x)) = d.right x
    have he : ef (e.right x) = c.right x := c.pairFst_right d x
    rw [←he,ef.symm_apply_apply]
    exact c.pairSnd_right d x

/-- Forgetting the endpoint equations gives the underlying group identification. -/
theorem nonempty_mulEquiv_of_matching_involutions
    (s : parabolic parameters .arms) (t : parabolic parameters .central)
    (hs : s^2=1) (ht : t^2=1)
    (hsout : c.left s∉c.middle.range) (htout : c.right t∉c.middle.range)
    (hc : (c.left s*c.right t)^6=1) (hd : (d.left s*d.right t)^6=1) :
    Nonempty (G ≃* H) := by
  obtain ⟨f,_,_⟩ := c.exists_mulEquiv_of_matching_involutions d s t hs ht hsout htout hc hd
  exact ⟨f⟩
end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.Completion
