module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.SymplecticFour.Recognition

/-!
# Marking-preserving recognition of symplectic completions

The common-cover proof of nonbinary symplectic recognition identifies the
actual endpoint maps. We retain those equations by constructing the equivalence
from the two projections of the paired completion. Girth eight and the shared
Weyl relation make both projections injective; generation makes them surjective.

This refinement is used to extend automorphisms of the native marked amalgam:
the original and twisted completions already have the native order. No bound
on the order of an external source group is involved in that application.

Source: Aschbacher–Smith F.4.8–10 and F.4.16–17, printed pp.278–283 of
`refs/quasithin.pdf`, via the published symplectic completion recognition.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
open SimpleGraph.PathTransitivePolygon.QuadrangleRecognition
namespace CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2] [Finite F]
namespace Completion
variable {E : SourceExtension F} {M : Type*} [Group M] (c : Completion E M)
omit [Finite F] [CharP F 2] in
private theorem marked_pair_overlap {H : Type*} [Group H] (d : Completion E H)
    (hc : c.left.range ⊓ c.right.range = c.middle.range) :
    (c.pairCompletion d).left.range ⊓ (c.pairCompletion d).right.range =
      (c.pairCompletion d).middle.range := by
  let e := c.pairCompletion d
  apply le_antisymm _ (le_inf e.middle_le_left e.middle_le_right)
  rintro z ⟨⟨x,hx⟩,⟨y,hy⟩⟩
  have hxy : c.left x=c.right y := by
    have he := congrArg (c.pairFst d) (hx.trans hy.symm)
    simpa only [e,RankTwoAmalgam.FaithfulCompletion.pairFst_left,
      RankTwoAmalgam.FaithfulCompletion.pairFst_right] using he
  obtain ⟨b,hb⟩ := hc.le (show c.left x∈c.left.range⊓c.right.range from
    ⟨⟨x,rfl⟩,⟨y,hxy.symm⟩⟩)
  have hbx : E.amalgam.left b=x :=
    c.left_injective hb
  exact ⟨b,by change e.left _=z; rw [hbx]; exact hx⟩

/-- Matching endpoint involutions with the quadrangle relation determine the actual
completion group; the whole overlap is retained in both projections. -/
theorem exists_marked_mulEquiv_of_matching_involutions {H : Type*} [Group H]
    (d : Completion E H)
    (hcO : c.left.range ⊓ c.right.range = c.middle.range)
    (hdO : d.left.range ⊓ d.right.range = d.middle.range)
    (s : E.left) (t : E.right)
    (hs : s^2=1) (ht : t^2=1)
    (hsout : c.left s∉c.middle.range) (htout : c.right t∉c.middle.range)
    (hc : (c.left s*c.right t)^4=1) (hd : (d.left s*d.right t)^4=1) :
    ∃ f : M ≃* H, (∀ x, f (c.left x) = d.left x) ∧
      (∀ x, f (c.right x) = d.right x) := by
  let e : Completion E (c.Pair d) := c.pairCompletion d
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
  have he6 : (e.left s*e.right t)^4=1 := by
    apply Subtype.ext
    apply Prod.ext
    · have h : c.pairFst d ((e.left s*e.right t)^4)=c.pairFst d 1 := by
        simpa only [map_pow,map_mul,map_one,e,
          RankTwoAmalgam.FaithfulCompletion.pairFst_left,
          RankTwoAmalgam.FaithfulCompletion.pairFst_right] using hc
      exact h
    · have h : c.pairSnd d ((e.left s*e.right t)^4)=c.pairSnd d 1 := by
        simpa only [map_pow,map_mul,map_one,e,
          RankTwoAmalgam.FaithfulCompletion.pairSnd_left,
          RankTwoAmalgam.FaithfulCompletion.pairSnd_right] using hd
      exact h
  have heO := c.marked_pair_overlap d hcO
  have hdiam := (e.quadrangle_metric_of_involutions heO (e.left s) (e.right t)
    ⟨s,rfl⟩ ⟨t,rfl⟩ hes het (by rw [←map_pow,hs,map_one])
      (by rw [←map_pow,ht,map_one]) he6).2.1
  have hf : CoverData e.cosetFamily c.cosetFamily (c.pairFst d) :=
    RankTwoAmalgam.FaithfulCompletion.coverData_of_hom _
      (by ext x; exact c.pairFst_left d x) (by ext x; exact c.pairFst_right d x) heO hcO
  have hg : CoverData e.cosetFamily d.cosetFamily (c.pairSnd d) :=
    RankTwoAmalgam.FaithfulCompletion.coverData_of_hom _
      (by ext x; exact c.pairSnd_left d x) (by ext x; exact c.pairSnd_right d x) heO hdO
  have hif := hf.injective_of_diameter_lt_girth e.connected hdiam
    (fun v p hp => (show (4 : ℕ) < 8 by decide).trans_le (c.cycle_length_ge_eight hcO v p hp))
  have his := hg.injective_of_diameter_lt_girth e.connected hdiam
    (fun v p hp => (show (4 : ℕ) < 8 by decide).trans_le (d.cycle_length_ge_eight hdO v p hp))
  let f := (MulEquiv.ofBijective (c.pairFst d) ⟨hif,hf.surjective⟩).symm.trans
    (MulEquiv.ofBijective (c.pairSnd d) ⟨his,hg.surjective⟩)
  refine ⟨f, ?_, ?_⟩
  · intro x
    change c.pairSnd d ((MulEquiv.ofBijective (c.pairFst d) ⟨hif,hf.surjective⟩).symm (c.left x)) = _
    rw [←c.pairFst_left d x]
    exact (congrArg (c.pairSnd d)
      ((MulEquiv.ofBijective (c.pairFst d) ⟨hif,hf.surjective⟩).symm_apply_apply _)).trans
        (c.pairSnd_left d x)
  · intro x
    change c.pairSnd d ((MulEquiv.ofBijective (c.pairFst d) ⟨hif,hf.surjective⟩).symm (c.right x)) = _
    rw [←c.pairFst_right d x]
    exact (congrArg (c.pairSnd d)
      ((MulEquiv.ofBijective (c.pairFst d) ⟨hif,hf.surjective⟩).symm_apply_apply _)).trans
        (c.pairSnd_right d x)


/-- For q > 2 the marked full-extension completion is identified with the
original extension itself: the Cartan argument has aligned the actual Weyl
reflections. This strengthening is proved through their paired completion. -/
theorem exists_marked_mulEquiv_of_card_le [Finite M] {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hcard : Nat.card M≤Nat.card E.carrier) : ∃ f : M ≃* E.carrier, (∀ x, f (c.left x) = E.modelCompletion.left x) ∧
      (∀ x, f (c.right x) = E.modelCompletion.right x) := by
  apply c.exists_marked_mulEquiv_of_matching_involutions E.modelCompletion ho E.model_overlap
    E.pointWeyl E.planeWeyl E.pointWeyl_sq E.planeWeyl_sq
  · rintro ⟨b,hb⟩
    have he := congrArg Subtype.val (c.left_injective hb)
    change b.val=MulAut.conj (WeylFrame.pointReflection (F := F)) at he
    have hm : MulAut.conj (WeylFrame.pointReflection (F := F)) ∈ E.middle ⊓ inner F :=
      ⟨he ▸ b.property,⟨_,rfl⟩⟩
    obtain ⟨g,hg,hg'⟩ := E.middle_inner.le hm
    exact WeylFrame.pointReflection_not_mem
      ((SourceExtension.inner_injective (F := F) hg') ▸ hg.2)
  · rintro ⟨b,hb⟩
    have he := congrArg Subtype.val (c.right_injective
      ((DFunLike.congr_fun c.compatible b).symm.trans hb))
    change b.val=MulAut.conj (WeylFrame.planeReflection (F := F)) at he
    have hm : MulAut.conj (WeylFrame.planeReflection (F := F)) ∈ E.middle ⊓ inner F :=
      ⟨he ▸ b.property,⟨_,rfl⟩⟩
    obtain ⟨g,hg,hg'⟩ := E.middle_inner.le hm
    exact WeylFrame.planeReflection_not_mem
      ((SourceExtension.inner_injective (F := F) hg') ▸ hg.1)
  · exact c.weylProduct_four_eq_one hF hn ho hcard
  · exact model_weylProduct_four


end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
