module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightReflectionChange

/-!
# The chosen original root is one of the same half-path roots

The supported half-path and the chosen reflection path follow the same
oriented embedded line. Their vertices, pointwise fixers and actual roots
agree. Thus the original root lies in the literal selected half-path actor.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Subgroup.CosetGeometry Theory.GroupTheory.WeakBNPair.RegularTree
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootHalfActor
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "F" => Universal.cosetFamily A

/-- The original eight reflection root belongs to the same selected actor;
there is no assumed comparison of roots or of quotient images. -/
theorem original_reflection_root_le_half_actor
    (c : CompatibleCartans L (reducedSylow L S)) (d : SixPathSmallActorGeometry c)
    {a b : SourceVertex A} (p : (sourceGraph A).Walk a b) (hp:p.IsPath) (hl:p.length=12)
    (hm:p.getVert 6=base F true) (hn:p.getVert 7=base F false)
    (hs:∀ z∈p.support,z∈cartanApartment A (reflectionGroup c d.reflection)) :
    pathRoot (X := (A).Universal)
      (reflectionPath c d.reflection d.fixes d.moves d.normalizes 6 (by decide) true).walk≤
        halfPathActor (X := (A).Universal) p 6 := by
  let r := reflectionPath c d.reflection d.fixes d.moves d.normalizes 6 (by decide) true
  have ht := (Universal.cosetGraph_isTree A
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).isAcyclic
  have hab : (sourceGraph A).Adj (base F true) (base F false) :=
    ⟨by change true≠false;decide,incident_base _ _ _⟩
  let l := (localMoversTrack ht ⟨source_action A⟩ hab (d.fixes true) (d.fixes false)
    (d.moves true) (d.moves false)).toLine
  have hcoords : ∀ k≤(p.drop 6).length,(p.drop 6).getVert k=l.vertex (k:ℤ) := by
    apply path_getVert_eq_line ht l (p.drop 6) (hp.drop 6)
    · simpa only [l,localMoversTrack_zero] using hm
    · simpa only [Walk.drop_getVert,l,Track.toLine,localMoversTrack_one] using hn
    · intro z hz
      have hz' : z∈p.support := by
        rw [Walk.drop_support_eq_support_drop_min] at hz
        exact List.mem_of_mem_drop hz
      have hz'' := hs z hz'
      rw [reflectionApartment_eq_oriented_line c d.reflection d.fixes d.squares d.normalizes true] at hz''
      exact hz''
  have he := pathRoot_map_conj (X := (A).Universal) (p.drop 6) r.walk.reverse 1
    (by rw [Walk.drop_length,hl,Walk.length_reverse,r.length_eq]) (by
      intro k hk
      rw [one_smul,hcoords k hk]
      exact (reflectionPath_reverse_getVert c d.reflection d.fixes d.moves d.squares
        d.normalizes 6 (by decide) true k (by simpa only [Walk.drop_length,hl] using hk)).symm)
  have hroot : pathRoot (X := (A).Universal) (p.drop 6)=pathRoot r.walk := by
    have hc : (MulAut.conj (1 : (A).Universal)).toMonoidHom=MonoidHom.id _ := by
      ext x
      simp
    simpa only [hc,Subgroup.map_id,pathRoot_reverse] using he
  rw [←hroot]
  exact le_sup_left
end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootHalfActor
