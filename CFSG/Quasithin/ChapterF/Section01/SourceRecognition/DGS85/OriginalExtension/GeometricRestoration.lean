module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.ApartmentAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.RestoredCompletion

/-!
# Original completion from the recognized apartment quotient

The universal map commutes with a genuine recognition isomorphism of the
geometric quotient. Therefore the geometric kernel-preservation theorem passes
to that recognized completion. Separation supplies its exact full overlap.
Applying the original extension construction now produces a faithful original
completion whose two restrictions are the literal geometric quotient map
followed by recognition and inner conjugation. The original Borel map is kept.

Source: DGS, *Groups and Graphs* (1985), (15.2), printed pp.226--228.
The input still includes apartment preservation by original actors and a
recognition isomorphism; it does not assume an original completion marking.
Permissible Aut⁰(X) and the exceptional extension cases remain source work.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
namespace ApartmentAction
universe u
variable {L B R : Type u} [Group L] [Group B] [Group R]
  {X Y K : Type*} [Group X] [Group Y] [Group K]
  {α : RankTwoAmalgam L B R}
  (a : K →* Iso α α) (c : FaithfulCompletion α (G := X)) (e : X ≃* Y)

/-- Recognition transports the same universal quotient map. -/
theorem lift_mapEquiv : Universal.lift α (c.mapEquiv e) =
    e.toMonoidHom.comp (Universal.lift α c) := by
  apply Monoid.PushoutI.hom_ext_nonempty
  intro i
  cases i <;> ext x
  · change L at x
    change Universal.lift α (c.mapEquiv e) (Universal.left α x) =
      e (Universal.lift α c (Universal.left α x))
    rw [Universal.lift_left, Universal.lift_left]
    rfl
  · change R at x
    change Universal.lift α (c.mapEquiv e) (Universal.right α x) =
      e (Universal.lift α c (Universal.right α x))
    rw [Universal.lift_right, Universal.lift_right]
    rfl

/-- Actual marked recognition preserves kernel invariance. No new invariance
premise on the recognized model is required. -/
theorem preservesCompletionKernel_mapEquiv
    (hk : CompletionAction.PreservesCompletionKernel a c) :
    CompletionAction.PreservesCompletionKernel a (c.mapEquiv e) := by
  intro b x hx
  have hx' : x ∈ (Universal.lift α c).ker := by
    apply e.injective
    change e (Universal.lift α c x) = e 1
    rw [map_one]
    change Universal.lift α (c.mapEquiv e) x = 1 at hx
    rw [lift_mapEquiv] at hx
    exact hx
  have hh := hk b hx'
  change Universal.lift α ((c.comapIso (a b)).mapEquiv e) x = 1
  rw [lift_mapEquiv]
  change e (Universal.lift α (c.comapIso (a b)) x) = 1
  rw [show Universal.lift α (c.comapIso (a b)) x = 1 from hh, map_one]

end ApartmentAction
open SuzukiContainment
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open Theory.GroupTheory.WeakBNPair.RegularTree

variable {G : Type*} [Group G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (h : HypothesisF11 L S)
  (T : Set (SourceVertex (reducedAmalgam L S))) (n : ℕ)
  (hsep : Separated (sourceRelation (reducedAmalgam L S) T n)
    (sourceGraph (reducedAmalgam L S)) (2*n)) (hn : 1 < n)
  (hcore : ((Universal.left (reducedAmalgam L S)).range ⊓
    (Universal.right (reducedAmalgam L S)).range).normalCore = ⊥)

/-- The marked reduced completion is the actual apartment quotient. -/
abbrev geometricReducedCompletion : FaithfulCompletion (reducedAmalgam L S)
    (G := QuotientGroup (reducedAmalgam L S) T n) :=
  quotientCompletion (reducedAmalgam L S) T n (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1)) hsep hn hcore

variable
  (hap : ∀ b : commonBorel L S, ∃ t : (reducedAmalgam L S).Universal,
    ∀ v ∈ T, ∃ w ∈ T,
      ApartmentAction.treeAutomorphism (reducedOverlapAction h)
        (geometricReducedCompletion T n hsep hn hcore) b v = t • w)

include hap in
/-- DGS 15.2's geometric descent on the literal original Borel action. -/
theorem geometricReducedCompletion_preserved :
    PreservesCompletionKernel h (geometricReducedCompletion T n hsep hn hcore) :=
  ApartmentAction.preserves_geometricCompletion (reducedOverlapAction h)
    T n (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1)) hsep hn hcore hap

variable {X : Type*} [Group X]
  (e : QuotientGroup (reducedAmalgam L S) T n ≃* X)

/-- Both recognized endpoint maps use the same genuine quotient isomorphism. -/
abbrev recognizedReducedCompletion :=
  (geometricReducedCompletion T n hsep hn hcore).mapEquiv e

include hap in
theorem recognizedReducedCompletion_preserved :
    PreservesCompletionKernel h (recognizedReducedCompletion T n hsep hn hcore e) :=
  ApartmentAction.preservesCompletionKernel_mapEquiv (reducedOverlapAction h) _ e
    (geometricReducedCompletion_preserved h T n hsep hn hcore hap)

theorem recognizedReducedCompletion_overlap :
    (recognizedReducedCompletion T n hsep hn hcore e).left.range ⊓
      (recognizedReducedCompletion T n hsep hn hcore e).right.range =
        (recognizedReducedCompletion T n hsep hn hcore e).middle.range :=
  FaithfulCompletion.mapEquiv_overlap _ e
    (quotient_overlap (reducedAmalgam L S) T n
      (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1)) hsep hn)

variable (hnormalizer : ∀ i, normalizer
    ((completionEndpoint (recognizedReducedCompletion T n hsep hn hcore e) i).range : Set X) =
      (completionEndpoint (recognizedReducedCompletion T n hsep hn hcore e) i).range)

include hnormalizer in
/-- Literal original restoration from a recognized apartment quotient. Kernel
invariance and full overlap are proved from the geometry. Both reduced
restrictions are expressed using the original quotient map and recognition e. -/
theorem exists_original_completion_of_apartments :
    ∃ d : FaithfulCompletion (originalAmalgam L S)
      (G := automorphismExtension h (recognizedReducedCompletion T n hsep hn hcore e)
        (recognizedReducedCompletion_preserved h T n hsep hn hcore hap e)),
      (∀ b : commonBorel L S, (d.middle b : MulAut X) =
        completionAction h (recognizedReducedCompletion T n hsep hn hcore e)
          (recognizedReducedCompletion_preserved h T n hsep hn hcore hap e) b) ∧
      (∀ x : parabolic L (reducedSylow L S) 0,
        (d.left (inclusion (reduced_parabolic_le h 0) x) : MulAut X) =
          MulAut.conj (e (quotientMap (reducedAmalgam L S) T n
            (Universal.left (reducedAmalgam L S) x)))) ∧
      (∀ x : parabolic L (reducedSylow L S) 1,
        (d.right (inclusion (reduced_parabolic_le h 1) x) : MulAut X) =
          MulAut.conj (e (quotientMap (reducedAmalgam L S) T n
            (Universal.right (reducedAmalgam L S) x)))) :=
  exists_original_completion h (recognizedReducedCompletion T n hsep hn hcore e)
    (recognizedReducedCompletion_preserved h T n hsep hn hcore hap e)
    (recognizedReducedCompletion_overlap T n hsep hn hcore e) hnormalizer

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
