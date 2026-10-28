module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.CartanGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.GeometricRestoration

/-!
# Restoring original endpoints from the local Cartan calculation

The reduced path and its actual pointwise stabilizer are marked on the
universal coset tree. Apartment uniqueness and reduced path transitivity,
with no branching among Cartan-fixed neighbors, prove preservation of the
apartment family by every element of the original full Borel. Descent and
recognition then supply both original endpoint maps, restricting to the
same quotient map on the reduced endpoints.

Source: DGS, *Groups and Graphs* (1985), (15.2), printed pp.226--228.
This is the regular no-branching case. The earlier-source apartment data,
its local Cartan fixed-neighbor calculation and genuine finite recognition
remain explicit. The former global apartment-preservation premise is proved.
The source small-field exceptions, permissible Aut⁰ actions and Chapter 15's
exceptional restoration are not asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open SuzukiContainment
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (h : HypothesisF11 L S)
  (T : Set (SourceVertex (reducedAmalgam L S))) (n : ℕ)
  (hsep : Separated (sourceRelation (reducedAmalgam L S) T n)
    (sourceGraph (reducedAmalgam L S)) (2*n)) (hn : 1 < n)
  (hcore : ((Universal.left (reducedAmalgam L S)).range ⊓
    (Universal.right (reducedAmalgam L S)).range).normalCore = ⊥)
  (hdeg : TwoNeighborsIn (sourceGraph (reducedAmalgam L S)) T)
  (hline : NoBranchingIn (sourceGraph (reducedAmalgam L S)) T)
  (hconn : ((sourceGraph (reducedAmalgam L S)).induce T).Preconnected)
  (hunique : ApartmentsUnique (X := (reducedAmalgam L S).Universal)
    (sourceGraph (reducedAmalgam L S)) T (n+1))
  (htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
    (sourceGraph (reducedAmalgam L S)) (n+1))
  {w : SourceVertex (reducedAmalgam L S)}
  (p : (sourceGraph (reducedAmalgam L S)).Walk
    (Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L S)) false) w)
  (hp : p.IsPath) (hlen : p.length = n+1) (hpT : ∀ v ∈ p.support, v ∈ T)
  (C : Subgroup (reducedAmalgam L S).Universal)
  (hC : ∀ g, g ∈ C ↔ ∀ k ≤ p.length, g • p.getVert k = p.getVert k)
  (hthin : NoBranchingIn (sourceGraph (reducedAmalgam L S))
    {v | ∀ g ∈ C, g • v = v})

include hdeg hline hconn hunique htrans hp hlen hpT hC hthin
/-- Every element of the original full Borel preserves the reduced apartment
family. The local fixed-neighbor input replaces the former global premise. -/
theorem original_apartment_preserved_of_thin_cartan :
    ∀ b : commonBorel L S, ∃ t : (reducedAmalgam L S).Universal,
      ∀ v ∈ T, ∃ z ∈ T,
        ApartmentAction.treeAutomorphism (reducedOverlapAction h)
          (geometricReducedCompletion T n hsep hn hcore) b v = t • z := by
  intro b
  exact CartanGeometry.apartment_image_of_thin_path_stabilizer
    (Universal.cosetGraph_isTree (reducedAmalgam L S)
      (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1)))
    (source_action (reducedAmalgam L S)) hdeg hline hconn (by omega) hunique htrans
    p hp hlen hpT C hC hthin
    (ApartmentAction.universalAction (reducedOverlapAction h)
      (geometricReducedCompletion T n hsep hn hcore) b)
    (ApartmentAction.treeAutomorphism (reducedOverlapAction h)
      (geometricReducedCompletion T n hsep hn hcore) b)
    (ApartmentAction.treeAutomorphism_smul (reducedOverlapAction h)
      (geometricReducedCompletion T n hsep hn hcore) b)
    (ApartmentAction.treeAutomorphism_base (reducedOverlapAction h)
      (geometricReducedCompletion T n hsep hn hcore) b false)

/-- The actual reduced geometric quotient kernel is invariant under the whole
original Borel, with no independent kernel or apartment-preservation premise. -/
theorem geometricReducedCompletion_preserved_of_thin_cartan :
    PreservesCompletionKernel h (geometricReducedCompletion T n hsep hn hcore) :=
  geometricReducedCompletion_preserved h T n hsep hn hcore
    (original_apartment_preserved_of_thin_cartan h T n hsep hn hcore
      hdeg hline hconn hunique htrans p hp hlen hpT C hC hthin)

variable {X : Type*} [Group X]
  (e : QuotientGroup (reducedAmalgam L S) T n ≃* X)

/-- Recognition uses the same quotient and both original endpoint restrictions. -/
theorem recognizedReducedCompletion_preserved_of_thin_cartan :
    PreservesCompletionKernel h (recognizedReducedCompletion T n hsep hn hcore e) :=
  ApartmentAction.preservesCompletionKernel_mapEquiv (reducedOverlapAction h) _ e
    (geometricReducedCompletion_preserved_of_thin_cartan h T n hsep hn hcore
      hdeg hline hconn hunique htrans p hp hlen hpT C hC hthin)

variable (hnormalizer : ∀ i, normalizer
    ((completionEndpoint (recognizedReducedCompletion T n hsep hn hcore e) i).range : Set X) =
      (completionEndpoint (recognizedReducedCompletion T n hsep hn hcore e) i).range)

include hnormalizer in
/-- Conditional DGS 15.2 restoration in the local no-branching case: both
endpoint inclusions and the full original Borel use the same constructed action. -/
theorem exists_original_completion_of_thin_cartan :
    ∃ d : FaithfulCompletion (originalAmalgam L S)
      (G := automorphismExtension h (recognizedReducedCompletion T n hsep hn hcore e)
        (recognizedReducedCompletion_preserved_of_thin_cartan h T n hsep hn hcore
          hdeg hline hconn hunique htrans p hp hlen hpT C hC hthin e)),
      (∀ b : commonBorel L S, (d.middle b : MulAut X) =
        completionAction h (recognizedReducedCompletion T n hsep hn hcore e)
          (recognizedReducedCompletion_preserved_of_thin_cartan h T n hsep hn hcore
            hdeg hline hconn hunique htrans p hp hlen hpT C hC hthin e) b) ∧
      (∀ x : parabolic L (reducedSylow L S) 0,
        (d.left (inclusion (reduced_parabolic_le h 0) x) : MulAut X) =
          MulAut.conj (e (quotientMap (reducedAmalgam L S) T n
            (Universal.left (reducedAmalgam L S) x)))) ∧
      (∀ x : parabolic L (reducedSylow L S) 1,
        (d.right (inclusion (reduced_parabolic_le h 1) x) : MulAut X) =
          MulAut.conj (e (quotientMap (reducedAmalgam L S) T n
            (Universal.right (reducedAmalgam L S) x)))) :=
  exists_original_completion h (recognizedReducedCompletion T n hsep hn hcore e)
    (recognizedReducedCompletion_preserved_of_thin_cartan h T n hsep hn hcore
      hdeg hline hconn hunique htrans p hp hlen hpT C hC hthin e)
    (recognizedReducedCompletion_overlap T n hsep hn hcore e) hnormalizer

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
