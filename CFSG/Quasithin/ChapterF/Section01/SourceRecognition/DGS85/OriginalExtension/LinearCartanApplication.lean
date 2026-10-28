module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.CartanRestoration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.UniversalFaithfulness
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.LinearApplication

/-!
# Linear F.1.12 application from the local Cartan calculation

Recognize the actual reduced apartment quotient as PSL₃(F), retaining its
right local-factor image. The geometric descent theorem proves preservation
of that quotient kernel by the original Borel, and separation proves the
whole overlap. The constructed original endpoint embedding then gives both
O₂(RS) = O₂(R) and containment of the same original S = O₂(N_G(L) ∩ H) in R.

Source: DGS (1985), (15.2), pp.226--228, applied to Aschbacher--Smith,
F.1.12, printed p.264. The original preparation and selected R are retained.
The local Cartan fixed-neighbor calculation, the actual reduced recognition
isomorphism and its local normalizer/factor markings remain explicit
earlier-source inputs. Apartment preservation, kernel invariance and
faithfulness of the actual universal tree are proved.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open SuzukiContainment Chapter6.Source.RankOneGeneric
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open Theory.GroupTheory.WeakBNPair.RegularTree
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Global.Preparation T L H A B R)
  (h : Input κ T L W n) (hTH : (T : Subgroup G) ≤ H)
  (F : Type) [Field F] [Finite F] [CharP F 2]
  {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m) (point : Bool)
  (Apt : Set (SourceVertex (reducedAmalgam ![L,R] (Global.sourceS L H)))) (r : ℕ)
  (hsep : Separated
    (sourceRelation (reducedAmalgam ![L,R] (Global.sourceS L H)) Apt r)
    (sourceGraph (reducedAmalgam ![L,R] (Global.sourceS L H))) (2*r)) (hr : 1 < r)
  (hdeg : TwoNeighborsIn (sourceGraph (reducedAmalgam ![L,R] (Global.sourceS L H))) Apt)
  (hline : NoBranchingIn (sourceGraph (reducedAmalgam ![L,R] (Global.sourceS L H))) Apt)
  (hconn : ((sourceGraph (reducedAmalgam ![L,R] (Global.sourceS L H))).induce Apt).Preconnected)
  (hunique : ApartmentsUnique (X := (reducedAmalgam ![L,R] (Global.sourceS L H)).Universal)
    (sourceGraph (reducedAmalgam ![L,R] (Global.sourceS L H))) Apt (r+1))
  (htrans : BasedPathTransitive (X := (reducedAmalgam ![L,R] (Global.sourceS L H)).Universal)
    (sourceGraph (reducedAmalgam ![L,R] (Global.sourceS L H))) (r+1))
  {w : SourceVertex (reducedAmalgam ![L,R] (Global.sourceS L H))}
  (p : (sourceGraph (reducedAmalgam ![L,R] (Global.sourceS L H))).Walk
    (Subgroup.CosetGeometry.base
      (Universal.cosetFamily (reducedAmalgam ![L,R] (Global.sourceS L H))) false) w)
  (hp : p.IsPath) (hlen : p.length = r+1) (hpT : ∀ v ∈ p.support, v ∈ Apt)
  (C : Subgroup (reducedAmalgam ![L,R] (Global.sourceS L H)).Universal)
  (hC : ∀ g, g ∈ C ↔ ∀ k ≤ p.length, g • p.getVert k = p.getVert k)
  (hthin : NoBranchingIn (sourceGraph (reducedAmalgam ![L,R] (Global.sourceS L H)))
    {v | ∀ g ∈ C, g • v = v})
  (e : QuotientGroup (reducedAmalgam ![L,R] (Global.sourceS L H)) Apt r ≃* PSL(3,F))
  (hnormalizer : ∀ i, normalizer
    ((completionEndpoint (recognizedReducedCompletion Apt r hsep hr (reduced_universal_core_eq_bot (d.hypothesisF11 h hTH)) e) i).range :
      Set PSL(3,F)) =
        (completionEndpoint (recognizedReducedCompletion Apt r hsep hr (reduced_universal_core_eq_bot (d.hypothesisF11 h hTH)) e) i).range)
  (hR : (R.subgroupOf (parabolic ![L,R]
    (reducedSylow ![L,R] (Global.sourceS L H)) 1)).map
      (recognizedReducedCompletion Apt r hsep hr (reduced_universal_core_eq_bot (d.hypothesisF11 h hTH)) e).right =
        Matrix.PSL3.LinearThree.OuterExtensions.localFactor F point)

include d h hTH hm hF hnormalizer hR hdeg hline hconn hunique htrans hp hlen hpT hC hthin

/-- F.1.12 on the same selected R and the same original source S. The input
is recognition of the actual geometric reduced quotient; algebraic kernel
invariance, original endpoint embeddings and full overlap are all constructed. -/
theorem linear_original_core_and_containment_of_thin_cartan :
    (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ Global.sourceS L H ≤ R := by
  let c := recognizedReducedCompletion Apt r hsep hr (reduced_universal_core_eq_bot (d.hypothesisF11 h hTH)) e
  have hk : PreservesCompletionKernel (d.hypothesisF11 h hTH) c :=
    recognizedReducedCompletion_preserved_of_thin_cartan (d.hypothesisF11 h hTH)
      Apt r hsep hr (reduced_universal_core_eq_bot (d.hypothesisF11 h hTH)) hdeg hline hconn hunique htrans p hp hlen hpT C hC hthin e
  have ho : c.left.range ⊓ c.right.range = c.middle.range :=
    recognizedReducedCompletion_overlap Apt r hsep hr (reduced_universal_core_eq_bot (d.hypothesisF11 h hTH)) e
  exact ⟨linear_original_right_core d h hTH F hm hF point c hk ho hnormalizer hR,
    linear_original_sourceS_le_right d h hTH F hm hF point c hk ho hnormalizer hR⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
