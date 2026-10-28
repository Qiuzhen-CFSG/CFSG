module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.Completion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.LinearCore

/-!
# Linear containment from a reduced completion marking

The DGS completion construction supplies an injective map of the original
right parabolic into Aut(PSL₃(F)), carrying its same selected local factor R
onto the native local factor's inner image. The existing linear extension
core calculation gives O₂(RS) = O₂(R), and the original normalized-Borel
factorization gives S ≤ R. Here S is literally O₂(N_G(L) ∩ H).

These are conditional applications of DGS (15.2), printed pp.226--228, to
Aschbacher--Smith F.1.12, printed p.264. Only the reduced completion and its
kernel invariance, endpoint normalizers and local-factor marking are inputs;
the original endpoint embedding is constructed. Recognition and geometric
kernel invariance still belong to the full source argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open SuzukiContainment Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Global.Preparation T L H A B R)
  (h : Input κ T L W n) (hTH : (T : Subgroup G) ≤ H)
  (F : Type) [Field F] [Finite F] [CharP F 2]
  {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
  (point : Bool)
  (c : FaithfulCompletion (reducedAmalgam ![L,R] (Global.sourceS L H))
    (G := PSL(3,F)))
  (hk : PreservesCompletionKernel (d.hypothesisF11 h hTH) c)
  (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
  (hnormalizer : ∀ i, normalizer ((completionEndpoint c i).range : Set PSL(3,F)) =
    (completionEndpoint c i).range)
  (hR : (R.subgroupOf (parabolic ![L,R]
    (reducedSylow ![L,R] (Global.sourceS L H)) 1)).map c.right =
      Matrix.PSL3.LinearThree.OuterExtensions.localFactor F point)

include d h hTH hm hF hk hoverlap hnormalizer hR

/-- Transfer the reduced right-factor marking to the original endpoint and
apply its native linear core calculation. -/
theorem linear_original_right_core :
    (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 := by
  obtain ⟨f,hf,hmark⟩ := exists_original_endpoint_local_marking
    (d.hypothesisF11 h hTH) c hk hoverlap hnormalizer 1
    (Matrix.PSL3.LinearThree.OuterExtensions.localFactor F point) hR
  exact d.linear_extension_right_core F hm hF point f hf hmark

/-- The same original source S is contained in the selected R. The completion
premises concern the reduced marked pair; an original embedding is constructed. -/
theorem linear_original_sourceS_le_right : Global.sourceS L H ≤ R := by
  obtain ⟨f,hf,hmark⟩ := exists_original_endpoint_local_marking
    (d.hypothesisF11 h hTH) c hk hoverlap hnormalizer 1
    (Matrix.PSL3.LinearThree.OuterExtensions.localFactor F point) hR
  exact d.sourceS_le_right_of_linear_extension h hTH F hm hF point f hf hmark

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
