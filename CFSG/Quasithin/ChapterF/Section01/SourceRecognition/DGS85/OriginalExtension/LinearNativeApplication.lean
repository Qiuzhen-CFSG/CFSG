module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.LinearNative
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.LinearApplication

/-!
# The prepared linear consumer from a marked reduced row

Apply native linear restoration to the literal prepared pair ![L,R] and
S=O₂(N_G(L)∩H). Solvable residuals derive the right-factor marking from the
supplied perfectness of R. Native lifts and Sylow conjugacy discharge the
kernel and normalizer premises of the existing original endpoint core
calculation, yielding O₂(RS)=O₂(R) and S≤R for the original chosen R.

Source: DGS, *Groups and Graphs* (1985), (15.2), pp.226–228, and
Aschbacher–Smith F.1.12, pp.263–264. Only the marked nonbinary reduced
linear comparison remains a recognition input; the other source rows and
exhaustive recognition belong to the source assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Global.Preparation T L H A B R)
  (h : Input κ T L W n) (hTH : (T : Subgroup G) ≤ H)
  (F : Type) [Field F] [Finite F] [CharP F 2]
  {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2^m) (i : Bool)
  (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) (LinearNative.amalgam F i))

include d h hTH hm hF e
/-- The nonbinary linear reduced comparison restores the SAME source S and R.
The perfectness already supplied for selected R derives its local-factor
marking; native lifts discharge kernel invariance and endpoint normalizers. -/
theorem linear_original_core_and_containment_of_reduced_iso (hp : Group.IsPerfect R) :
    (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ Global.sourceS L H ≤ R := by
  let hf := d.hypothesisF11 h hTH
  let c := LinearNative.reducedCompletion F i e
  have hk : PreservesCompletionKernel hf c := LinearNative.reduced_preserved F hf i e hF hm
  have ho := LinearNative.reduced_overlap F i e
  have hN := LinearNative.reduced_normalizer F i e hF (by omega : 0<m)
  have hR := LinearNative.right_factor_marking F hf i e hF hm hp
  exact ⟨linear_original_right_core d h hTH F (by omega) hF i c hk ho hN hR,
    linear_original_sourceS_le_right d h hTH F (by omega) hF i c hk ho hN hR⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
