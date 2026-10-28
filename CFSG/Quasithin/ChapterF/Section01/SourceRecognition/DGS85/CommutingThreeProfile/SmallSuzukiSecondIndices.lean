module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiThreePathExchange
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiElementaryPathCard

/-!
# The two binary second indices on the original small-Suzuki path

The moved-neighbor commutator forces a nontrivial image in the actual
linear quotient. The elementary local-index bound is two, so this image
has order two. The same original three-path transporter supplies the
opposite index. No positive Suzuki parameter or complement is needed.
-/

public noncomputable section
open Subgroup SimpleGraph
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Both literal second indices equal two, derived from the nonzero source
intersection commutator and the binary quotient markings. -/
theorem source_small_suzuki_second_indices
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (hq : Nat.card k = 2)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    {z w c : Vertex (reducedFamily L S)}
    (hyz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hwz : (graph (reducedFamily L S)).Adj w z)
    (hwc : (graph (reducedFamily L S)).Adj w c)
    (hzn : z ≠ base (reducedFamily L S) (!i))
    (hwy : w ≠ base (reducedFamily L S) i) (hcz : c ≠ z)
    (hbranch : ⁅V (reducedFamily L S) w 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) i),
      V (reducedFamily L S) (base (reducedFamily L S) i) 1⁆ ≠ ⊥) :
    let F := reducedFamily L S
    (Q F (base F (!i))).relIndex (V F w 1 ⊓ Q F (base F i)) = Nat.card k ∧
      (Q F c).relIndex (V F (base F i) 1 ⊓ Q F w) = Nat.card k := by
  let F := reducedFamily L S
  let m := base F (!i)
  let y := base F i
  let W := V F w 1 ⊓ Q F y
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let := V_elementary F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb w
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    (inclusion (show W ≤ V F w 1 from inf_le_left)) (inclusion_injective _)
  have hym : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hWm : W ≤ stabilizer F m := inf_le_right.trans
    (((source_Z_Q_U (reduced_triple h) y).2.trans (ballKernel_one_le_edge F hym)).trans inf_le_right)
  let : Finite W := Finite.of_injective (inclusion hWm) (inclusion_injective _)
  have hi := source_small_suzuki_elementary_local_index h (!i) eLin
    (by cases i <;> exact eSuz) hq m W hWm
  change (Q F m).relIndex W ≤ 2 at hi
  have hmove := source_small_suzuki_intersection_moves_other_center h i hb eSuz T hT
    hwz hyz hzn hbranch
  have hi1 : (Q F m).relIndex W ≠ 1 := by
    intro he
    have hWQ : W ≤ Q F m := relIndex_eq_one.mp he
    apply hmove
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact hWQ.trans (le_centralizer_iff.mp
      (Z_centralizes_Q F m (source_Z_Q_U (reduced_triple h) m).1))
  have hi0 : (Q F m).relIndex W ≠ 0 := index_ne_zero_of_finite
  have hiW : (Q F m).relIndex W = Nat.card k := by omega
  exact ⟨hiW,(source_small_suzuki_second_index_exchange h i eSuz eLin T hT
    hyz hwz hwc hzn hwy hcz).trans hiW⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
