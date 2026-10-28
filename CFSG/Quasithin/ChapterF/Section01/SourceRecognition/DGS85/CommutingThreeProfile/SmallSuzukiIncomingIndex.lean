module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiSecondIndices
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSylowNeighbors

/-!
# Incoming binary second index

A single original Suzuki-star conjugator carries the selected outgoing
neighbor to the marked linear vertex. The actual moved-center theorem
and the binary elementary local bound give index two there; the same
conjugator transports that index back to the incoming intersection.
-/

public noncomputable section
open Subgroup SimpleGraph
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

theorem source_small_suzuki_incoming_second_index
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (hq : Nat.card k = 2)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    {x z : Vertex (reducedFamily L S)}
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    (hyz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hzn : z ≠ base (reducedFamily L S) (!i))
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) i),
      V (reducedFamily L S) (base (reducedFamily L S) i) 1⁆ ≠ ⊥) :
    (Q (reducedFamily L S) z).relIndex
      (V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k := by
  let F := reducedFamily L S
  let m := base F (!i)
  let y := base F i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hym : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨g,hg,hgz⟩ := star_locally_transitive h i hyz hym
  have hgy : g • y = y := star_le_stabilizer i hg
  have hgm : g • m ≠ m := fun he => hzn ((MulAction.injective g) (hgz.trans he.symm))
  have hadj {u v : Vertex F} (huv : (graph F).Adj u v) :
      (graph F).Adj (g • u) (g • v) :=
    (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr huv
  have hygm : (graph F).Adj y (g • m) := by simpa only [hgy] using hadj hym
  have hbranch' : ⁅V F (g • x) 1 ⊓ Q F y,V F y 1⁆ ≠ ⊥ := by
    have hh := (map_eq_bot_iff_of_injective
      (⁅V F x 1 ⊓ Q F y,V F y 1⁆ : Subgroup (G₀ L S)) (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).not.mpr hbranch
    rwa [map_commutator,Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      ←V_translate F,←Q_translate F,←V_translate F,hgy] at hh
  have hmove := source_small_suzuki_intersection_moves_other_center h i hb eSuz T hT
    (hadj hxm) hygm hgm hbranch'
  let W := V F (g • x) 1 ⊓ Q F y
  let := V_elementary F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb (g • x)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    (inclusion (show W ≤ V F (g • x) 1 from inf_le_left)) (inclusion_injective _)
  have hWm : W ≤ stabilizer F m := inf_le_right.trans
    (((source_Z_Q_U (reduced_triple h) y).2.trans (ballKernel_one_le_edge F hym)).trans inf_le_right)
  let : Finite W := Finite.of_injective (inclusion hWm) (inclusion_injective _)
  have hu := source_small_suzuki_elementary_local_index h (!i) eLin
    (by cases i <;> exact eSuz) hq m W hWm
  change (Q F m).relIndex W ≤ 2 at hu
  have hi1 : (Q F m).relIndex W ≠ 1 := by
    intro he
    apply hmove
    exact commutator_eq_bot_iff_le_centralizer.mpr
      ((relIndex_eq_one.mp he).trans (le_centralizer_iff.mp
        (Z_centralizes_Q F m (source_Z_Q_U (reduced_triple h) m).1)))
  have hi0 : (Q F m).relIndex W ≠ 0 := index_ne_zero_of_finite
  have hi' : (Q F m).relIndex (V F (g • x) 1 ⊓ Q F y) = Nat.card k := by
    change (Q F m).relIndex W = Nat.card k
    omega
  have he := relIndex_map_map_of_injective (Q F z) (V F x 1 ⊓ Q F y)
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    ←V_translate F,←Q_translate F,←Q_translate F,hgy,hgz] at he
  exact he.symm.trans hi'

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
