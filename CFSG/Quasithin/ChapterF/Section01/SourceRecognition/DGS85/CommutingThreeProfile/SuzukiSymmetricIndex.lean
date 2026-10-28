module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSpanFixedIndex
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSpanFixedIndex

/-!
# The reversed Suzuki span index on an arbitrary incoming edge

The first index of (12.3)(a) measures the image of V_x at y. Move the
common linear neighbor to the base by the actual Suzuki star, then use
the linear neighbor exchange to interchange x and y. Conjugation
invariance gives the reversed index [V_y : V_y intersect Q_x] = q,
including its image in the original completion.

The implementation import reuses this family's proved private neighbor
exchange without changing its public boundary. The actual centralizer
case in SuzukiTrappedCentralizer uses the reversed index to bound an
intersection with the remote core; no additional critical pair in the
reverse orientation is assumed.

Source: DGS85, Groups and Graphs (1985), (12.3)(a) and the displayed
(*) in (12.7), printed pp.179 and184--185. This is the nonbinary case.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Reverse the first source index by the literal linear neighbor exchange. -/
theorem source_suzuki_reverse_first_index
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {a x m : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x m)
    (hym : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) m)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) m ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    (Q F x).relIndex (V F (base F i) 1) = 2^(2*n+1) ∧
      ((Q F x).map (G₀ L S).subtype).relIndex
        ((V F (base F i) 1).map (G₀ L S).subtype) = 2^(2*n+1) := by
  let F := reducedFamily L S
  let y := base F i
  let z := base F (!i)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hi : (Q F y).relIndex (V F x 1) = 2^(2*n+1) := by
    simpa only [inf_relIndex_left] using
      (source_suzuki_first_index h i hb hc hxa hxm hym hn eSuz eLin R hR).1
  have hne : x ≠ y := by
    intro he
    have hZx : Z F a ≤ V F x 1 := Z_neighbor_le_V F hxa
    have hV := V_le_Q F (reduced_triple h).generate
      (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb x
    rw [he] at hV hZx
    exact hc.2 (hZx.trans (hV.trans (source_Z_Q_U (reduced_triple h) y).2))
  have hyz : (graph F).Adj y z :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨g,hg,hgm⟩ := star_locally_transitive h i hym hyz
  have hgy : g • y = y := star_le_stabilizer i hg
  have hzx : (graph F).Adj z (g • x) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hxm.symm
    change (graph F).Adj (g • m) (g • x) at hh
    rwa [hgm] at hh
  have hne' : g • x ≠ y := fun he => hne ((MulAction.injective g) (he.trans hgy.symm))
  obtain ⟨u,_,hux,huy⟩ := linear_neighbor_swap h (!i) eLin hzx hyz.symm hne'
  let t := g⁻¹ * u * g
  have htx : t • x = y := by
    dsimp only [t]
    rw [mul_smul,mul_smul,hux,inv_smul_eq_iff]
    exact hgy.symm
  have hty : t • y = x := by
    dsimp only [t]
    rw [mul_smul,mul_smul,hgy,huy,inv_smul_smul]
  have he := relIndex_map_map_of_injective (Q F y) (V F x 1)
    (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective
  rw [←Q_translate F,←V_translate F,htx,hty] at he
  have hj := he.trans hi
  exact ⟨hj,(relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective).trans hj⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
