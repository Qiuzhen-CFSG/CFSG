module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.FullEdgeComplements
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.MarkedComplementIndex
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiIntersectionDenominator

/-!
# The nonbinary Suzuki second index in DGS 12.3(a)

Move the middle vertex to the opposite base vertex using the actual
starred action. Construct the odd complement there, move it to fix the
selected neighbor, and conjugate back. Equal full-edge and two-core orders
make the resulting subgroup a complement at the selected linear endpoint.

The marked-quotient supplement then supplies the full linear Sylow image
of V_x intersect Q_y. The Suzuki denominator calculation identifies its
kernel with V_x intersect Q_z, proving the printed second index q. The
field coordinates retain the original/starred quotient representatives,
and the index is also transported through the original completion inclusion.

The common-Sylow markings, shared field parameter, starred containment,
and nonzero movement are explicit source inputs. Both complement choices,
the quotient supplement, the image Sylow, and the required vertex distinction
are proved here. This treats q > 2. SuzukiIndices supplies the first index;
the binary branch and later 12.3--12.9 conclusions remain separate obligations.

Source: DGS85, Groups and Graphs, (12.1)(b,c,e), (12.3)(a), printed pp.178--179.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo Reduction Theory.GroupTheory.AmalgamGraph
open BenderSuzuki.MatrixGroups BenderSuzuki.Converse
namespace ReducedLayer
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Construct the full-edge complement at the selected linear base vertex. -/
theorem source_suzuki_selected_edge_complement
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL2 k)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (T : Sylow 2 (star L S i))
    (hcommon : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    {x m : Vertex (reducedFamily L S)}
    (hxm : (graph (reducedFamily L S)).Adj x m)
    (hym : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) m)
    (hmz : m ≠ base (reducedFamily L S) (!i))
    (hyx : base (reducedFamily L S) i ≠ x) :
    let F := reducedFamily L S
    let E := stabilizer F (base F i) ⊓ stabilizer F (base F (!i))
    ∃ K : Subgroup E, (pCore 2 E).IsComplement' K ∧ Odd (Nat.card K) ∧
      K.map E.subtype ≤ stabilizer F x := by
  let F := reducedFamily L S
  let E := stabilizer F (base F i) ⊓ stabilizer F (base F (!i))
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨a, ha, ham⟩ := star_locally_transitive h i hym hadj
  have hay : a • base F i = base F i := star_le_stabilizer i ha
  have hx' : (graph F).Adj (a • x) (base F (!i)) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F a).map_adj_iff.mpr hxm
    change (graph F).Adj (a • x) (a • m) at hh
    rwa [ham] at hh
  have hxy' : base F i ≠ a • x := by
    intro he
    exact hyx ((MulAction.injective a) (hay.trans he))
  have hz' : (graph F).Adj (base F i) (a • base F (!i)) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F a).map_adj_iff.mpr hadj
    change (graph F).Adj (a • base F i) (a • base F (!i)) at hh
    rwa [hay] at hh
  have hzm' : a • base F (!i) ≠ base F (!i) := by
    intro he
    exact hmz ((MulAction.injective a) (ham.trans he.symm))
  obtain ⟨K₀, hK₀, hodd, _, q, _, hfix, _, _, hc, _⟩ :=
    source_linear_suzuki_edge_complements h i hn eLin eSuz T hcommon hx' hxy' hz' hzm'
  let E₀ := stabilizer F (a • x) ⊓ stabilizer F (base F (!i))
  let C := (K₀.map E₀.subtype).map (MulAut.conj q).toMonoidHom
  let D := C.map (MulAut.conj a⁻¹).toMonoidHom
  have hback (v : Vertex F) (hv : C ≤ stabilizer F (a • v)) : D ≤ stabilizer F v := by
    have hh := map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) hv
    rw [← stabilizer_translate, inv_smul_smul] at hh
    exact hh
  have hDx : D ≤ stabilizer F x := hback x (hfix.trans (inf_le_left.trans inf_le_left))
  have hDy : D ≤ stabilizer F (base F i) := hback (base F i) (by
    rw [hay]
    exact hfix.trans (inf_le_left.trans inf_le_right))
  have hDz : D ≤ stabilizer F (base F (!i)) := hback _ (hfix.trans inf_le_right)
  have hDE : D ≤ E := le_inf hDy hDz
  have hcard : Nat.card D = Nat.card K₀ :=
    (card_map_of_injective (MulAut.conj a⁻¹).injective).trans hc
  have hcomp := source_edge_complement_transfer h hx' hadj K₀ hK₀ D hDE
    (hcard.symm ▸ hodd) hcard
  refine ⟨D.subgroupOf E, hcomp, ?_, ?_⟩
  · rw [Nat.card_congr (subgroupOfEquivOfLe hDE).toEquiv, hcard]
    exact hodd
  · rw [map_subgroupOf_eq_of_le hDE]
    exact hDx

/-- The literal second index in the nonbinary Suzuki branch, with the complement
and its quotient supplement constructed from the source markings. -/
theorem source_suzuki_second_index
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {x m : Vertex (reducedFamily L S)}
    (hxm : (graph (reducedFamily L S)).Adj x m)
    (hym : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) m)
    (hmz : m ≠ base (reducedFamily L S) (!i))
    {n : ℕ} (hn : 0 < n) (hq : Nat.card k = 2 ^ (2 * n + 1))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup n)
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) m ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (hW : V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) i) ≤
      star L S (!i))
    (hmove : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) i),
      Z (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ ≠ ⊥) :
    let F := reducedFamily L S
    let W := V F x 1 ⊓ Q F (base F i)
    let D := V F x 1 ⊓ Q F (base F (!i))
    D ≤ W ∧ D.relIndex W = 2 ^ (2 * n + 1) ∧
      (D.map (G₀ L S).subtype).relIndex (W.map (G₀ L S).subtype) = 2 ^ (2 * n + 1) ∧
      ∃ P : Sylow 2 SL(2,k), ∃ f : W →* Multiplicative k,
        Function.Surjective f ∧ f.ker = D.subgroupOf W ∧
        ∀ w, ((Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 P) (f w) : SL(2,k)) =
          eLin ((originalQuotient h (!i)).symm
            (QuotientGroup.mk' (pCore 2 (star L S (!i))) ⟨w, hW w.property⟩)) := by
  let F := reducedFamily L S
  let W := V F x 1 ⊓ Q F (base F i)
  let D := V F x 1 ⊓ Q F (base F (!i))
  have hadj : (graph F).Adj (base F (!i)) (base F i) :=
    ⟨by change (!i) ≠ i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F (!i) i⟩
  have hyx : base F i ≠ x := by
    intro he
    have hV := V_elementary F (reduced_triple h).generate
      (fun v => (source_Z_Q_U (reduced_triple h) v).1)
      (reduced_kernel_sylow h) hb (base F i)
    have hzV : Z F (base F (!i)) ≤ V F (base F i) 1 :=
      le_iSup_of_le _ (le_iSup_of_le ((mem_ball_one F _ _).mpr (Or.inl hadj.symm)) le_rfl)
    apply hmove
    change ⁅V F x 1 ⊓ Q F (base F i), Z F (base F (!i))⁆ = ⊥
    rw [← he]
    exact bot_unique ((commutator_mono inf_le_left hzV).trans_eq
      (commutator_self_eq_bot_iff.mpr hV.toIsMulCommutative))
  obtain ⟨K, hK, hodd, hKx⟩ := source_suzuki_selected_edge_complement
    h i hn eLin eSuz T hT hxm hym hmz hyx
  obtain ⟨hD, hden, _⟩ := source_suzuki_intersection_denominator
    h i hb hxm hym hmz hn eSuz T R hT hR
  obtain ⟨hindex, _, P, f, hf, hker, hmark⟩ := source_linear_index_of_edge_complement
    h (!i) hadj eLin hW hmove K hK hodd hKx
  have hi : D.relIndex W = 2 ^ (2 * n + 1) := by
    change (V F x 1 ⊓ Q F (base F (!i))).relIndex W = _
    rw [← hden, inf_relIndex_left, hindex, hq]
  refine ⟨le_inf inf_le_left hD, hi, ?_, P, f, hf, ?_, hmark⟩
  · rw [relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective]
    exact hi
  · rw [hker]
    ext w
    exact ⟨fun hw => ⟨w.property.1, hw⟩, fun hw => hw.2⟩

end ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
