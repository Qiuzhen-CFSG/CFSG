module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiRemoteCenters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSylowNeighbors

/-!
# Remote-center transitivity on a zero-parameter path

The frozen small-Suzuki remote-center theorem is transported from the marked
base edge to the middle edge of an actual nine-path.  This supplies the
centralizer action used on the Suzuki side of the terminal normalized-edge
argument, without a positive Suzuki parameter or a generation-by-two-
involutions assertion.
-/

public noncomputable section
open Subgroup SimpleGraph
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

set_option backward.isDefEq.respectTransparency false in
theorem source_small_suzuki_path_center_transitivity
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup 0)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    {v2 v3 v4 v5 v6 v7 v8 : Vertex (reducedFamily L S)}
    (h23 : (graph (reducedFamily L S)).Adj v2 v3)
    (h34 : (graph (reducedFamily L S)).Adj v3 v4)
    (h45 : (graph (reducedFamily L S)).Adj v4 v5)
    (h56 : (graph (reducedFamily L S)).Adj v5 v6)
    (h67 : (graph (reducedFamily L S)).Adj v6 v7)
    (h78 : (graph (reducedFamily L S)).Adj v7 v8)
    (hne64 : v6 ≠ v4) (htype : v5.type = i)
    (hca : IsCriticalPair (reducedFamily L S) v2 v5)
    (hcc : IsCriticalPair (reducedFamily L S) v8 v5)
    (D : Subgroup (G₀ L S))
    (hD2 : D ≤ Q (reducedFamily L S) v2)
    (hD4 : D ≤ Q (reducedFamily L S) v4)
    (hD5 : D ≤ Q (reducedFamily L S) v5)
    (hD8 : D ≤ Q (reducedFamily L S) v8) :
    (∀ v, (graph (reducedFamily L S)).Adj v5 v →
      ∃ a ∈ stabilizer (reducedFamily L S) v5 ⊓ centralizer (D : Set (G₀ L S)),
        a • v4 = v) ∧
      V (reducedFamily L S) v5 1 ≤ centralizer (D : Set (G₀ L S)) := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have ht4 : v4.type = !i := Bool.eq_not_iff.mpr (htype ▸ h45.1)
  obtain ⟨g,hg4,hg5⟩ := incident_common_translate F h45.2
  rw [ht4] at hg4
  rw [htype] at hg5
  let c := (MulAut.conj g⁻¹).toMonoidHom
  have hm : g⁻¹ • v4 = base F (!i) := by rw [←hg4,inv_smul_smul]
  have hy : g⁻¹ • v5 = base F i := by rw [←hg5,inv_smul_smul]
  have hca' : IsCriticalPair F (g⁻¹ • v2) (base F i) := by
    simpa only [hy] using criticalPair_translate F hca g⁻¹
  have hcc' : IsCriticalPair F (g⁻¹ • v8) (base F i) := by
    simpa only [hy] using criticalPair_translate F hcc g⁻¹
  have ha {u v : Vertex F} (huv : (graph F).Adj u v) :
      (graph F).Adj (g⁻¹ • u) (g⁻¹ • v) :=
    (Subgroup.CosetGeometry.translationGraphIso F g⁻¹).map_adj_iff.mpr huv
  have hy6 : (graph F).Adj (base F i) (g⁻¹ • v6) := by
    simpa only [hy] using ha h56
  have hbase : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide,
      Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨R,hR⟩ := (source_common_sylow_neighbors h i T hT) (g⁻¹ • v6) hy6
  have hZn (u v : Vertex F) (hd : (graph F).dist u v ≤ 2) : Z F u ≤ Q F v :=
    CommutingNontrivial.Z_le_Q_of_dist_lt_b F
      (fun v => (source_Z_Q_U (reduced_triple h) v).1) u v
      (lt_of_le_of_lt hd hb) (reduced_kernel_sylow h v)
  have hZa : Z F (g⁻¹ • v2) ≤ Q F (base F (!i)) := by
    have hh := map_mono (f := c) (hZn v2 v4
      (SimpleGraph.dist_le (SimpleGraph.Walk.cons h23 (SimpleGraph.Walk.cons h34 .nil))))
    change (Z F v2).map (MulAut.conj g⁻¹).toMonoidHom ≤
      (Q F v4).map (MulAut.conj g⁻¹).toMonoidHom at hh
    rwa [←Z_translate F,←Q_translate F,hm] at hh
  have hZc : Z F (g⁻¹ • v8) ≤ Q F (g⁻¹ • v6) := by
    have hh := map_mono (f := c) (hZn v8 v6
      (SimpleGraph.dist_le (SimpleGraph.Walk.cons h78.symm
        (SimpleGraph.Walk.cons h67.symm .nil))))
    change (Z F v8).map (MulAut.conj g⁻¹).toMonoidHom ≤
      (Q F v6).map (MulAut.conj g⁻¹).toMonoidHom at hh
    rwa [←Z_translate F,←Q_translate F] at hh
  have hDq (v : Vertex F) (hv : D ≤ Q F v) :
      D.map c ≤ Q F (g⁻¹ • v) := by
    have hh := map_mono (f := c) hv
    change D.map c ≤ (Q F v).map (MulAut.conj g⁻¹).toMonoidHom at hh
    rwa [←Q_translate F] at hh
  have hDy : D.map c ≤ Q F (base F i) := by simpa only [hy] using hDq v5 hD5
  have hDm : D.map c ≤ Q F (base F (!i)) := by simpa only [hm] using hDq v4 hD4
  have hCa : Z F (g⁻¹ • v2) ≤ centralizer (D.map c : Set (G₀ L S)) :=
    (Z_centralizes_Q F _ (source_Z_Q_U (reduced_triple h) _).1).trans
      (centralizer_le (hDq v2 hD2))
  have hCc : Z F (g⁻¹ • v8) ≤ centralizer (D.map c : Set (G₀ L S)) :=
    (Z_centralizes_Q F _ (source_Z_Q_U (reduced_triple h) _).1).trans
      (centralizer_le (hDq v8 hD8))
  have hne : g⁻¹ • v6 ≠ base F (!i) := by
    rw [←hm]
    exact fun he => hne64 ((MulAction.injective g⁻¹) he)
  have hremote := small_suzuki_remote_critical_center_transitive h i hb eSuz
    (ha h23.symm) (by simpa only [hm] using ha h34) hy6 (ha h67.symm) (ha h78)
    hne hca' hcc' T R hT hR
  let E := Z F (g⁻¹ • v2) ⊔ Z F (g⁻¹ • v8)
  have hEC : E ≤ centralizer (D.map c : Set (G₀ L S)) := sup_le hCa hCc
  have hEP : E ≤ star L S i := by
    apply sup_le
    · exact hZa.trans ((le_sup_left.trans hT.ge).trans (map_subtype_le _))
    · exact hZc.trans ((le_sup_left.trans hR.ge).trans (map_subtype_le _))
  have htrans : ∀ v, (graph F).Adj v5 v →
      ∃ a ∈ stabilizer F v5 ⊓ centralizer (D : Set (G₀ L S)), a • v4 = v := by
    intro v hv
    have hv' : (graph F).Adj (base F i) (g⁻¹ • v) := by
      simpa only [hy] using ha hv
    obtain ⟨a,haE,hea⟩ := hremote (g⁻¹ • v) hv'
    have hafix : a • base F i = base F i := star_le_stabilizer i (hEP haE)
    have hact : c (g * a * g⁻¹) = a := by
      change g⁻¹ * (g * a * g⁻¹) * (g⁻¹)⁻¹ = a
      group
    refine ⟨g * a * g⁻¹,⟨?_,?_⟩,?_⟩
    · change (g * a * g⁻¹) • v5 = v5
      rw [mul_smul,mul_smul,hy,hafix,hg5]
    · intro d hd
      apply (MulAut.conj g⁻¹).injective
      change c (d * (g * a * g⁻¹)) = c ((g * a * g⁻¹) * d)
      rw [map_mul c d (g * a * g⁻¹),map_mul c (g * a * g⁻¹) d,hact]
      exact hEC haE (c d) (mem_map_of_mem c hd)
    · rw [mul_smul,mul_smul,hm,hea,smul_inv_smul]
  have hremoteC := small_suzuki_remote_critical_center_propagation h i hb eSuz
    (ha h23.symm) (by simpa only [hm] using ha h34) hy6 (ha h67.symm) (ha h78)
    hne hca' hcc' T R hT hR (D.map c) (hDq v2 hD2) (hDq v8 hD8) hDm hDy
  have hV : V F v5 1 ≤ centralizer (D : Set (G₀ L S)) := by
    intro u hu t ht
    have huc : c u ∈ V F (base F i) 1 := by
      have hh := mem_map_of_mem c hu
      change c u ∈ (V F v5 1).map (MulAut.conj g⁻¹).toMonoidHom at hh
      rw [←V_translate F,hy] at hh
      exact hh
    have htc : c t ∈ D.map c := mem_map_of_mem c ht
    have hh := hremoteC.1 huc (c t) htc
    apply (MulAut.conj g⁻¹).injective
    change c (t * u) = c (u * t)
    simpa only [map_mul] using hh
  exact ⟨htrans,hV⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
