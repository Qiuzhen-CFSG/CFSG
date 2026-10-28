module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiEscapingCentralizer

/-!
# The untrapped centralizer on the actual DGS nine-path

Starting from one common Sylow at the base edge, conjugation in the
actual Suzuki star constructs the common Sylow at every incident edge.
For an arbitrary nine-path, choose coordinates from its fourth/fifth
edge and transport its two remote critical centers and interior core
containments together. The proved critical-center indices and remote
center propagation show that every two-subgroup of its pointwise fixer
centralizes the full span at the fifth vertex. The calculation uses
independent vertices before returning to the literal BasedWalk, avoiding
expensive elimination of its dependent coordinates.

Now normalize the second/third edge instead. For t in the same path
subgroup, let A = C_(V_delta1)(t). If A escapes Q_delta3, the just-proved
fifth-span centralization discharges the premise of
SuzukiEscapingCentralizer. Thus A join V_delta5 is transitive at delta3
and t centralizes its entire span. Both orientations and the original
completion inclusion are retained; no extra centralization or family
of common Sylows is assumed.

This completes the two span-centralization steps in the nonbinary
untrapped branch of (12.7). The subsequent conjugated-intersection
argument at the intervening linear vertex and the (3.2)(c) contradiction
remain needed for the odd-order nine-path bound. The binary cases,
Suzuki selection, full kernel conclusions and final (12.8)--(12.9)/(13.1)
assembly remain separate obligations of this source family.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.7), printed p.184, using (12.3)(a), (12.4)(b) and (12.5).
-/

public noncomputable section
open Subgroup SimpleGraph
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem common_sylow_neighbors
    (h : HypothesisF11 L S) (i : Bool) (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    ∀ v, (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) v →
      ∃ R : Sylow 2 (star L S i), (R : Subgroup (star L S i)).map (star L S i).subtype =
        Q (reducedFamily L S) v ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i) := by
  let F := reducedFamily L S
  let P := star L S i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite P := Finite.of_injective (inclusion (star_le_stabilizer i)) (inclusion_injective _)
  intro v hv
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨g,hg,hgm⟩ := star_locally_transitive h i hadj hv
  have hgy : g • base F i = base F i := star_le_stabilizer i hg
  let t : P := ⟨g,hg⟩
  let R := T.mapSurjective (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).surjective
  have hf : P.subtype.comp (MulAut.conj t).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp P.subtype := by ext u; rfl
  refine ⟨R,?_⟩
  change ((T : Subgroup P).map (MulAut.conj t).toMonoidHom).map P.subtype = _
  rw [Subgroup.map_map,hf,←Subgroup.map_map,hT,Subgroup.map_sup,←Q_translate F,←Q_translate F,hgm,hgy]

private theorem interior_center_propagation
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (T₀ : Sylow 2 (star L S i))
    (hT₀ : (T₀ : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
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
    V (reducedFamily L S) v5 1 ≤ centralizer (D : Set (G₀ L S)) := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hcommon := common_sylow_neighbors h i T₀ hT₀
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
  have hy6 : (graph F).Adj (base F i) (g⁻¹ • v6) := by simpa only [hy] using ha h56
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨R,hR⟩ := hcommon _ hy6
  have hia := source_suzuki_critical_center_index h i hb hca' (ha h23.symm)
    (by simpa only [hm] using ha h34) hadj hn eSuz eLin T₀ hT₀
  have hic := source_suzuki_critical_center_index h i hb hcc' (ha h78)
    (ha h67.symm) hy6 hn eSuz eLin R hR
  have hZn (u v : Vertex F) (hd : (graph F).dist u v ≤ 2) : Z F u ≤ Q F v :=
    CommutingNontrivial.Z_le_Q_of_dist_lt_b F (fun v => (source_Z_Q_U (reduced_triple h) v).1)
      u v (lt_of_le_of_lt hd hb) (reduced_kernel_sylow h v)
  have hZa : Z F (g⁻¹ • v2) ≤ Q F (base F (!i)) := by
    have hh := map_mono (f := c) (hZn v2 v4
      (SimpleGraph.dist_le (SimpleGraph.Walk.cons h23 (SimpleGraph.Walk.cons h34 .nil))))
    change (Z F v2).map (MulAut.conj g⁻¹).toMonoidHom ≤
      (Q F v4).map (MulAut.conj g⁻¹).toMonoidHom at hh
    rwa [←Z_translate F,←Q_translate F,hm] at hh
  have hZc : Z F (g⁻¹ • v8) ≤ Q F (g⁻¹ • v6) := by
    have hh := map_mono (f := c) (hZn v8 v6
      (SimpleGraph.dist_le (SimpleGraph.Walk.cons h78.symm (SimpleGraph.Walk.cons h67.symm .nil))))
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
  have hV' := (source_suzuki_remote_center_propagation h i hn eSuz hy6 hne T₀ R hT₀ hR
    hZa hZc hia hic (D.map c) hDy hDm hCa hCc).1
  have hV : V F v5 1 ≤ centralizer (D : Set (G₀ L S)) := by
    intro u hu t ht
    have hum : c u ∈ V F (base F i) 1 := by
      have hh := mem_map_of_mem c hu
      change c u ∈ (V F v5 1).map (MulAut.conj g⁻¹).toMonoidHom at hh
      rw [←V_translate F,hy] at hh
      exact hh
    have hh := hV' hum (c t) (mem_map_of_mem c ht)
    apply (MulAut.conj g⁻¹).injective
    change c (t * u) = c (u * t)
    simpa only [map_mul] using hh
  exact hV

set_option backward.isDefEq.respectTransparency false in
/-- Propagation at the fifth vertex of an arbitrary nine-path. The coordinate
change is constructed from its fourth/fifth edge, and all path fixers and
critical pairs are transported by that same element. -/
theorem source_suzuki_nine_path_span_centralizer_at
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (T₀ : Sylow 2 (star L S i))
    (hT₀ : (T₀ : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 9 v₀) (hp : p.Nonbacktracking)
    (htype : (p.2.2.2.2.1 : Vertex (reducedFamily L S)).type = i)
    (hca : IsCriticalPair (reducedFamily L S)
      (p.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)))
    (hcc : IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)))
    (D : Subgroup (G₀ L S)) (hD : IsPGroup 2 D)
    (hfix : D ≤ pathStabilizer (reducedFamily L S) p) :
    let F := reducedFamily L S
    V F (p.2.2.2.2.1 : Vertex F) 1 ≤ centralizer (D : Set (G₀ L S)) ∧
      (V F (p.2.2.2.2.1 : Vertex F) 1).map (G₀ L S).subtype ≤
        centralizer (D.map (G₀ L S).subtype : Set G) := by
  let F := reducedFamily L S
  have hcore := source_mixed_path_two_subgroup_core h (!i) eLin
    (by cases i <;> exact eSuz) p hp D hD hfix
  have hV := interior_center_propagation h i hb hn eSuz eLin T₀ hT₀
    p.2.2.1.property p.2.2.2.1.property p.2.2.2.2.1.property
    p.2.2.2.2.2.1.property p.2.2.2.2.2.2.1.property p.2.2.2.2.2.2.2.1.property
    hp.2.2.2.2.1 htype hca hcc D
    (hcore _ (by simp [BasedWalk.vertices])) (hcore _ (by simp [BasedWalk.vertices]))
    (hcore _ (by simp [BasedWalk.vertices])) (hcore _ (by simp [BasedWalk.vertices]))
  refine ⟨hV,?_⟩
  rw [←inf_eq_left] at hV ⊢
  rw [map_inf_centralizer_of_injective _ (G₀ L S).subtype_injective,hV]

set_option backward.isDefEq.respectTransparency false in
/-- The untrapped branch of (12.7) on the literal nine-path fixer. The
fifth-vertex span is proved to centralize the path subgroup before propagating
to the third-vertex span; it is not an additional centralization assumption. -/
theorem source_suzuki_nine_path_untrapped_span
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (T₀ : Sylow 2 (star L S i))
    (hT₀ : (T₀ : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 9 v₀) (hp : p.Nonbacktracking)
    (hm : (p.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) (!i))
    (hy : (p.2.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) i)
    (hca : IsCriticalPair (reducedFamily L S)
      (p.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)))
    (hcc : IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)))
    (hc : IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (base (reducedFamily L S) i))
    (D : Subgroup (G₀ L S)) (hD : IsPGroup 2 D)
    (hfix : D ≤ pathStabilizer (reducedFamily L S) p)
    (t : G₀ L S) (ht : t ∈ D)
    (hesc : ¬ V (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)) 1 ⊓
      centralizer ({t} : Set (G₀ L S)) ≤ Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    let E := (V F (p.1 : Vertex F) 1 ⊓ centralizer ({t} : Set (G₀ L S))) ⊔
      V F (p.2.2.2.2.1 : Vertex F) 1
    (∀ v, (graph F).Adj (base F i) v → ∃ g ∈ E, g • base F (!i) = v) ∧
      V F (base F i) 1 ≤ centralizer ({t} : Set (G₀ L S)) ∧
      (V F (base F i) 1).map (G₀ L S).subtype ≤ centralizer ({(t : G)} : Set G) := by
  let F := reducedFamily L S
  have hcommon := common_sylow_neighbors h i T₀ hT₀
  have hcore := source_mixed_path_two_subgroup_core h (!i) eLin
    (by cases i <;> exact eSuz) p hp D hD hfix
  have htype : (p.2.2.2.2.1 : Vertex F).type = i := by
    have h3 : (p.2.2.1 : Vertex F).type = i := congrArg Subgroup.CosetGeometry.Vertex.type hy
    have h4 : i ≠ (p.2.2.2.1 : Vertex F).type := h3 ▸ p.2.2.2.1.property.1
    have h5 := p.2.2.2.2.1.property.1
    exact (Bool.eq_not_iff.mpr h5.symm).trans (Bool.not_eq_iff.mpr h4.symm)
  have hW := (source_suzuki_nine_path_span_centralizer_at h i hb hn eSuz eLin T₀ hT₀
    p hp htype hca hcc D hD hfix).1
  have hWt : V F (p.2.2.2.2.1 : Vertex F) 1 ≤ centralizer ({t} : Set (G₀ L S)) := by
    intro u hu a ha
    have he : a = t := Set.mem_singleton_iff.mp ha
    subst a
    exact hW hu t ht
  have hxm : (graph F).Adj (p.1 : Vertex F) (base F (!i)) := by
    have hh : (graph F).Adj (p.1 : Vertex F) (p.2.1 : Vertex F) := p.2.1.property
    simpa only [hm] using hh
  have hyz : (graph F).Adj (base F i) (p.2.2.2.1 : Vertex F) := by
    have hh : (graph F).Adj (p.2.2.1 : Vertex F) (p.2.2.2.1 : Vertex F) := p.2.2.2.1.property
    simpa only [hy] using hh
  have hzn : (p.2.2.2.1 : Vertex F) ≠ base F (!i) := by
    simpa only [hm] using hp.2.2.1
  obtain ⟨R,hR⟩ := hcommon _ hyz
  have htm : t ∈ Q F (base F (!i)) := by
    have hh := hcore (p.2.1 : Vertex F) (by simp [BasedWalk.vertices]) ht
    simpa only [hm] using hh
  have hty : t ∈ Q F (base F i) := by
    have hh := hcore (p.2.2.1 : Vertex F) (by simp [BasedWalk.vertices]) ht
    simpa only [hy] using hh
  exact source_suzuki_untrapped_centralizer_propagation h i hb hxm hyz
    p.2.2.2.2.1.property.symm p.2.2.2.2.2.1.property hzn hc hn eSuz eLin
    T₀ R hT₀ hR t htm hty hWt hesc

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
