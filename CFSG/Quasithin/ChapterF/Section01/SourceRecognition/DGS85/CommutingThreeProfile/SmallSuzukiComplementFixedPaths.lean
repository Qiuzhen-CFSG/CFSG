module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiCriticalPlacement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.FullEdgeComplements
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SourceParameter
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.ComplementSelection

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open BenderSuzuki.Converse BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem small_suzuki_base_edge_transitive
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL2 k)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    (T : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (j : Bool) {y z : Vertex (reducedFamily L S)}
    (hy : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) j) y)
    (hz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) j) z)
    (hyx : y ≠ base (reducedFamily L S) (!j))
    (hzx : z ≠ base (reducedFamily L S) (!j)) :
    ∃ t ∈ (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!j)) ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) j) :
        Subgroup (G₀ L S)).pCoreIn 2, t • y = z := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hadj (j : Bool) : (graph F).Adj (base F j) (base F (!j)) :=
    ⟨by change j ≠ !j; cases j <;> decide, Subgroup.CosetGeometry.incident_base F j (!j)⟩
  by_cases hj : j = i
  · subst j
    exact linear_incident_core_transitive h i eLin (hadj i) hy hz hyx hzx
  · have hj' : j = !i := Bool.eq_not_iff.mpr hj
    subst j
    obtain ⟨t,ht,he⟩ := small_suzuki_neighbor_core_transitive h (!i) eSuz T
      (by simpa only [Bool.not_not] using hT) hy hz hyx hzx
    let E := stabilizer F (base F (!(!i))) ⊓ stabilizer F (base F (!i))
    let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer F (base F (!i)) from inf_le_right)) (inclusion_injective _)
    have hQE : Q F (base F (!(!i))) ≤ E := le_inf (Q_le_stabilizer F _)
      (((source_Z_Q_U (reduced_triple h) _).2.trans
        (ballKernel_one_le_edge F (hadj (!i)).symm)).trans inf_le_right)
    have hcore := pGroup_le_core_of_core_sylow E (Q F (base F (!(!i)))) hQE
      (isPGroup_pCoreIn 2 _) (source_edge_core_sylow (reduced_triple h)
        (reduced_borel_core_sylow h) (hadj (!i)).symm)
    exact ⟨t,hcore ht,he⟩


private theorem small_suzuki_edge_core_transitive
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL2 k)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    (T : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    {a x y z : Vertex (reducedFamily L S)}
    (hax : (graph (reducedFamily L S)).Adj a x)
    (hy : (graph (reducedFamily L S)).Adj a y)
    (hz : (graph (reducedFamily L S)).Adj a z) (hyx : y ≠ x) (hzx : z ≠ x) :
    ∃ t ∈ (stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) a :
      Subgroup (G₀ L S)).pCoreIn 2, t • y = z := by
  let F := reducedFamily L S
  obtain ⟨g,hga,hgx⟩ := incident_common_translate F hax.2
  have hx : x.type = !a.type := Bool.eq_not_iff.mpr hax.1.symm
  rw [hx] at hgx
  have hga' : g⁻¹ • a = base F a.type := (congrArg (g⁻¹ • ·) hga.symm).trans (inv_smul_smul g _)
  have hgx' : g⁻¹ • x = base F (!a.type) := by rw [←hgx,inv_smul_smul]
  have hadj {w : Vertex F} (hw : (graph F).Adj a w) :
      (graph F).Adj (base F a.type) (g⁻¹ • w) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g⁻¹).map_adj_iff.mpr hw
    change (graph F).Adj (g⁻¹ • a) (g⁻¹ • w) at hh
    rwa [hga'] at hh
  have hne {w : Vertex F} (hw : w ≠ x) : g⁻¹ • w ≠ base F (!a.type) := by
    rw [←hgx']
    exact fun he => hw ((MulAction.injective g⁻¹) he)
  obtain ⟨t,ht,he⟩ := small_suzuki_base_edge_transitive h i eLin eSuz T hT a.type
    (hadj hy) (hadj hz) (hne hyx) (hne hzx)
  let E := stabilizer F (base F (!a.type)) ⊓ stabilizer F (base F a.type)
  have hE : E.map (MulAut.conj g).toMonoidHom = stabilizer F x ⊓ stabilizer F a := by
    rw [map_inf _ _ _ (MulAut.conj g).injective]
    rw [←stabilizer_translate,←stabilizer_translate,hgx,hga]
  have hcore : (E.pCoreIn 2).map (MulAut.conj g).toMonoidHom =
      (stabilizer F x ⊓ stabilizer F a : Subgroup (G₀ L S)).pCoreIn 2 := by
    rw [←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,hE]
  refine ⟨g*t*g⁻¹,?_,?_⟩
  · rw [←hcore]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom ht
  · rw [mul_smul,mul_smul,he,smul_inv_smul]

/-- An odd subgroup fixing an edge has another fixed neighbor at either endpoint. -/

theorem small_suzuki_odd_fixed_neighbor
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL2 k)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    (T : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    {a x : Vertex (reducedFamily L S)} (hax : (graph (reducedFamily L S)).Adj a x)
    (C : Subgroup (G₀ L S)) (hodd : Odd (Nat.card C))
    (hC : C ≤ stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) a) :
    ∃ y : Vertex (reducedFamily L S), (graph (reducedFamily L S)).Adj a y ∧
      y ≠ x ∧ C ≤ stabilizer (reducedFamily L S) y := by
  let F := reducedFamily L S
  let E := stabilizer F x ⊓ stabilizer F a
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer F a from inf_le_right))
    (inclusion_injective _)
  let : Finite (E.pCoreIn 2 ⊔ C : Subgroup (G₀ L S)) := Finite.of_injective
    (inclusion (sup_le (pCoreIn_le 2 E) hC)) (inclusion_injective _)
  let : Group.IsSolvable E := reduced_edge_solvable h hax.symm
  have hsolv : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hC) (inclusion_injective _)
  let : Finite ((graph F).neighborSet a) := finite_neighbors F a
  have hcard : 1 < Nat.card ((graph F).neighborSet a) := by
    rw [card_neighbors_of_indices F (fun j => ((F (!j)).subgroupOf (F j)).index) (fun _ => rfl)]
    exact lt_of_lt_of_le (by decide) (source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) a.type)
  let : Nontrivial ((graph F).neighborSet a) := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hh
    let := hh
    have he : Nat.card ((graph F).neighborSet a) = 1 := Nat.card_of_subsingleton ⟨x,hax⟩
    omega
  obtain ⟨y,hyx⟩ := exists_ne (⟨x,hax⟩ : (graph F).neighborSet a)
  have hyx' : (y : Vertex F) ≠ x := fun he => hyx (Subtype.ext he)
  have hnorm : C ≤ normalizer (E.pCoreIn 2 : Set (G₀ L S)) :=
    hC.trans (E.le_normalizer.trans (normalizer_le_normalizer_characteristic_image E (pCore 2 E)))
  obtain ⟨q,hq,hfix⟩ := Theory.GroupAction.exists_two_group_conjugate_fixing_point
    (E.pCoreIn 2) C (isPGroup_pCoreIn 2 E) hodd hsolv hnorm (y : Vertex F) (by
      intro c hc
      have hca : c • a = a := (hC hc).2
      have hcx : c • x = x := (hC hc).1
      have hcy : (graph F).Adj a (c • (y : Vertex F)) := by
        have hh := (Subgroup.CosetGeometry.translationGraphIso F c).map_adj_iff.mpr y.property
        change (graph F).Adj (c • a) (c • (y : Vertex F)) at hh
        rwa [hca] at hh
      exact small_suzuki_edge_core_transitive h i eLin eSuz T hT hax y.property hcy hyx'
        (fun he => hyx' ((MulAction.injective c) (he.trans hcx.symm))))
  have hqa : q⁻¹ • a = a := ((pCoreIn_le 2 E) ((E.pCoreIn 2).inv_mem hq)).2
  have hqx : q⁻¹ • x = x := ((pCoreIn_le 2 E) ((E.pCoreIn 2).inv_mem hq)).1
  refine ⟨q⁻¹ • (y : Vertex F),?_,?_,?_⟩
  · have hh := (Subgroup.CosetGeometry.translationGraphIso F q⁻¹).map_adj_iff.mpr y.property
    change (graph F).Adj (q⁻¹ • a) (q⁻¹ • (y : Vertex F)) at hh
    rwa [hqa] at hh
  · rw [←hqx]
    exact fun he => hyx' ((MulAction.injective q⁻¹) he)
  · intro c hc
    have hh := hfix (mem_map_of_mem (MulAut.conj q).toMonoidHom hc)
    change (q*c*q⁻¹) • (y : Vertex F) = (y : Vertex F) at hh
    change c • (q⁻¹ • (y : Vertex F)) = q⁻¹ • (y : Vertex F)
    apply MulAction.injective q
    simpa only [mul_smul,smul_inv_smul] using hh


/-- Keep the same odd subgroup while extending either orientation of a fixed edge. -/

theorem small_suzuki_odd_fixed_paths
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL2 k)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    (T : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (C : Subgroup (G₀ L S)) (hodd : Odd (Nat.card C)) (m : ℕ)
    {a x : Vertex (reducedFamily L S)} (hax : (graph (reducedFamily L S)).Adj a x)
    (hC : C ≤ stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) a) :
    ∃ p : BasedWalk (graph (reducedFamily L S)) (m+1) a,
      (p.1 : Vertex (reducedFamily L S)) = x ∧ p.Nonbacktracking ∧
      C ≤ pathStabilizer (reducedFamily L S) p ∧
      C.map (G₀ L S).subtype ≤ (pathStabilizer (reducedFamily L S) p).map (G₀ L S).subtype := by
  let F := reducedFamily L S
  suffices ∃ p : BasedWalk (graph F) (m+1) a,
      (p.1 : Vertex F) = x ∧ p.Nonbacktracking ∧ C ≤ pathStabilizer F p by
    obtain ⟨p,hp,hn,hfix⟩ := this
    exact ⟨p,hp,hn,hfix,map_mono hfix⟩
  induction m generalizing a x with
  | zero =>
    refine ⟨⟨⟨x,hax⟩,PUnit.unit⟩,rfl,trivial,?_⟩
    intro c hc z hz
    change z ∈ [a,x] at hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact (hC hc).2
    · have he : z = x := by simpa only [List.mem_singleton] using hz
      subst z
      exact (hC hc).1
  | succ m ih =>
    obtain ⟨y,hxy,hya,hCy⟩ := small_suzuki_odd_fixed_neighbor h i eLin eSuz T hT hax.symm
      C hodd (le_inf (hC.trans inf_le_right) (hC.trans inf_le_left))
    obtain ⟨p,hpy,hp,hCp⟩ := ih hxy (le_inf hCy (hC.trans inf_le_left))
    refine ⟨⟨⟨x,hax⟩,p⟩,rfl,?_,?_⟩
    · change (p.1 : Vertex F) ≠ a ∧ p.Nonbacktracking
      exact ⟨hpy ▸ hya,hp⟩
    · intro c hc z hz
      change z ∈ a :: p.vertices at hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact (hC hc).2
      · exact hCp hc z hz


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
