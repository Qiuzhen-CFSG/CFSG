module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiNeighborOrbits
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.FullEdgeComplements
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SourceParameter
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.ComplementSelection

/-!
# One full-Borel complement on the source paths

In the mixed linear/nonbinary Suzuki branch, the normal two-core of each
full edge is transitive on the remaining neighbors at either endpoint.
The linear action is already proved; at the Suzuki endpoint the original
common-Sylow marking supplies the orbit. One common edge conjugation
transports these actions to arbitrary vertices.

An odd subgroup fixing an edge normalizes its two-core. Coprime complement
conjugacy gives another fixed neighbor: conjugate the subgroup into a point
stabilizer, then translate that point back. Thus the original odd subgroup
stays fixed while its path is extended. Induction constructs nonbacktracking
walks of every prescribed length through either orientation of the edge.

Apply this construction to the complement of the actual source-minimal
nonregular path from LocalStructure.SourceParameter. This selects that
simple path and both six-path orientations with the same complement,
retaining its literal image in the original full Borel. The complement
property transfers to every edge that it fixes. The six-paths are expressed
as nonbacktracking based walks, as in SuzukiSixPathRegular; reversing the
Suzuki-starting one gives the orientation of the source's gamma_2.

The common-Sylow identity and the two original quotient markings remain
genuine earlier-source inputs. This selection supplies neither the
critical-center data along the chosen six-paths nor endpoint regularity.
The opposite six-path action, the deduction s >= 7, Suzuki selection, the
full-kernel bounds, binary alternatives and the remaining Chapter 12/13
assembly still require their source arguments.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(6.7), printed p.123, and the path choice in (12.8), printed pp.185--186.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open BenderSuzuki.Converse BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem mixed_base_edge_transitive
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL2 k)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
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
    obtain ⟨t,ht,he⟩ := suzuki_neighbor_core_transitive h (!i) hn eSuz T
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

private theorem mixed_edge_core_transitive
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL2 k)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
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
  obtain ⟨t,ht,he⟩ := mixed_base_edge_transitive h i hn eLin eSuz T hT a.type
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
theorem source_mixed_odd_fixed_neighbor
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL2 k)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
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
      exact mixed_edge_core_transitive h i hn eLin eSuz T hT hax y.property hcy hyx'
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
theorem source_mixed_odd_fixed_paths
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL2 k)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
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
    obtain ⟨y,hxy,hya,hCy⟩ := source_mixed_odd_fixed_neighbor h i hn eLin eSuz T hT hax.symm
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


/-- Select the source-minimal nonregular path and both six-path orientations
with one complement to the original full-Borel core. -/
theorem source_mixed_minimal_path_fixed_six_paths
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL2 k)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (T : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i))) :
    let F := reducedFamily L S
    ∃ m : ℕ, m+1 = sourceS (P := fun j => (P₀ L S j).subgroupOf (G₀ L S)) ∧
      ∃ j : Bool, ∃ p : BasedWalk (graph F) (m+1) (base F j),
        p.Nonbacktracking ∧ ¬ Theory.GroupAction.CubicTree.RightRegular (A := G₀ L S) p ∧
        p.toWalk.IsPath ∧ ∃ C : Subgroup (G₀ L S),
          Odd (Nat.card C) ∧ C ≤ pathStabilizer F p ∧
          C.map (G₀ L S).subtype ≤ B₀ L S ⊓ (pathStabilizer F p).map (G₀ L S).subtype ∧
          Disjoint (C.map (G₀ L S).subtype) ((commonBorel L S).pCoreIn 2) ∧
          C.map (G₀ L S).subtype ⊔ (commonBorel L S).pCoreIn 2 = B₀ L S ∧
          (∀ a x : Vertex F, (graph F).Adj a x →
            C ≤ stabilizer F x ⊓ stabilizer F a →
            (pCore 2 (stabilizer F x ⊓ stabilizer F a : Subgroup (G₀ L S))).IsComplement'
              (C.subgroupOf (stabilizer F x ⊓ stabilizer F a))) ∧
          ∀ r : Bool, ∃ γ : BasedWalk (graph F) 6 (base F r),
            (γ.1 : Vertex F) = base F (!r) ∧ γ.Nonbacktracking ∧
            C ≤ pathStabilizer F γ ∧
            C.map (G₀ L S).subtype ≤ (pathStabilizer F γ).map (G₀ L S).subtype := by
  let F := reducedFamily L S
  obtain ⟨m,hm,j,p,hp,hpn,hsimp,D,hD,hdis,hsup,hcop⟩ := reduced_sourceS_path_complement h
  have hBG : B₀ L S ≤ G₀ L S :=
    (show B₀ L S ≤ P₀ L S 0 from le_sup_right).trans le_sup_left
  have hDG : D ≤ G₀ L S := (hD.trans inf_le_left).trans hBG
  let C := D.subgroupOf (G₀ L S)
  have hCD : C.map (G₀ L S).subtype = D := map_subgroupOf_eq_of_le hDG
  have hcard : Nat.card C = Nat.card D := Nat.card_congr (subgroupOfEquivOfLe hDG).toEquiv
  have hodd : Odd (Nat.card C) := hcard.symm ▸ Nat.coprime_two_left.mp hcop
  have hCp : C ≤ pathStabilizer F p := by
    apply (map_le_map_iff_of_injective (G₀ L S).subtype_injective).mp
    rw [hCD]
    exact hD.trans inf_le_right
  have hE : stabilizer F (base F false) ⊓ stabilizer F (base F true) =
      (B₀ L S).subgroupOf (G₀ L S) := by
    rw [stabilizer,stabilizer,Subgroup.CosetGeometry.stabilizer_base,
      Subgroup.CosetGeometry.stabilizer_base]
    exact (reduced_triple h).intersection
  have hCE : C ≤ stabilizer F (base F false) ⊓ stabilizer F (base F true) := by
    rw [hE]
    exact subgroupOf_mono _ (hD.trans inf_le_left)
  have hCr (r : Bool) : C ≤ stabilizer F (base F (!r)) ⊓ stabilizer F (base F r) := by
    cases r
    · exact le_inf (hCE.trans inf_le_right) (hCE.trans inf_le_left)
    · exact hCE
  have hadj (r : Bool) : (graph F).Adj (base F r) (base F (!r)) :=
    ⟨by change r ≠ !r; cases r <;> decide,Subgroup.CosetGeometry.incident_base F r (!r)⟩
  let E := stabilizer F (base F false) ⊓ stabilizer F (base F true)
  have hcore : (E.pCoreIn 2).map (G₀ L S).subtype = (commonBorel L S).pCoreIn 2 := by
    dsimp only [E]
    rw [hE,←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 (G₀ L S).subtype (G₀ L S).subtype_injective,map_subgroupOf_eq_of_le hBG,B₀_core h]
  have hdis' : Disjoint C (E.pCoreIn 2) := by
    apply disjoint_iff.mpr
    apply map_injective (G₀ L S).subtype_injective
    rw [Subgroup.map_inf _ _ _ (G₀ L S).subtype_injective,Subgroup.map_bot,hCD,hcore]
    exact disjoint_iff.mp hdis
  have hsup' : C ⊔ E.pCoreIn 2 = E := by
    apply map_injective (G₀ L S).subtype_injective
    rw [Subgroup.map_sup,hCD,hcore,hsup]
    dsimp only [E]
    rw [hE,map_subgroupOf_eq_of_le hBG]
  have hEC : (pCore 2 E).IsComplement' (C.subgroupOf E) := by
    have hd : Disjoint (pCore 2 E) (C.subgroupOf E) := by
      apply disjoint_iff.mpr
      apply map_injective E.subtype_injective
      rw [Subgroup.map_inf _ _ _ E.subtype_injective,Subgroup.map_bot,map_subgroupOf_eq_of_le hCE]
      exact disjoint_iff.mp hdis'.symm
    have hs : pCore 2 E ⊔ C.subgroupOf E = ⊤ := by
      apply map_injective E.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hCE]
      have ht : (⊤ : Subgroup E).map E.subtype = E := by
        rw [←subgroupOf_self E,map_subgroupOf_eq_of_le le_rfl]
      rw [ht]
      exact (sup_comm _ _).trans hsup'
    refine ⟨mul_injective_of_disjoint hd,?_⟩
    intro a
    have ha : a ∈ pCore 2 E ⊔ C.subgroupOf E := hs ▸ mem_top a
    obtain ⟨u,hu,v,hv,he⟩ := mem_sup_of_normal_left.mp ha
    exact ⟨(⟨u,hu⟩,⟨v,hv⟩),he⟩
  refine ⟨m,hm,j,p,hp,hpn,hsimp,C,hodd,hCp,?_,?_,?_,?_,?_⟩
  · rwa [hCD]
  · rwa [hCD]
  · rwa [hCD]
  · intro a x hax hCa
    exact source_edge_complement_transfer h (hadj false) hax.symm
      (C.subgroupOf E) hEC C hCa hodd
      (Nat.card_congr (subgroupOfEquivOfLe hCE).toEquiv).symm
  · intro r
    exact source_mixed_odd_fixed_paths h i hn eLin eSuz T hT C hodd 5 (hadj r) (hCr r)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
