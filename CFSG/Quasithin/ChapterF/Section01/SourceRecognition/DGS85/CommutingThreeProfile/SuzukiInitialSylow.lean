module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CoreGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearResidualLayer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.FullGraphObstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CoreProductComparison

/-!
# Initial Sylow marking for the linear row

For either endpoint orientation, the linear rank-one quotient supplies an
initial Sylow subgroup of the starred local group whose image in the reduced
completion is the common edge core.  The proof applies the source edge-core
product theorem to the reduced graph, then transports its local Sylow through
the source identification of the graph local group with the starred group.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(8.5), (12.1) and (12.3), pp. 139, 178--180.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/--
For either endpoint, construct the source linear Sylow marking in the starred
local group.  Its image in the completion is the join of the two adjacent
reduced edge cores.
-/
theorem source_linear_initial_sylow
    {k : Type} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card k = 2 ^ n)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k) :
    ∃ T : Sylow 2 (star L S i),
      (T : Subgroup (star L S i)).map (star L S i).subtype =
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
          Q (reducedFamily L S) (base (reducedFamily L S) i) := by
  let F := family (fun j => (P₀ L S j).subgroupOf (G₀ L S))
  let d := Reduction.reducedFullEarlierLocalTheorems h
  change EarlierLocalTheorems (family (fun j => (P₀ L S j).subgroupOf (G₀ L S))) at d
  let _ := finite_endpoints (Reduction.reduced_triple h)
  let v := base F i
  let w := base F (!i)
  have hvw : (graph F).Adj v w := by
    exact ⟨by change i ≠ !i; cases i <;> decide,
      Subgroup.CosetGeometry.incident_base F i (!i)⟩
  let ep : Matrix.SpecialLinearGroup (Fin 2) k ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩
  have efamily : (family L i ⧸ pCore 2 (family L i)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k := by
    cases i with
    | false => change (L 0 ⧸ pCore 2 (L 0)) ≃* _; exact e
    | true => change (L 1 ⧸ pCore 2 (L 1)) ≃* _; exact e
  have hM : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)) := by
    change IsRankOneModel (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v))
    have hq : IsRankOneModel (family L i ⧸ pCore 2 (family L i)) := by
      cases i
      · exact h.quotient 0
      · exact h.quotient 1
    exact hq.of_equiv ((Reduction.reduced_graphLinearQuotient h i (efamily.trans ep)).trans
      (efamily.trans ep).symm)
  have hi : ClassicalGroup.IsPSL (d.localGroup v ⧸ pCore 2 (d.localGroup v)) 2 (2 ^ n) := by
    change ClassicalGroup.IsPSL (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) 2 (2 ^ n)
    exact ⟨k, inferInstance, inferInstance, hcard,
      ⟨Reduction.reduced_graphLinearQuotient h i (efamily.trans ep)⟩⟩
  obtain ⟨R, hR⟩ := source_edge_core_local_sylow
    (Reduction.reduced_triple h) (Reduction.reduced_borel_core_sylow h) d hvw
  have hob : ¬ stabilizer F w ≤ normalizer
      ((Q F v ⊓ Q F w : Subgroup (G₀ L S)) : Set (G₀ L S)) := by
    change ¬ stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      normalizer ((Q (reducedFamily L S) (base (reducedFamily L S) i) ⊓
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)) : Subgroup (G₀ L S)) : Set (G₀ L S))
    exact Reduction.reduced_graph_core_obstruction h _ _ hvw.symm
  have hprod := source_linear_edge_core_product
    (Reduction.reduced_triple h) d hvw hM R hR hob hn hi
  have hlocal : d.localGroup v = star L S i := by
    change graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) = star L S i
    exact source_linear_graphLocalGroup_eq_star h i e
  let c : d.localGroup v ≃* star L S i := MulEquiv.subgroupCongr hlocal
  have hfinv : Finite
      (stabilizer F v) := by
    change Finite (stabilizer (reducedFamily L S) (base (reducedFamily L S) i))
    exact (Reduction.reduced_graph_setup h).2.2.1 v |>.1
  let : Finite (stabilizer F v) := hfinv
  let : Finite (d.localGroup v) := Finite.of_injective
    (inclusion (d.local_le v)) (inclusion_injective _)
  let : Finite (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)) := by
    exact (Reduction.reduced_graph_setup h).2.2.1 (base (reducedFamily L S) i) |>.1
  let : Finite (star L S i) := Finite.of_injective
    (inclusion (star_le_stabilizer (L := L) (S := S) i)) (inclusion_injective _)
  let T : Sylow 2 (star L S i) :=
    R.mapSurjective (f := c.toMonoidHom) c.surjective
  have hTc : (T : Subgroup (star L S i)).map (star L S i).subtype =
      (R : Subgroup (d.localGroup v)).map (d.localGroup v).subtype := by
    dsimp [T]
    change ((R : Subgroup (d.localGroup v)).map c.toMonoidHom).map
      (star L S i).subtype = _
    rw [Subgroup.map_map]
    rfl
  refine ⟨T, ?_⟩
  rw [hTc, hR]
  simpa only [v, w, Reduction.reducedFamily, sup_comm] using hprod.symm

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
