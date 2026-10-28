module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.ComplementFixedPaths

/-!
# One source-minimal complement on a normalized nine-path

The complement chosen for the actual source-minimal nonregular path fixes
both endpoints of the original base edge. Extend the edge backwards twice
and forwards seven times, keeping that same odd subgroup fixed throughout.
The resulting nine-path has its second and third vertices equal to the
original linear and Suzuki base vertices, respectively.

The source application retains the minimal path, its full-Borel complement,
the literal original inclusion maps and the complement on the normalized
edge. This supplies the path and complement inputs of the opposite six-path
argument. Critical-pair geometry, natural centers and the preceding
commutator identities remain earlier-source obligations.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(6.7), printed p.123, and (12.7)--(12.8), printed pp.184--186.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open BenderSuzuki.Converse BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem fixed_nine_path
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL2 k)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (T : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (C : Subgroup (G₀ L S)) (hodd : Odd (Nat.card C))
    (hC : C ≤ stabilizer (reducedFamily L S) (base (reducedFamily L S) i) ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i))) :
    ∃ v₀ : Vertex (reducedFamily L S),
      ∃ p : BasedWalk (graph (reducedFamily L S)) 9 v₀,
        p.Nonbacktracking ∧
        (p.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) i ∧
        (p.2.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) (!i) ∧
        C ≤ pathStabilizer (reducedFamily L S) p := by
  let F := reducedFamily L S
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨a,ha,han,hCa⟩ := source_mixed_odd_fixed_neighbor h i hn eLin eSuz T hT
    hadj C hodd (le_inf (hC.trans inf_le_right) (hC.trans inf_le_left))
  obtain ⟨v₀,hv,hvn,hCv⟩ := source_mixed_odd_fixed_neighbor h i hn eLin eSuz T hT
    ha.symm C hodd (le_inf (hC.trans inf_le_left) hCa)
  obtain ⟨q,hq,hqn,hCq,_⟩ := source_mixed_odd_fixed_paths h i hn eLin eSuz T hT
    C hodd 6 hadj (le_inf (hC.trans inf_le_right) (hC.trans inf_le_left))
  let p : BasedWalk (graph F) 9 v₀ := ⟨⟨a,hv.symm⟩,⟨⟨base F i,ha.symm⟩,q⟩⟩
  refine ⟨v₀,p,?_,rfl,hq,?_⟩
  · change base F i ≠ v₀ ∧ (q.1 : Vertex F) ≠ a ∧ q.Nonbacktracking
    exact ⟨hvn.symm,hq.symm ▸ han.symm,hqn⟩
  · intro c hc z hz
    change z ∈ v₀ :: a :: q.vertices at hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hCv hc
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hCa hc
    · exact hCq hc z hz

/-- Extend the exact source-minimal path complement to the normalized nine-path. -/
theorem source_mixed_minimal_path_fixed_nine_path
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
          ∃ v₀ : Vertex F, ∃ q : BasedWalk (graph F) 9 v₀,
            q.Nonbacktracking ∧ (q.2.1 : Vertex F) = base F i ∧
            (q.2.2.1 : Vertex F) = base F (!i) ∧
            C ≤ pathStabilizer F q ∧
            C.map (G₀ L S).subtype ≤ (pathStabilizer F q).map (G₀ L S).subtype ∧
            (pCore 2 (stabilizer F (base F i) ⊓ stabilizer F (base F (!i)) :
              Subgroup (G₀ L S))).IsComplement'
                (C.subgroupOf (stabilizer F (base F i) ⊓ stabilizer F (base F (!i)))) := by
  let F := reducedFamily L S
  obtain ⟨m,hm,j,p,hp,hpn,hps,C,hodd,hCp,hCo,hdis,hsup,htransfer,_⟩ :=
    source_mixed_minimal_path_fixed_six_paths h i hn eLin eSuz T hT
  have hE : stabilizer F (base F false) ⊓ stabilizer F (base F true) =
      (B₀ L S).subgroupOf (G₀ L S) := by
    rw [stabilizer,stabilizer,Subgroup.CosetGeometry.stabilizer_base,
      Subgroup.CosetGeometry.stabilizer_base]
    exact (reduced_triple h).intersection
  have hCB : C ≤ (B₀ L S).subgroupOf (G₀ L S) := by
    intro c hc
    exact (hCo (mem_map_of_mem (G₀ L S).subtype hc)).1
  have hCbase : C ≤ stabilizer F (base F i) ⊓ stabilizer F (base F (!i)) := by
    cases i
    · simpa only [Bool.not_false,hE] using hCB
    · simpa only [Bool.not_true,inf_comm] using (hE.symm ▸ hCB)
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hK := htransfer (base F (!i)) (base F i) hadj.symm hCbase
  obtain ⟨v₀,q,hq,hmq,hyq,hCq⟩ := fixed_nine_path h i hn eLin eSuz T hT C hodd hCbase
  exact ⟨m,hm,j,p,hp,hpn,hps,C,hodd,hCp,hCo,hdis,hsup,v₀,q,hq,hmq,hyq,hCq,map_mono hCq,hK⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
