module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiComplementFixedPaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.ComplementNinePath

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open BenderSuzuki.Converse BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

theorem small_suzuki_minimal_path_fixed_six_paths
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL2 k)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
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
    exact small_suzuki_odd_fixed_paths h i eLin eSuz T hT C hodd 5 (hadj r) (hCr r)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
