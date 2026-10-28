module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallSolvableObstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallSuzukiEnlargement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.NonlinearObstructionApplication

/-!
# Small solvable obstructions on the original F1.11 triple

An original D₁₀ quotient gives an enlarged quotient D₁₀ or Sz(2), while
an original Sz(2) quotient preserves the starred endpoint. Both therefore
have order dividing twenty through the literal graph/enlargement maps.
The replacement-section proof discharges both 6.5 conclusions. Injective
transport returns the nonnormality statement on the original parabolic
cores and the non-Sylow statement for their full-endpoint closure.

The opposite endpoint is unrestricted. The full Borel, strict dihedral
enlargement and possibly infinite completion are retained. The remaining
small unitary cases are separate obligations.
Source: DGS, Groups and Graphs (1985), 6.1 and 6.4--6.5, pp.118--122;
Aschbacher--Smith F.1.9, printed pp.261--262.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem graph_small_quotient_card (h : HypothesisF11 L S) (j : Bool)
    (hm : Nonempty ((family L j ⧸ pCore 2 (family L j)) ≃* DihedralGroup 5) ∨
      Nonempty ((family L j ⧸ pCore 2 (family L j)) ≃* SuzukiMatrixGroup 0)) :
    Nat.card (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) j) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) j))) ∣ 20 := by
  rcases hm with hd | hs
  · obtain ⟨e⟩ := hd
    rcases reduced_graph_dihedral_alternatives h j e with hd | hs
    · obtain ⟨_,⟨f⟩⟩ := hd
      rw [Nat.card_congr f.toEquiv,DihedralGroup.nat_card]
      decide
    · obtain ⟨f⟩ := hs
      rw [Nat.card_congr f.toEquiv,suzukiZero_card]
  · obtain ⟨e⟩ := hs
    rw [Nat.card_congr (reduced_graphSuzukiQuotient_all h j 0 e).toEquiv,suzukiZero_card]

set_option backward.isDefEq.respectTransparency false in
private theorem small_enlargement_card (h : HypothesisF11 L S) (i : Fin 2)
    (d : LocalRankOneData ((P₀ L S i).subgroupOf (G₀ L S)) ((B₀ L S).subgroupOf (G₀ L S)))
    (hm : Nonempty ((L i ⧸ pCore 2 (L i)) ≃* DihedralGroup 5) ∨
      Nonempty ((L i ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup 0)) :
    Nat.card (localEnlargement d ⧸ pCore 2 (localEnlargement d)) ∣ 20 := by
  revert d hm
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i <;> intro d hm
  · have he := graphLocalGroup_base_eq (reduced_borel_core_sylow h) (reduced_vertex_sylow h) false d
    let c := MulEquiv.subgroupCongr he.symm
    let f : (localEnlargement d ⧸ pCore 2 (localEnlargement d)) ≃*
        (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) false) ⧸
          pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) false))) :=
      QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
    rw [Nat.card_congr f.toEquiv]
    exact graph_small_quotient_card h false hm
  · have he := graphLocalGroup_base_eq (reduced_borel_core_sylow h) (reduced_vertex_sylow h) true d
    let c := MulEquiv.subgroupCongr he.symm
    let f : (localEnlargement d ⧸ pCore 2 (localEnlargement d)) ≃*
        (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true) ⧸
          pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true))) :=
      QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
    rw [Nat.card_congr f.toEquiv]
    exact graph_small_quotient_card h true hm

/-- The original D10 and Sz(2) markings discharge both adjacent-core obstructions,
including the strict dihedral enlargement alternative. -/
theorem reduced_small_solvable_adjacent_core_obstruction (h : HypothesisF11 L S) (i : Fin 2)
    (hmodel : Nonempty ((L (other i) ⧸ pCore 2 (L (other i))) ≃* DihedralGroup 5) ∨
      Nonempty ((L (other i) ⧸ pCore 2 (L (other i))) ≃* SuzukiMatrixGroup 0)) :
    let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
    (¬ localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set (G₀ L S))) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))),
      (T : Subgroup (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))).map
        (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).subtype = (P i).pCoreIn 2 := by
  let d := Classical.choice ((reduced_triple h).local_data (other i))
  let := d.finite_P
  let : Finite (localEnlargement d) := Finite.of_injective
    (inclusion (localEnlargement_le d)) (inclusion_injective _)
  exact source_small_solvable_adjacent_core_obstruction (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) i d
    (QuotientGroup.mk' (pCore 2 (localEnlargement d))) (QuotientGroup.ker_mk' _)
    (small_enlargement_card h (other i) d hmodel)

private theorem reduced_endpoint_le_generated (i : Fin 2) : P₀ L S i ≤ G₀ L S := by
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

private theorem reduced_core_image (h : HypothesisF11 L S) (i : Fin 2) :
    (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2).map (G₀ L S).subtype =
      (parabolic L S i).pCoreIn 2 := by
  rw [map_pCoreIn_of_injective 2 _ _ (G₀ L S).subtype_injective,
    map_subgroupOf_eq_of_le (reduced_endpoint_le_generated i),P₀_core h i]

/-- Both obstructions on the original parabolic cores and full-endpoint closure. -/
theorem original_small_solvable_adjacent_core_obstruction (h : HypothesisF11 L S) (i : Fin 2)
    (hmodel : Nonempty ((L (other i) ⧸ pCore 2 (L (other i))) ≃* DihedralGroup 5) ∨
      Nonempty ((L (other i) ⧸ pCore 2 (L (other i))) ≃* SuzukiMatrixGroup 0)) :
    (¬ enlargedEndpoint L S (other i) ≤ normalizer
      (↑((parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2) : Set G)) ∧
    (¬ parabolic L S (other i) ≤ normalizer
      (↑((parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2) : Set G)) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i))),
      (T : Subgroup (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i)))).map
        (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i))).subtype =
          (parabolic L S i).pCoreIn 2 := by
  let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
  let d := Classical.choice ((reduced_triple h).local_data (other i))
  let := d.finite_P
  obtain ⟨hn0,hs0⟩ := reduced_small_solvable_adjacent_core_obstruction h i hmodel
  have hD : (((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Subgroup (G₀ L S)).map
      (G₀ L S).subtype = (parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2 := by
    rw [Subgroup.map_inf _ _ _ (G₀ L S).subtype_injective,reduced_core_image h i,
      reduced_core_image h (other i)]
  have hn : ¬ enlargedEndpoint L S (other i) ≤ normalizer
      (↑((parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2) : Set G) := by
    intro hh
    apply hn0
    intro x hx
    have hxl : (x : G) ∈ enlargedEndpoint L S (other i) := by
      rw [←reduced_localEnlargement_image h (other i) d]
      exact mem_map_of_mem (G₀ L S).subtype hx
    have hxn := le_normalizer_comap (G₀ L S).subtype (hh hxl)
    rwa [←hD,comap_map_eq_self_of_injective (G₀ L S).subtype_injective] at hxn
  have hEP : enlargedEndpoint L S (other i) ≤ parabolic L S (other i) :=
    sup_le (starredParabolic_le (other i)) ((pCoreIn_le 2 (commonBorel L S)).trans
      (commonBorel_le_parabolic (L := L) (S := S) (other i)))
  refine ⟨hn,(fun hh => hn (hEP.trans hh)),?_⟩
  intro hs
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  have hX := reduced_core_closure_full_image h i
  let f := (G₀ L S).subtype
  let eX : X ≃* conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i)) :=
    (X.equivMapOfInjective f (G₀ L S).subtype_injective).trans (MulEquiv.subgroupCongr hX)
  let := (Classical.choice ((reduced_triple h).local_data (other i))).finite_P
  have hAP : (P i).pCoreIn 2 ≤ P (other i) :=
    (source_core_le_borel (Classical.choice ((reduced_triple h).local_data i))).trans
      (le_sup_right.trans (Classical.choice ((reduced_triple h).local_data (other i))).supplement.le)
  let : Finite X := Finite.of_injective (inclusion (conjugateSpanBy_le_self hAP))
    (inclusion_injective _)
  let : Finite (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i))) :=
    Finite.of_equiv X eX.toEquiv
  obtain ⟨T,hT⟩ := hs
  let T0 := T.mapSurjective (f := eX.symm.toMonoidHom) eX.symm.surjective
  apply hs0
  refine ⟨T0,?_⟩
  apply map_injective (G₀ L S).subtype_injective
  rw [reduced_core_image h i,map_map]
  have hm := congrArg (Subgroup.map
    (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i))).subtype)
    (show (T0 : Subgroup X).map eX.toMonoidHom = (T : Subgroup _) from by
      change ((T : Subgroup _).map eX.symm.toMonoidHom).map eX.toMonoidHom = _
      rw [map_map]
      simp)
  rw [map_map,hT] at hm
  exact hm


end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
