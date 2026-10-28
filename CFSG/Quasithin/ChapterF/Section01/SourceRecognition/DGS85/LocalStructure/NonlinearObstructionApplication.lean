module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.NonlinearObstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.UnitaryApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SuzukiEnlargement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EarlierInputs
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.BinaryObstructionApplication

/-!
# The large nonlinear obstruction on the original F1.11 triple

The original Suzuki or unitary quotient marking constructs the actual
enlarged quotient. The general replacement argument now proves both 6.5
clauses without a neighboring-center condition. Injective transport keeps
the original parabolic cores and the closure under the full original
endpoint. The 6.6 application uses this obstruction on the reduced edge.

Only the marked neighboring endpoint is restricted; the opposite endpoint
may be any original rank-one row. Cubic centers and infinite completions
are retained. Small unitary, Sz(2), and D₁₀ alternatives remain separate.
Source: DGS, Groups and Graphs (1985), reduction p.95, 6.4--6.6,
pp.120--123; Aschbacher--Smith F.1.9, pp.261--262.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private def suzukiEnlargementQuotient (h : HypothesisF11 L S) (i : Fin 2)
    (d : LocalRankOneData ((P₀ L S i).subgroupOf (G₀ L S)) ((B₀ L S).subgroupOf (G₀ L S)))
    {m : ℕ} (hm : 0 < m) (e : (L i ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m) :
    (localEnlargement d ⧸ pCore 2 (localEnlargement d)) ≃* SuzukiMatrixGroup m := by
  revert d e
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i <;> intro d e
  · have he := graphLocalGroup_base_eq (reduced_borel_core_sylow h) (reduced_vertex_sylow h) false d
    let c := MulEquiv.subgroupCongr he.symm
    exact (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
      (reduced_graphSuzukiQuotient h false hm e)
  · have he := graphLocalGroup_base_eq (reduced_borel_core_sylow h) (reduced_vertex_sylow h) true d
    let c := MulEquiv.subgroupCongr he.symm
    exact (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
      (reduced_graphSuzukiQuotient h true hm e)

private def projectiveUnitaryEnlargementQuotient (h : HypothesisF11 L S) (i : Fin 2)
    (d : LocalRankOneData ((P₀ L S i).subgroupOf (G₀ L S)) ((B₀ L S).subgroupOf (G₀ L S)))
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (L i ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    (localEnlargement d ⧸ pCore 2 (localEnlargement d)) ≃* ProjectiveSpecialUnitaryMatrixGroup J := by
  revert d e
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i <;> intro d e
  · have he := graphLocalGroup_base_eq (reduced_borel_core_sylow h) (reduced_vertex_sylow h) false d
    let c := MulEquiv.subgroupCongr he.symm
    exact (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
      (reduced_graphProjectiveUnitaryQuotient h false J hn hcard hconj e)
  · have he := graphLocalGroup_base_eq (reduced_borel_core_sylow h) (reduced_vertex_sylow h) true d
    let c := MulEquiv.subgroupCongr he.symm
    exact (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
      (reduced_graphProjectiveUnitaryQuotient h true J hn hcard hconj e)

private def specialUnitaryEnlargementQuotient (h : HypothesisF11 L S) (i : Fin 2)
    (d : LocalRankOneData ((P₀ L S i).subgroupOf (G₀ L S)) ((B₀ L S).subgroupOf (G₀ L S)))
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (L i ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) :
    (localEnlargement d ⧸ pCore 2 (localEnlargement d)) ≃* J.specialSubgroup := by
  revert d e
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i <;> intro d e
  · have he := graphLocalGroup_base_eq (reduced_borel_core_sylow h) (reduced_vertex_sylow h) false d
    let c := MulEquiv.subgroupCongr he.symm
    exact (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
      (reduced_graphSpecialUnitaryQuotient h false J hn hcard hconj e)
  · have he := graphLocalGroup_base_eq (reduced_borel_core_sylow h) (reduced_vertex_sylow h) true d
    let c := MulEquiv.subgroupCongr he.symm
    exact (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
      (reduced_graphSpecialUnitaryQuotient h true J hn hcard hconj e)

/-- Both 6.5 clauses from the original suzuki marking. -/
theorem reduced_suzuki_adjacent_core_obstruction (h : HypothesisF11 L S) (i : Fin 2)
    {m : ℕ} (hm : 0 < m)
    (e : (L (other i) ⧸ pCore 2 (L (other i))) ≃* SuzukiMatrixGroup m) :
    let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
    (¬ localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set (G₀ L S))) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))),
      (T : Subgroup (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))).map
        (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).subtype = (P i).pCoreIn 2 :=
  source_suzuki_adjacent_core_obstruction (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) i (Classical.choice ((reduced_triple h).local_data (other i)))
    hm
    (suzukiEnlargementQuotient h (other i) _ hm e)


/-- Both 6.5 clauses from the original projective unitary marking. -/
theorem reduced_projective_unitary_adjacent_core_obstruction (h : HypothesisF11 L S) (i : Fin 2)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hnpos : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (L (other i) ⧸ pCore 2 (L (other i))) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
    (¬ localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set (G₀ L S))) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))),
      (T : Subgroup (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))).map
        (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).subtype = (P i).pCoreIn 2 :=
  source_projective_unitary_adjacent_core_obstruction (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) i (Classical.choice ((reduced_triple h).local_data (other i)))
    J hnpos hcard hconj
    (projectiveUnitaryEnlargementQuotient h (other i) _ J hnpos hcard hconj e)

/-- Both 6.5 clauses from the original special unitary marking. -/
theorem reduced_special_unitary_adjacent_core_obstruction (h : HypothesisF11 L S) (i : Fin 2)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hnpos : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (L (other i) ⧸ pCore 2 (L (other i))) ≃* J.specialSubgroup) :
    let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
    (¬ localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set (G₀ L S))) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))),
      (T : Subgroup (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))).map
        (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).subtype = (P i).pCoreIn 2 :=
  source_special_unitary_adjacent_core_obstruction (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) i (Classical.choice ((reduced_triple h).local_data (other i)))
    J hnpos hcard hconj
    (specialUnitaryEnlargementQuotient h (other i) _ J hnpos hcard hconj e)

/-- The three large nonlinear source rows discharge both obstructions with no opposite-endpoint restriction. -/
theorem reduced_large_nonlinear_adjacent_core_obstruction (h : HypothesisF11 L S) (i : Fin 2)
    (hmodel : (∃ m : ℕ, 0 < m ∧ Nonempty ((L (other i) ⧸ pCore 2 (L (other i))) ≃*
        SuzukiMatrixGroup m)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSU (L (other i) ⧸ pCore 2 (L (other i))) 3 (2^n)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ IsSU (L (other i) ⧸ pCore 2 (L (other i))) 3 (2^n))) :
    let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
    (¬ localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set (G₀ L S))) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))),
      (T : Subgroup (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))).map
        (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).subtype = (P i).pCoreIn 2 := by
  rcases hmodel with ⟨m,hm,⟨e⟩⟩ | ⟨n,hn,hm⟩ | ⟨n,hn,hm⟩
  · exact reduced_suzuki_adjacent_core_obstruction h i hm e
  · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
    let := hF
    let := hfin
    exact reduced_projective_unitary_adjacent_core_obstruction h i J hn hcard hconj e
  · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
    let := hF
    let := hfin
    exact reduced_special_unitary_adjacent_core_obstruction h i J hn hcard hconj e

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
theorem original_large_nonlinear_adjacent_core_obstruction (h : HypothesisF11 L S) (i : Fin 2)
    (hmodel : (∃ m : ℕ, 0 < m ∧ Nonempty ((L (other i) ⧸ pCore 2 (L (other i))) ≃*
        SuzukiMatrixGroup m)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSU (L (other i) ⧸ pCore 2 (L (other i))) 3 (2^n)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ IsSU (L (other i) ⧸ pCore 2 (L (other i))) 3 (2^n))) :
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
  obtain ⟨hn0,hs0⟩ := reduced_large_nonlinear_adjacent_core_obstruction h i hmodel
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

/-- The original large nonlinear quotient discharges the obstruction in the actual 6.6 center-product application. -/
theorem reduced_large_nonlinear_normal_center_product (h : HypothesisF11 L S) (j : Bool)
    (hmodel : (∃ m : ℕ, 0 < m ∧ Nonempty ((L (other (if j then 1 else 0)) ⧸ pCore 2 (L (other (if j then 1 else 0)))) ≃*
        SuzukiMatrixGroup m)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSU (L (other (if j then 1 else 0)) ⧸ pCore 2 (L (other (if j then 1 else 0)))) 3 (2^n)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ IsSU (L (other (if j then 1 else 0)) ⧸ pCore 2 (L (other (if j then 1 else 0)))) 3 (2^n)))
    (hn : stabilizer (reducedFamily L S) (base (reducedFamily L S) (!j)) ≤ normalizer
      (↑(Z (reducedFamily L S) (base (reducedFamily L S) j) ⊔
        Z (reducedFamily L S) (base (reducedFamily L S) (!j))) : Set (G₀ L S))) :
    (∀ T : Sylow 2 (stabilizer (reducedFamily L S) (base (reducedFamily L S) j)),
      Z (reducedFamily L S) (base (reducedFamily L S) j) = omegaCenterIn
        ((T : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) j))).map
          (stabilizer (reducedFamily L S) (base (reducedFamily L S) j)).subtype)) ∧
      Z (reducedFamily L S) (base (reducedFamily L S) j) ≤
        Z (reducedFamily L S) (base (reducedFamily L S) (!j)) := by
  have hadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) j)
      (base (reducedFamily L S) (!j)) :=
    ⟨by cases j <;> exact Bool.noConfusion,Subgroup.CosetGeometry.incident_base _ _ _⟩
  apply reduced_normal_center_product h hadj hn
  intro hh
  simp only [Q,stabilizer,Subgroup.CosetGeometry.stabilizer_base] at hh
  cases j
  · exact (reduced_large_nonlinear_adjacent_core_obstruction h 0 hmodel).1
      ((localEnlargement_le _).trans hh)
  · exact (reduced_large_nonlinear_adjacent_core_obstruction h 1 hmodel).1
      ((localEnlargement_le _).trans hh)
end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
