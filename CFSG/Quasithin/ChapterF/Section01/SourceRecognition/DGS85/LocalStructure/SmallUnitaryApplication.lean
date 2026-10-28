module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallUnitaryObstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.BinaryObstructionApplication

/-!
# Degree-one unitary enlarged quotients on the original F.1.1 cores

The literal inclusion of the reduced enlargement into the original
completion gives the quotient marking used by the small-unitary
obstruction. Injective transport then proves both 6.5 conclusions for
the original parabolic cores and their closure under the full endpoint.
The same obstruction discharges the 6.6 center-product application.

The enlarged quotient, rather than the original local quotient, is
marked here. Producing this marking from original Hypothesis F.1.1 is
the remaining degree-one 6.1 obligation. Neither solvability nor an
assumed obstruction is used to discard the small rows.
Source: DGS, Groups and Graphs (1985), reduction p.95 and 6.4--6.6,
pp.120--123; Aschbacher--Smith F.1.9, pp.261--262.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G]
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Transport the actual original enlarged quotient to the reduced endpoint and apply both 6.5 clauses. -/
theorem reduced_small_unitary_enlargement_obstruction (h : HypothesisF11 L S) (i : Fin 2)
    (hm : ClassicalGroup.IsPSU (enlargedEndpoint L S (other i) ⧸
        pCore 2 (enlargedEndpoint L S (other i))) 3 2 ∨
      IsSU (enlargedEndpoint L S (other i) ⧸ pCore 2 (enlargedEndpoint L S (other i))) 3 2) :
    let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
    (¬ localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set (G₀ L S))) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))),
      (T : Subgroup (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))).map
        (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).subtype = (P i).pCoreIn 2 := by
  let d := Classical.choice ((reduced_triple h).local_data (other i))
  let e := ((localEnlargement d).equivMapOfInjective (G₀ L S).subtype
    (G₀ L S).subtype_injective).trans
      (MulEquiv.subgroupCongr (reduced_localEnlargement_image h (other i) d))
  let eQ := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  apply source_small_unitary_adjacent_core_obstruction (reduced_triple h) (reduced_borel_core_sylow h) i d
  rcases hm with hm | hm
  · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨f⟩⟩ := hm
    exact Or.inl ⟨F,hF,hfin,J,hcard,hconj,⟨eQ.trans f⟩⟩
  · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨f⟩⟩ := hm
    exact Or.inr ⟨F,hF,hfin,J,hcard,hconj,⟨eQ.trans f⟩⟩
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
theorem original_small_unitary_enlargement_obstruction (h : HypothesisF11 L S) (i : Fin 2)
    (hmodel : ClassicalGroup.IsPSU (enlargedEndpoint L S (other i) ⧸
        pCore 2 (enlargedEndpoint L S (other i))) 3 2 ∨
      IsSU (enlargedEndpoint L S (other i) ⧸ pCore 2 (enlargedEndpoint L S (other i))) 3 2) :
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
  obtain ⟨hn0,hs0⟩ := reduced_small_unitary_enlargement_obstruction h i hmodel
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

/-- The actual 6.6 center-product application, retaining the outstanding degree-one enlarged marking. -/
theorem reduced_small_unitary_enlargement_center_product (h : HypothesisF11 L S) (j : Bool)
    (hm : ClassicalGroup.IsPSU
        (enlargedEndpoint L S (other (if j then 1 else 0)) ⧸
          pCore 2 (enlargedEndpoint L S (other (if j then 1 else 0)))) 3 2 ∨
      IsSU (enlargedEndpoint L S (other (if j then 1 else 0)) ⧸
          pCore 2 (enlargedEndpoint L S (other (if j then 1 else 0)))) 3 2)
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
  · exact (reduced_small_unitary_enlargement_obstruction h 0 hm).1
      ((localEnlargement_le _).trans hh)
  · exact (reduced_small_unitary_enlargement_obstruction h 1 hm).1
      ((localEnlargement_le _).trans hh)
end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
