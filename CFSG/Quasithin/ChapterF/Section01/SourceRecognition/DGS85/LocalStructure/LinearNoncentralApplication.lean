module
public import Theory.GroupTheory.AmalgamGraph.SylowCenterEmbedding
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearNoncentralObstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.BinaryObstructionApplication

/-!
# The noncentral linear obstruction in the original F1.11 amalgam

The original quotient markings construct both reduced linear actions.
The proved noncentral (6.5) branch applies to the actual reduced graph,
and its (6.6) normal-center-product consumer has its obstruction premise
discharged. Injective transport preserves the reduced Sylow-center span
and identifies the closure image with closure under the original full
endpoint, giving both obstructions on the original parabolic cores.

The full Borel, original S, reduced Borel and reduced completion retain
their literal definitions and maps. The original noncentrality condition
uses the Sylow-center span of the reduced endpoint inside the original
group. The field orders are unrestricted and may differ.

Source: DGS, Groups and Graphs (1985), reduction p.95 and (6.5)--(6.6),
pp.121--123; Aschbacher--Smith F.1.9, pp.261--262. Larger-field central
exclusion and general model selection are not asserted here.
-/


open Subgroup Theory.GroupTheory
open scoped MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]

/-- The original linear markings discharge the 6.4 premises in the noncentral reduced 6.5 branch. -/
theorem reduced_linear_noncentral_adjacent_core_obstruction (h : HypothesisF11 L S) (i : Fin 2)
    (e : (L (other i) ⧸ pCore 2 (L (other i))) ≃* PSL(2,F))
    (eδ : (L i ⧸ pCore 2 (L i)) ≃* PSL(2,K))
    (hnc : ¬ sylowCenterSpan ((P₀ L S (other i)).subgroupOf (G₀ L S)) ≤ centralizer
      (conjugateSpanBy (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)
        ((P₀ L S (other i)).subgroupOf (G₀ L S)) : Set (G₀ L S))) :
    let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
    (¬ localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set (G₀ L S))) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))),
      (T : Subgroup (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))).map
        (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).subtype = (P i).pCoreIn 2 := by
  let d := Classical.choice ((reduced_triple h).local_data (other i))
  let f := reduced_linearEnlargementQuotient h (other i) d e
  let q := f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localEnlargement d)))
  have hq : Function.Surjective q := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 (localEnlargement d) := by
    rw [MonoidHom.ker_comp_of_injective _ _ f.injective,QuotientGroup.ker_mk']
  let eSL : SL(2,K) ≃* PSL(2,K) := MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
    ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  fin_cases i
  · exact source_linear_noncentral_adjacent_core_obstruction (reduced_triple h) (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) false d q hq hk hnc ((reduced_graphLinearQuotient h false eδ).trans eSL.symm)
  · exact source_linear_noncentral_adjacent_core_obstruction (reduced_triple h) (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) true d q hq hk hnc ((reduced_graphLinearQuotient h true eδ).trans eSL.symm)

private theorem reduced_endpoint_le_generated (i : Fin 2) : P₀ L S i ≤ G₀ L S := by
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

private theorem reduced_core_image (h : HypothesisF11 L S) (i : Fin 2) :
    (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2).map (G₀ L S).subtype =
      (parabolic L S i).pCoreIn 2 := by
  rw [map_pCoreIn_of_injective 2 _ _ (G₀ L S).subtype_injective,
    map_subgroupOf_eq_of_le (reduced_endpoint_le_generated i),P₀_core h i]

/-- The noncentral branch gives both obstructions on the original parabolic cores and full-endpoint closure. -/
theorem original_linear_noncentral_adjacent_core_obstruction (h : HypothesisF11 L S) (i : Fin 2)
    (e : (L (other i) ⧸ pCore 2 (L (other i))) ≃* PSL(2,F))
    (eδ : (L i ⧸ pCore 2 (L i)) ≃* PSL(2,K))
    (hnc : ¬ sylowCenterSpan (P₀ L S (other i)) ≤ centralizer
      (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i)) : Set G)) :
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
  have hnc0 : ¬ sylowCenterSpan (P (other i)) ≤ centralizer
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) : Set (G₀ L S)) := by
    intro hz
    apply hnc
    have hZ : (sylowCenterSpan (P (other i))).map (G₀ L S).subtype =
        sylowCenterSpan (P₀ L S (other i)) := by
      rw [←sylowCenterSpan_map_of_injective _ (G₀ L S).subtype_injective _,
        map_subgroupOf_eq_of_le (reduced_endpoint_le_generated (other i))]
    intro z hz0 x hx0
    obtain ⟨z',hz',rfl⟩ := hZ.symm ▸ hz0
    obtain ⟨x',hx',rfl⟩ := (reduced_core_closure_full_image h i).symm ▸ hx0
    exact congrArg (G₀ L S).subtype (hz hz' x' hx')
  obtain ⟨hn0,hs0⟩ := reduced_linear_noncentral_adjacent_core_obstruction h i e eδ hnc0
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

/-- Source 6.6 on the actual reduced linear edge, with its noncentral 6.5 obstruction discharged. -/
theorem reduced_linear_noncentral_normal_center_product (h : HypothesisF11 L S) (j : Bool)
    (e : (L (other (if j then 1 else 0)) ⧸ pCore 2 (L (other (if j then 1 else 0)))) ≃* PSL(2,F))
    (eδ : (family L j ⧸ pCore 2 (family L j)) ≃* PSL(2,K))
    (hnc : ¬ Z (reducedFamily L S) (base (reducedFamily L S) (!j)) ≤ centralizer
      (conjugateSpanBy (Q (reducedFamily L S) (base (reducedFamily L S) j))
        (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!j))) : Set (G₀ L S)))
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
  simp only [Z,Q,stabilizer,Subgroup.CosetGeometry.stabilizer_base] at hnc
  cases j
  · exact (reduced_linear_noncentral_adjacent_core_obstruction h 0 e eδ hnc).1
      ((localEnlargement_le _).trans hh)
  · exact (reduced_linear_noncentral_adjacent_core_obstruction h 1 e eδ hnc).1
      ((localEnlargement_le _).trans hh)
end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
