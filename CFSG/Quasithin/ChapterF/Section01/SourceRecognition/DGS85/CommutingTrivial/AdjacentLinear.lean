module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReorientedConfiguration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearObstruction

/-!
# Source 6.5 from adjacent linear graph quotient markings

A common edge conjugator moves the two supplied markings to the two base
vertices. At either orientation, the intrinsic base local group equals
G* O₂(B). Its transported quotient equivalence constructs a surjective
SL₂ map with exactly the intrinsic two-core as kernel. The proved linear
6.5 theorem therefore forbids normalization of the adjacent-core
intersection by the local enlargement, hence by the full stabilizer.
A second common edge conjugator transports this obstruction to every edge.

The markings concern actual graph local groups. No reversal of the
original-to-reduced quotient map or comparison of the fields is used.
LinearApplications applies the result to both Chapter 9 natural sections.
Source: DGS, Groups and Graphs (1985), 6.5, pp.121--122; 9.3--9.4,
pp.142--143.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]

private theorem marked_base_obstruction (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (j : Bool)
    (e : (graphLocalGroup (family P) (base (family P) (!j)) ⧸
      pCore 2 (graphLocalGroup (family P) (base (family P) (!j)))) ≃* SL(2,F))
    (eδ : (graphLocalGroup (family P) (base (family P) j) ⧸
      pCore 2 (graphLocalGroup (family P) (base (family P) j))) ≃* SL(2,K)) :
    ¬ stabilizer (family P) (base (family P) (!j)) ≤ normalizer
      ((Q (family P) (base (family P) j) ⊓ Q (family P) (base (family P) (!j)) :
        Subgroup G) : Set G) := by
  have hd : Nonempty (LocalRankOneData (family P (!j)) B) := by
    cases j
    · exact h.local_data 1
    · exact h.local_data 0
  let d := Classical.choice hd
  let c := MulEquiv.subgroupCongr (graphLocalGroup_base_eq hB hS (!j) d).symm
  let f := (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans e
  let q := f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localEnlargement d)))
  have hq : Function.Surjective q := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 (localEnlargement d) := by
    rw [MonoidHom.ker_comp_of_injective _ _ f.injective,QuotientGroup.ker_mk']
  intro hn
  simp only [Q,stabilizer,Subgroup.CosetGeometry.stabilizer_base] at hn
  exact (source_linear_adjacent_core_obstruction h hB hS j d q hq hk eδ).1
    ((localEnlargement_le d).trans hn)

private theorem marked_base_obstructions (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (j : Bool)
    (e : (graphLocalGroup (family P) (base (family P) j) ⧸
      pCore 2 (graphLocalGroup (family P) (base (family P) j))) ≃* SL(2,F))
    (eδ : (graphLocalGroup (family P) (base (family P) (!j)) ⧸
      pCore 2 (graphLocalGroup (family P) (base (family P) (!j)))) ≃* SL(2,K)) :
    (¬ stabilizer (family P) (base (family P) j) ≤ normalizer
      ((Q (family P) (base (family P) (!j)) ⊓ Q (family P) (base (family P) j) :
        Subgroup G) : Set G)) ∧
    (¬ stabilizer (family P) (base (family P) (!j)) ≤ normalizer
      ((Q (family P) (base (family P) j) ⊓ Q (family P) (base (family P) (!j)) :
        Subgroup G) : Set G)) := by
  cases j
  · exact ⟨marked_base_obstruction h hB hS true e eδ,
      marked_base_obstruction h hB hS false eδ e⟩
  · exact ⟨marked_base_obstruction h hB hS false e eδ,
      marked_base_obstruction h hB hS true eδ e⟩

/-- Supplied linear markings at two incident vertices discharge source 6.5
at every edge, without an original-endpoint marking or field comparison. -/
theorem adjacent_linear_graph_core_obstruction (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    (eα : (graphLocalGroup (family P) a ⧸ pCore 2 (graphLocalGroup (family P) a)) ≃* SL(2,F))
    (eβ : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,K))
    (v w : Vertex (family P)) (hvw : (graph (family P)).Adj v w) :
    ¬ stabilizer (family P) v ≤ normalizer
      ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G) := by
  obtain ⟨g,ha,hbeta⟩ := incident_common_translate (family P) hab.2
  obtain ⟨_,fα,_,_,_⟩ := local_quotient_parameter_transport h g ha
  obtain ⟨_,fβ,_,_,_⟩ := local_quotient_parameter_transport h g hbeta
  have ht : beta.type = !a.type := Bool.eq_not_of_ne hab.1.symm
  have eβ₀ : (graphLocalGroup (family P) (base (family P) (!a.type)) ⧸
      pCore 2 (graphLocalGroup (family P) (base (family P) (!a.type)))) ≃* SL(2,K) := by
    rw [←ht]
    exact fβ.trans eβ
  have hb (j : Bool) : ¬ stabilizer (family P) (base (family P) j) ≤ normalizer
      ((Q (family P) (base (family P) (!j)) ⊓ Q (family P) (base (family P) j) :
        Subgroup G) : Set G) := by
    have hh := marked_base_obstructions h hB hS a.type (fα.trans eα) eβ₀
    by_cases hj : j = a.type
    · subst j
      exact hh.1
    · have hj' : j = !a.type := Bool.eq_not_of_ne hj
      rw [hj',Bool.not_not]
      exact hh.2
  obtain ⟨k,hv,hw⟩ := incident_common_translate (family P) hvw.2
  have htw : w.type = !v.type := Bool.eq_not_of_ne hvw.1.symm
  intro hn
  rw [←hv,←hw,Q_translate,Q_translate,stabilizer_translate,
    ←Subgroup.map_inf _ _ _ (MulAut.conj k).injective,←map_equiv_normalizer_eq] at hn
  have hn' := (map_le_map_iff_of_injective (MulAut.conj k).injective).mp hn
  rw [htw] at hn'
  exact hb v.type hn'
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
