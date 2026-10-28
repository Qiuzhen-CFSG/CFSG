module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearObstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.RankOneOddTransport

/-!
# The linear 6.5 obstruction with unrestricted opposite endpoint

The replacement and central-center arguments use the marked linear quotient
at lambda. In the noncentral branch, odd transport at delta now comes from
its actual original starred model. The displacement core-pair contradiction
therefore applies to mixed orientations as well, including a degree-one
unitary opposite endpoint. Both the relative-normality and the full-endpoint
closure Sylow obstructions retain their original subgroups.

Source: DGS, Groups and Graphs (1985), 6.4--6.5, pp.120--122.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The noncentral linear branch, with every original opposite endpoint model allowed. -/
theorem source_linear_noncentral_obstruction_unrestricted_opposite (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (j : Bool) (d : LocalRankOneData (family P (!j)) B)
    (q : localEnlargement d →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d))
    (hnc : ¬ sylowCenterSpan (family P (!j)) ≤ centralizer
      (conjugateSpanBy ((family P j).pCoreIn 2) (family P (!j)) : Set G)) :
    (¬ localEnlargement d ≤ normalizer
      (↑((family P j).pCoreIn 2 ⊓ (family P (!j)).pCoreIn 2) : Set G)) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((family P j).pCoreIn 2) (family P (!j))),
      (T : Subgroup (conjugateSpanBy ((family P j).pCoreIn 2) (family P (!j)))).map
        (conjugateSpanBy ((family P j).pCoreIn 2) (family P (!j))).subtype = (family P j).pCoreIn 2 := by
  let := finite_endpoints h
  let A := (family P j).pCoreIn 2
  let U := sylowCenterSpan (family P (!j))
  let X := conjugateSpanBy A (family P (!j))
  let R := X.pCoreIn 2
  have hnot : ¬ localEnlargement d ≤ normalizer
      (↑((family P j).pCoreIn 2 ⊓ (family P (!j)).pCoreIn 2) : Set G) := by
    intro hn
    obtain ⟨_,mu,hm,_,hout⟩ := source_linear_escaping_neighbor h hB hS j d hn q hq hk hnc
    obtain ⟨x,hxP,hodd,hxm⟩ := source_rankOne_odd_neighbor_transport h j hm
    have hout' : ¬ U.map (MulAut.conj x).toMonoidHom ≤ R := by
      rw [←hxm,Z_translate] at hout
      simpa only [Z,Subgroup.CosetGeometry.stabilizer_base] using hout
    have hURomega : U ≤ omegaCenterIn R := by
      cases j
      · exact source_center_le_closure_core_omega h hB hS 0
      · exact source_center_le_closure_core_omega h hB hS 1
    have hUR : U ≤ R := hURomega.trans (map_subtype_le _)
    have hU : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le hURomega
    have hR : R = A ⊓ centralizer (U : Set G) := by
      cases j
      · exact (source_linear_neighbor_center_centralizer h hB hS 0 d hn q hq hk hnc).2.symm
      · exact (source_linear_neighbor_center_centralizer h hB hS 1 d hn q hq hk hnc).2.symm
    have hb : ∀ a ∈ A, a ∉ R → R.relIndex A ≤ (centralizer ({a} : Set G)).relIndex U := by
      cases j
      · exact source_linear_neighbor_center_displacement h hB hS 0 d hn q hq hk hnc
      · exact source_linear_neighbor_center_displacement h hB hS 1 d hn q hq hk hnc
    have hnR : family P (!j) ≤ normalizer (R : Set G) :=
      (le_normalizer_conjugateSpanBy A (family P (!j))).trans
        (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
    have hnU : family P (!j) ≤ normalizer (U : Set G) :=
      (normal_subgroupOf_iff_le_normalizer (sylowCenterSpan_le _)).mp (sylowCenterSpan_normal _)
    cases j
    · exact source_displacement_core_pair_obstruction h 0 R U hU hUR hR hb hnR hnU x hxP hodd hout'
    · exact source_displacement_core_pair_obstruction h 1 R U hU hUR hR hb hnR hnU x hxP hodd hout'
  refine ⟨hnot,?_⟩
  intro hs
  apply hnot
  have hAP : A ≤ family P (!j) := by
    have hBP : B ≤ family P (!j) := le_sup_right.trans d.supplement.le
    cases j
    · exact (source_core_le_borel (Classical.choice (h.local_data 0))).trans hBP
    · exact (source_core_le_borel (Classical.choice (h.local_data 1))).trans hBP
  have hXP : X ≤ family P (!j) := conjugateSpanBy_le_self hAP
  have hnX := le_normalizer_conjugateSpanBy A (family P (!j))
  obtain ⟨T,hT⟩ := hs
  have hc : A ⊓ (family P (!j)).pCoreIn 2 = X.pCoreIn 2 := by
    apply le_antisymm
    · exact (inf_le_inf_right _ (le_conjugateSpanBy _ _)).trans (inf_pCoreIn_le_of_le 2 hXP)
    · exact le_inf ((pCoreIn_le_sylow X T).trans_eq hT) (pCoreIn_mono_of_normalizes hXP hnX)
  change localEnlargement d ≤ normalizer (↑(A ⊓ (family P (!j)).pCoreIn 2) : Set G)
  rw [hc]
  exact (localEnlargement_le d).trans
    (hnX.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))


/-- Both 6.5 clauses from the marked linear neighboring quotient, with no restriction on the opposite endpoint. -/
theorem source_linear_obstruction_unrestricted_opposite (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (j : Bool) (d : LocalRankOneData (family P (!j)) B)
    (q : localEnlargement d →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d)) :
    (¬ localEnlargement d ≤ normalizer
      (↑((family P j).pCoreIn 2 ⊓ (family P (!j)).pCoreIn 2) : Set G)) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((family P j).pCoreIn 2) (family P (!j))),
      (T : Subgroup (conjugateSpanBy ((family P j).pCoreIn 2) (family P (!j)))).map
        (conjugateSpanBy ((family P j).pCoreIn 2) (family P (!j))).subtype = (family P j).pCoreIn 2 := by
  have hnot : ¬ localEnlargement d ≤ normalizer
      (↑((family P j).pCoreIn 2 ⊓ (family P (!j)).pCoreIn 2) : Set G) := by
    intro hn
    have hnc : ¬ sylowCenterSpan (family P (!j)) ≤ centralizer
        (conjugateSpanBy ((family P j).pCoreIn 2) (family P (!j)) : Set G) := by
      cases j
      · exact source_linear_neighbor_center_noncentral h hB hS 0 d hn q hq hk
      · exact source_linear_neighbor_center_noncentral h hB hS 1 d hn q hq hk
    exact (source_linear_noncentral_obstruction_unrestricted_opposite h hB hS j d q hq hk hnc).1 hn
  refine ⟨hnot, ?_⟩
  have hnfull : ¬ family P (!j) ≤ normalizer
      (↑((family P j).pCoreIn 2 ⊓ (family P (!j)).pCoreIn 2) : Set G) :=
    fun hn => hnot ((localEnlargement_le d).trans hn)
  cases j
  · exact core_not_sylow_of_inter_not_normal h 0 hnfull
  · exact core_not_sylow_of_inter_not_normal h 1 hnfull
end CFSG.Quasithin.ChapterF.Source.DGS85
