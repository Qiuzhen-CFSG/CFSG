module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.BinaryCorePair
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.BinaryEscapeApplication

/-!
# DGS 6.5 for a binary neighboring linear quotient

The binary central-case exclusion and the escape theorem supply the actual
neighboring center outside the closure core. The other endpoint's linear
quotient supplies an odd transporter to that neighbor. The index-two
centralizer-pair contradiction then removes the contrary normality, with
no noncentrality or Frattini premise remaining. The original core cannot
be Sylow in its closure either, by the proved first implication of 6.5.

The fields at the two endpoints need not agree. Only the neighboring field
has order two. Source: DGS, Groups and Graphs (1985), 6.5, pp.121--122.
-/
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]

/-- Both clauses of 6.5 at the base edge, when the neighboring quotient is binary and the first quotient is linear. -/
theorem source_binary_adjacent_core_obstruction (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (j : Bool) (d : LocalRankOneData (family P (!j)) B)
    (q : localEnlargement d →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d)) (hF : Nat.card F = 2)
    (eδ : (graphLocalGroup (family P) (base (family P) j) ⧸
      pCore 2 (graphLocalGroup (family P) (base (family P) j))) ≃* SL(2,K)) :
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
  have hadj : (graph (family P)).Adj (base (family P) j) (base (family P) (!j)) :=
    ⟨by cases j <;> exact Bool.noConfusion,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hnot : ¬ localEnlargement d ≤ normalizer
      (↑((family P j).pCoreIn 2 ⊓ (family P (!j)).pCoreIn 2) : Set G) := by
    intro hn
    have hnc : ¬ U ≤ centralizer (X : Set G) := by
      cases j
      · exact source_binary_neighbor_center_noncentral h hB hS 0 d hn q hq hk hF
      · exact source_binary_neighbor_center_noncentral h hB hS 1 d hn q hq hk hF
    obtain ⟨_,mu,hm,_,hout⟩ := source_linear_escaping_neighbor h hB hS j d hn q hq hk hnc
    obtain ⟨x,hx,hodd,hxm⟩ := source_linear_odd_neighbor_transport_of_quotient h hB hS hadj hm eδ
    have hxP : x ∈ family P j := by
      have hh := sylowGenerated_le (stabilizer (family P) (base (family P) j)) hx
      simpa only [Subgroup.CosetGeometry.stabilizer_base] using hh
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
    have hi : R.relIndex A = 2 := by
      cases j
      · exact (source_linear_closure_core_relIndex h hB hS 0 d hn q hq hk).trans hF
      · exact (source_linear_closure_core_relIndex h hB hS 1 d hn q hq hk).trans hF
    have hnR : family P (!j) ≤ normalizer (R : Set G) :=
      (le_normalizer_conjugateSpanBy A (family P (!j))).trans
        (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
    have hnU : family P (!j) ≤ normalizer (U : Set G) :=
      (normal_subgroupOf_iff_le_normalizer (sylowCenterSpan_le _)).mp (sylowCenterSpan_normal _)
    cases j
    · exact source_index_two_core_pair_obstruction h 0 R U hU hUR hR hi hnR hnU x hxP hodd hout'
    · exact source_index_two_core_pair_obstruction h 1 R U hU hUR hR hi hnR hnU x hxP hodd hout'
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
end CFSG.Quasithin.ChapterF.Source.DGS85
