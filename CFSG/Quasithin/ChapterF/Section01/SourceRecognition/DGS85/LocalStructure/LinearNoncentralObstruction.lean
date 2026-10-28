module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CorePairDisplacement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.NeighborEscapeApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.NeighborDisplacement

/-!
# Both adjacent-core obstructions in the noncentral linear branch

The actual escaping neighboring center and the opposite endpoint's
linear quotient supply an odd-order transporter. The faithful action
on that center supplies sharp displacement at every field size.
The general core-pair contradiction excludes relative normality of
the adjacent-core intersection. The proved Sylow-to-normality argument
then excludes Q_delta being Sylow in its closure as well.

The two endpoint fields are independent. Noncentrality is the remaining
source branch condition; no Frattini, displacement, or field-size premise
is left. The original F1.11 application is LinearNoncentralApplication.

Source: DGS, Groups and Graphs (1985), (6.5), pp.121--122. The central
case and general rank-one model selection are separate obligations.
-/


open Subgroup Theory.GroupTheory
open scoped MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]

/-- Both 6.5 clauses in the noncentral branch, for arbitrary marked linear endpoint fields. -/
theorem source_linear_noncentral_adjacent_core_obstruction (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (j : Bool) (d : LocalRankOneData (family P (!j)) B)
    (q : localEnlargement d →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d))
    (hnc : ¬ sylowCenterSpan (family P (!j)) ≤ centralizer
      (conjugateSpanBy ((family P j).pCoreIn 2) (family P (!j)) : Set G))
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
end CFSG.Quasithin.ChapterF.Source.DGS85
