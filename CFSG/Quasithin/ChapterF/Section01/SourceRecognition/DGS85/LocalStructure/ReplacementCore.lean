module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CoreClosure
public import Theory.GroupTheory.PCoreCommutatorCentralizer

/-!
# The replacement span in both neighboring-center branches

Write X=<Q_delta^G_lambda> and D=Q_delta intersect Q_lambda. Under the
contrary relative normality, [O₂(X),X] lies in D. Characteristic two then
puts C_X(D) inside O₂(X). Since Z_delta centralizes D, it lies in
Q_delta intersect O₂(X), hence in D. Normality of D puts the literal
replacement span <Z_delta^X> in Ω₁Z(D), regardless of whether Z_lambda
centralizes X. No Sylow or quotient-model assumption is used.

This supplies the elementary-containment premise in the source replacement
argument, including the central neighboring-center case.
Source: DGS, Groups and Graphs (1985), 6.4, pp.120--121.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The common-core centralizer lies in the actual closure core, before Sylow recognition. -/
theorem source_inter_centralizer_le_closure_core (h : LocallyRankOneTriple P B) (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    X ⊓ centralizer ((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2 : Set G) ≤ X.pCoreIn 2 := by
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  let D := (P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2
  let := (Classical.choice (h.local_data (other i))).finite_P
  have hXP : X ≤ P (other i) := conjugateSpanBy_le_self
    ((source_core_le_borel (Classical.choice (h.local_data i))).trans
      (le_sup_right.trans (Classical.choice (h.local_data (other i))).supplement.le))
  let : Finite X := Finite.of_injective (inclusion hXP) (inclusion_injective _)
  let : (D.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer (hXP.trans hn)
  have hc : ⁅pCore 2 X, (⊤ : Subgroup X)⁆ ≤ D.subgroupOf X := by
    apply (map_le_iff_le_comap).mp
    rw [map_commutator, ←MonoidHom.range_eq_map, range_subtype]
    exact core_closure_core_commutator_le_inter h i hn
  have hh := centralizer_le_pCore_of_core_commutator (D.subgroupOf X)
    (core_closure_selfCentralizing h i) hc
  change X ⊓ centralizer (D : Set G) ≤ X.pCoreIn 2
  intro x hx
  exact mem_map_of_mem X.subtype (hh (show (⟨x,hx.1⟩ : X) ∈
    centralizer (D.subgroupOf X : Set X) from fun d hd => Subtype.ext (hx.2 d hd)))

/-- Contrary relative normality puts the opposite center in both cores in every branch. -/
theorem source_opposite_center_le_inter (h : LocallyRankOneTriple P B) (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    sylowCenterSpan (P i) ≤ (P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2 := by
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  have hZ := sylowCenterSpan_le_coreOmega _ (source_core_selfCentralizing
    (Classical.choice (h.local_data i)))
  have hZQ : sylowCenterSpan (P i) ≤ (P i).pCoreIn 2 := hZ.trans (map_subtype_le _)
  have hZC : sylowCenterSpan (P i) ≤ X ⊓ centralizer
      ((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2 : Set G) :=
    le_inf (hZQ.trans (le_conjugateSpanBy _ _)) (fun z hz =>
      centralizer_le inf_le_left ((mem_omegaCenterIn_iff _ _).mp (hZ hz)).2.1)
  have hXP : X ≤ P (other i) := conjugateSpanBy_le_self
    ((source_core_le_borel (Classical.choice (h.local_data i))).trans
      (le_sup_right.trans (Classical.choice (h.local_data (other i))).supplement.le))
  exact le_inf hZQ ((hZC.trans (source_inter_centralizer_le_closure_core h i hn)).trans
    (pCoreIn_mono_of_normalizes hXP (le_normalizer_conjugateSpanBy _ _)))

/-- The literal replacement span from printed 6.4 is elementary and lies
in the center omega of the original core intersection in both cases. -/
theorem source_replacement_span_le_inter_omega_of_inter_normal (h : LocallyRankOneTriple P B)
    (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    conjugateSpanBy (sylowCenterSpan (P i))
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))) ≤
        omegaCenterIn ((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) := by
  apply conjugateSpanBy_le
  · intro z hz
    obtain ⟨_,hc,hp⟩ := (mem_omegaCenterIn_iff _ _).mp
      (sylowCenterSpan_le_coreOmega _ (source_core_selfCentralizing
        (Classical.choice (h.local_data i))) hz)
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨source_opposite_center_le_inter h i hn hz,
        centralizer_le inf_le_left hc,hp⟩
  · exact ((conjugateSpanBy_le_self ((source_core_le_borel
      (Classical.choice (h.local_data i))).trans
        (le_sup_right.trans (Classical.choice (h.local_data (other i))).supplement.le))).trans hn).trans
        (normalizer_le_normalizer_omegaCenterIn _)

end CFSG.Quasithin.ChapterF.Source.DGS85
