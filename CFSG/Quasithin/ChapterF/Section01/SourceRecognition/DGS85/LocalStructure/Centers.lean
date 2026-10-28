module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LocalTransitivity
public import Theory.GroupTheory.AmalgamGraph.Centralizer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.CoreIntersections

/-!
# Local center centralizers and normal adjacent center products

The finite primitive local pair gives DGS 6.2(c): the actual vertex two-core
is Sylow in the full vertex centralizer of Z, or Z is every Sylow omega-center.
A common edge Sylow turns the latter alternative into containment in the
neighboring Z. The two-orbit critical minimum then excludes this alternative
at a critical starting vertex, proving 3.8(d) and its centralizer-Sylow consequence.

The actual reduced F1.11 applications discharge the 6.2(c,d) premises in the
branch owner's opening-7.1 intersection and reverse-escape lemmas. The 6.6
center-product deduction is also proved, conditional only on the still-open
6.5 adjacent-core obstruction. Adjacent centers normalize each other, so the
join in that statement is proved to be the literal source product. All
normality is relative to the stated vertex stabilizer; the ambient completion
need not be finite, and Q is never identified with the full local kernel U.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, 3.8(d), p.83; 6.2(c), p.119; 6.6, p.123; opening of 7.1, p.126.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The vertex Sylow markings transport with the entire incident edge. -/
theorem source_edge_vertex_sylow (h : LocallyRankOneTriple P B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w) :
    ∃ T : Sylow 2 (stabilizer (family P) v),
      (T : Subgroup (stabilizer (family P) v)).map (stabilizer (family P) v).subtype ≤
        stabilizer (family P) v ⊓ stabilizer (family P) w := by
  let := finite_endpoints h
  obtain ⟨g, hP, hE⟩ := source_edge_transport h hvw
  have hs : ∃ T : Sylow 2 (family P v.type),
      (T : Subgroup (family P v.type)).map (family P v.type).subtype ≤ B := by
    cases ht : v.type
    · exact hS 0
    · exact hS 1
  rw [hE, hP]
  obtain ⟨T, hT⟩ := hs
  obtain ⟨R, hR⟩ := sylow_witness_map (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    (family P v.type) ((T : Subgroup (family P v.type)).map (family P v.type).subtype) ⟨T, rfl⟩
  exact ⟨R, hR.le.trans (map_mono hT)⟩

/-- Characteristic two holds in every actual vertex stabilizer. -/
theorem source_vertex_core_selfCentralizing (h : LocallyRankOneTriple P B)
    (v : Vertex (family P)) :
    centralizer (pCore 2 (stabilizer (family P) v) : Set (stabilizer (family P) v)) ≤
      pCore 2 (stabilizer (family P) v) := by
  let := finite_endpoints h
  obtain ⟨g, hg⟩ := Subgroup.CosetGeometry.exists_smul_base (family P) v
  rw [← hg, stabilizer_translate]
  rw [show stabilizer (family P) (base (family P) v.type) = family P v.type from
    Subgroup.CosetGeometry.stabilizer_base _ _]
  change centralizer (pCore 2 ((family P v.type).map (MulAut.conj g).toMonoidHom) :
    Set ((family P v.type).map (MulAut.conj g).toMonoidHom)) ≤ _
  apply (Theory.Quasithin.centralizer_pCore_le_iff 2
    ((family P v.type).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)).mp
  cases ht : v.type
  · exact source_core_selfCentralizing (Classical.choice (h.local_data 0))
  · exact source_core_selfCentralizing (Classical.choice (h.local_data 1))

/-- Source 6.2(c), in the full vertex centralizer and for every Sylow. -/
theorem source_centralizer_sylow_or_Z_eq (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w) :
    (∃ T : Sylow 2 (stabilizer (family P) v ⊓ centralizer (Z (family P) v : Set G) : Subgroup G),
      (T : Subgroup (stabilizer (family P) v ⊓ centralizer (Z (family P) v : Set G) : Subgroup G)).map
        (stabilizer (family P) v ⊓ centralizer (Z (family P) v : Set G)).subtype = Q (family P) v) ∨
    ∀ T : Sylow 2 (stabilizer (family P) v),
      Z (family P) v = omegaCenterIn ((T : Subgroup (stabilizer (family P) v)).map
        (stabilizer (family P) v).subtype) := by
  let := finite_endpoints h
  exact centralizer_sylow_or_span_eq (stabilizer (family P) v)
    (stabilizer (family P) v ⊓ stabilizer (family P) w) inf_le_left
    (source_edge_maximal h hvw) (source_edge_core_sylow h hB hvw)
    (source_edge_vertex_sylow h hS hvw) (source_vertex_core_selfCentralizing h v)

/-- Collapse to one Sylow omega-center places Z in the neighboring Z. -/
theorem source_Z_le_neighbor_of_eq_seeds (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (he : ∀ T : Sylow 2 (stabilizer (family P) v),
      Z (family P) v = omegaCenterIn ((T : Subgroup (stabilizer (family P) v)).map
        (stabilizer (family P) v).subtype)) : Z (family P) v ≤ Z (family P) w := by
  let := finite_endpoints h
  let E := stabilizer (family P) v ⊓ stabilizer (family P) w
  obtain ⟨T, hT⟩ := source_edge_vertex_sylow h hS hvw
  obtain ⟨R, hR⟩ := source_edge_vertex_sylow h hS hvw.symm
  have hET := sylow_image_eq_edge_core (stabilizer (family P) v) E inf_le_left
    (source_edge_core_sylow h hB hvw) T hT
  have hER := sylow_image_eq_edge_core (stabilizer (family P) w) E inf_le_right
    (source_edge_core_sylow h hB hvw) R (by simpa only [E, inf_comm] using hR)
  rw [he T, hET, ← hER]
  exact le_iSup (fun R : Sylow 2 (stabilizer (family P) w) =>
    omegaCenterIn ((R : Subgroup (stabilizer (family P) w)).map
      (stabilizer (family P) w).subtype)) R

/-- Source 3.8(d): a critical starting center cannot be one Sylow omega-center. -/
theorem source_critical_Z_ne_seed (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (T : Sylow 2 (stabilizer (family P) v)) :
    Z (family P) v ≠ omegaCenterIn ((T : Subgroup (stabilizer (family P) v)).map
      (stabilizer (family P) v).subtype) := by
  let := finite_endpoints h
  intro he
  have hvw : w ≠ v := by
    intro hh
    subst w
    have hz := (source_Z_Q_U h v).1.trans ((map_subtype_le _).trans (source_Z_Q_U h v).2)
    exact hc.2 hz
  obtain ⟨x, hx, hd⟩ := exists_predecessor (family P) h.generate w v hvw
  have hzx : Z (family P) v ≤ Z (family P) x :=
    source_Z_le_neighbor_of_eq_seeds h hB hS hx
      (sylowCenterSpan_eq_all_seeds_of_eq _ T he)
  apply hc.2
  apply hzx.trans (Z_le_U_of_dist_lt_b (family P) x w _)
  have hdist := hc.1
  rw [SimpleGraph.dist_comm (u := w) (v := v), SimpleGraph.dist_comm (u := w) (v := x)] at hd
  omega

/-- At the critical starting vertex, 3.8(d) removes the second 6.2(c) alternative. -/
theorem source_critical_centralizer_sylow (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hc : IsCriticalPair (family P) v w) :
    ∃ T : Sylow 2 (stabilizer (family P) v ⊓ centralizer (Z (family P) v : Set G) : Subgroup G),
      (T : Subgroup (stabilizer (family P) v ⊓ centralizer (Z (family P) v : Set G) : Subgroup G)).map
        (stabilizer (family P) v ⊓ centralizer (Z (family P) v : Set G)).subtype = Q (family P) v := by
  let := finite_endpoints h
  obtain ⟨g, hg⟩ := Subgroup.CosetGeometry.exists_smul_base (family P) v
  have hadj : (graph (family P)).Adj v (g • base (family P) (!v.type)) := by
    rw [← hg]
    exact (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr
      ⟨by change v.type ≠ !v.type; cases v.type <;> decide,
        Subgroup.CosetGeometry.incident_base _ _ _⟩
  rcases source_centralizer_sylow_or_Z_eq h hB hS hadj with hs | he
  · exact hs
  · obtain ⟨T⟩ := Sylow.nonempty (p := 2) (G := stabilizer (family P) v)
    exact (source_critical_Z_ne_seed h hB hS hc T (he T)).elim

/-- Literal opening-7.1 application: every two-subgroup in the critical vertex
has the same intersection with its center centralizer and its actual core. -/
theorem source_critical_inf_centralizer (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (A : Subgroup G) (hA : IsPGroup 2 A) (hAP : A ≤ stabilizer (family P) v) :
    A ⊓ centralizer (Z (family P) v : Set G) = A ⊓ Q (family P) v := by
  have hQC : Q (family P) v ≤ centralizer (Z (family P) v : Set G) := by
    rw [le_centralizer_iff]
    exact (source_Z_Q_U h v).1.trans (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1)
  exact Noncommuting.inf_centralizer_eq_inf_core (stabilizer (family P) v) (Q (family P) v)
    (Z (family P) v) A hA hAP (pCoreIn_le 2 _) hQC
    ((stabilizer (family P) v).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer (family P) v))))
    (source_critical_centralizer_sylow h hB hS hc)

/-- The literal opening of DGS7.1: a noncommuting critical pair is critical
in both directions, and both centralizer intersections are the corresponding
core intersections. Both 6.2(c) and 6.2(d) premises are discharged here. -/
theorem source_noncommuting_critical_intersections (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v, Z (family P) w⁆ ≠ ⊥) :
    IsCriticalPair (family P) w v ∧
      Z (family P) w ⊓ centralizer (Z (family P) v : Set G) = Z (family P) w ⊓ Q (family P) v ∧
      Z (family P) v ⊓ centralizer (Z (family P) w : Set G) = Z (family P) v ⊓ Q (family P) w := by
  let := finite_endpoints h
  have hp (x : Vertex (family P)) : IsPGroup 2 (Z (family P) x) :=
    (isPGroup_pCoreIn 2 _).of_injective
      (inclusion ((source_Z_Q_U h x).1.trans (map_subtype_le _))) (inclusion_injective _)
  have hQC : Q (family P) v ≤ centralizer (Z (family P) v : Set G) := by
    rw [le_centralizer_iff]
    exact (source_Z_Q_U h v).1.trans
      (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1)
  have he := Noncommuting.not_le_kernel_of_noncommuting (Z (family P) v) (Z (family P) w)
    (U (family P) v) (Q (family P) v) (hp w) (source_Z_Q_U h v).2
    ((U_le_stabilizer (family P) v).trans ((stabilizer (family P) v).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer (family P) v)))))
    (source_kernel_sylow h hB hS v) hQC hne
  have hc' : IsCriticalPair (family P) w v := ⟨SimpleGraph.dist_comm.trans hc.1, he⟩
  exact ⟨hc', source_critical_inf_centralizer h hB hS hc _ (hp w)
    (criticalPair_centers (family P) h.generate hc).1,
    source_critical_inf_centralizer h hB hS hc' _ (hp v)
      (criticalPair_centers (family P) h.generate hc').1⟩

/-- Adjacent centers normalize each other, so their join is the source's
literal subgroup product even in the noncommuting branch. -/
theorem source_adjacent_center_product (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w) :
    (↑(Z (family P) v ⊔ Z (family P) w) : Set G) =
      (Z (family P) v : Set G) * (Z (family P) w : Set G) := by
  let := finite_endpoints h
  apply coe_mul_of_left_le_normalizer_right
  have hzv : Z (family P) v ≤ stabilizer (family P) w :=
    (source_Z_Q_U h v).1.trans ((map_subtype_le _).trans
      ((source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge (family P) hvw).trans inf_le_right)))
  exact hzv.trans ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer (family P) w)).mp
    (Z_normal (family P) w))

/-- Source 6.6 from the earlier 6.5 obstruction: a normal product of adjacent
centers forces the first center to be a Sylow omega-center and to lie in the
second. The 6.2(c) Sylow alternative is proved here, not an additional premise. -/
theorem source_normal_center_product (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hn : stabilizer (family P) w ≤ normalizer ((Z (family P) v ⊔ Z (family P) w : Subgroup G) : Set G))
    (hnot : ¬ stabilizer (family P) w ≤ normalizer ((Q (family P) v ⊓ Q (family P) w : Subgroup G) : Set G)) :
    (∀ T : Sylow 2 (stabilizer (family P) v),
      Z (family P) v = omegaCenterIn ((T : Subgroup (stabilizer (family P) v)).map
        (stabilizer (family P) v).subtype)) ∧ Z (family P) v ≤ Z (family P) w := by
  let := finite_endpoints h
  rcases source_centralizer_sylow_or_Z_eq h hB hS hvw with hs | he
  · exfalso
    have hQC (x : Vertex (family P)) : Q (family P) x ≤ centralizer (Z (family P) x : Set G) := by
      rw [le_centralizer_iff]
      exact (source_Z_Q_U h x).1.trans
        (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1)
    have hnQ (x : Vertex (family P)) : stabilizer (family P) x ≤ normalizer (Q (family P) x : Set G) :=
      (stabilizer (family P) x).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer (family P) x)))
    have hQwv : Q (family P) w ≤ stabilizer (family P) v :=
      (source_Z_Q_U h w).2.trans ((ballKernel_one_le_edge (family P) hvw.symm).trans inf_le_right)
    have hi := Noncommuting.inf_centralizer_eq_inf_core (stabilizer (family P) v)
      (Q (family P) v) (Z (family P) v) (Q (family P) w) (isPGroup_pCoreIn 2 _)
      hQwv (pCoreIn_le 2 _) (hQC v) (hnQ v) hs
    have he : Q (family P) w ⊓ centralizer (Z (family P) v : Set G) =
        Q (family P) w ⊓ centralizer ((Z (family P) v ⊔ Z (family P) w : Subgroup G) : Set G) := by
      apply le_antisymm
      · apply le_inf inf_le_left
        rw [le_centralizer_iff]
        apply sup_le
        · exact le_centralizer_iff.mp inf_le_right
        · exact (le_centralizer_iff.mp (hQC w)).trans (centralizer_le inf_le_left)
      · exact inf_le_inf_left _ (centralizer_le (show Z (family P) v ≤ Z (family P) v ⊔ Z (family P) w from le_sup_left))
    apply hnot
    rw [inf_comm, ← hi, he]
    exact (le_inf (hnQ w) (hn.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  · exact ⟨he, source_Z_le_neighbor_of_eq_seeds h hB hS hvw he⟩

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Unconditional 6.2(c) on the actual reduced F1.11 graph. -/
theorem reduced_centralizer_sylow_or_Z_eq (h : HypothesisF11 L S)
    {v w : Vertex (reducedFamily L S)} (hvw : (graph (reducedFamily L S)).Adj v w) :
    (∃ T : Sylow 2 (stabilizer (reducedFamily L S) v ⊓
        centralizer (Z (reducedFamily L S) v : Set (G₀ L S)) : Subgroup (G₀ L S)),
      (T : Subgroup (stabilizer (reducedFamily L S) v ⊓
        centralizer (Z (reducedFamily L S) v : Set (G₀ L S)) : Subgroup (G₀ L S))).map
        (stabilizer (reducedFamily L S) v ⊓
          centralizer (Z (reducedFamily L S) v : Set (G₀ L S))).subtype = Q (reducedFamily L S) v) ∨
    ∀ T : Sylow 2 (stabilizer (reducedFamily L S) v),
      Z (reducedFamily L S) v = omegaCenterIn ((T : Subgroup (stabilizer (reducedFamily L S) v)).map
        (stabilizer (reducedFamily L S) v).subtype) :=
  source_centralizer_sylow_or_Z_eq (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hvw

/-- Actual reduced F1.11 application discharging the critical-centralizer
Sylow premise used in the opening of Chapter 7. -/
theorem reduced_critical_inf_centralizer (h : HypothesisF11 L S)
    {v w : Vertex (reducedFamily L S)} (hc : IsCriticalPair (reducedFamily L S) v w)
    (A : Subgroup (G₀ L S)) (hA : IsPGroup 2 A) (hAP : A ≤ stabilizer (reducedFamily L S) v) :
    A ⊓ centralizer (Z (reducedFamily L S) v : Set (G₀ L S)) = A ⊓ Q (reducedFamily L S) v :=
  source_critical_inf_centralizer (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hc A hA hAP
/-- Actual reduced F1.11 application of the opening Chapter 7 identities,
without residual, Sylow-centralizer or kernel-Sylow callbacks. -/
theorem reduced_noncommuting_critical_intersections (h : HypothesisF11 L S)
    {v w : Vertex (reducedFamily L S)} (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v, Z (reducedFamily L S) w⁆ ≠ ⊥) :
    IsCriticalPair (reducedFamily L S) w v ∧
      Z (reducedFamily L S) w ⊓ centralizer (Z (reducedFamily L S) v : Set (G₀ L S)) =
        Z (reducedFamily L S) w ⊓ Q (reducedFamily L S) v ∧
      Z (reducedFamily L S) v ⊓ centralizer (Z (reducedFamily L S) w : Set (G₀ L S)) =
        Z (reducedFamily L S) v ⊓ Q (reducedFamily L S) w :=
  source_noncommuting_critical_intersections (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hc hne

/-- Reduced F1.11 application of 6.6. Only the earlier 6.5 obstruction remains
explicit; its final unconditional discharge belongs to this setup theorem family. -/
theorem reduced_normal_center_product (h : HypothesisF11 L S)
    {v w : Vertex (reducedFamily L S)} (hvw : (graph (reducedFamily L S)).Adj v w)
    (hn : stabilizer (reducedFamily L S) w ≤
      normalizer ((Z (reducedFamily L S) v ⊔ Z (reducedFamily L S) w : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hnot : ¬ stabilizer (reducedFamily L S) w ≤
      normalizer ((Q (reducedFamily L S) v ⊓ Q (reducedFamily L S) w : Subgroup (G₀ L S)) : Set (G₀ L S))) :
    (∀ T : Sylow 2 (stabilizer (reducedFamily L S) v),
      Z (reducedFamily L S) v = omegaCenterIn ((T : Subgroup (stabilizer (reducedFamily L S) v)).map
        (stabilizer (reducedFamily L S) v).subtype)) ∧
      Z (reducedFamily L S) v ≤ Z (reducedFamily L S) w :=
  source_normal_center_product (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hvw hn hnot

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
