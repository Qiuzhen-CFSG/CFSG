module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.KernelSylow
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# Local transitivity and the elementary adjacent-core obstruction premises

The actual rank-one Sylow normalizer is maximal in the full endpoint,
including its outer Borel factors. A normal subgroup which is not two-closed
therefore covers the Borel cosets. Common conjugation transports the full
edge and endpoint together, giving transitivity on the actual neighbors
at every vertex of the reduced F1.11 graph: DGS (6.2)(b).

Under the contrary intersection-normality assumption of (6.4), the opposite
core escapes the second vertex core. The full kernel is two-closed, so the
literal normal closure also escapes it and covers the Borel cosets. A
characteristic subgroup of the first core normal in this closure is then
normalized by both original endpoints. Faithfulness kills it, proving
(6.4)(b). Normal-subgroup inheritance supplies the self-centralizing core
premise for this same closure. The preliminary implication in (6.5) is also
proved: Sylow membership would make the core intersection normal.

These results include actual reduced F1.11 applications. The Sylow and SL₂
quotient assertions of (6.4), the Baumann contradiction of (6.5), and the
later center/path conclusions are separate remaining source obligations.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, (3.2)(c), p.72; (6.2), p.119; (6.4)--(6.5), pp.120--122.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G]

/-- The rank-one Sylow normalizer is maximal in the full endpoint, including
its outer Borel factors. -/
theorem source_borel_maximal {P B : Subgroup G} (d : LocalRankOneData P B)
    (M : Subgroup G) (hBM : B ≤ M) (hMP : M ≤ P) : M = B ∨ M = P := by
  let := d.finite_P
  let : Finite d.Pstar := Finite.of_injective (inclusion d.Pstar_le) (inclusion_injective _)
  by_cases hstar : M.subgroupOf d.Pstar = ⊤
  · right
    apply le_antisymm hMP
    rw [← d.supplement]
    refine sup_le ?_ hBM
    intro x hx
    exact (show (⟨x, hx⟩ : d.Pstar) ∈ M.subgroupOf d.Pstar by rw [hstar]; trivial)
  · left
    have hS : (d.sylow : Subgroup d.Pstar) ≤ M.subgroupOf d.Pstar := by
      apply le_trans _ (comap_mono hBM)
      change (d.sylow : Subgroup d.Pstar) ≤ B.subgroupOf d.Pstar
      rw [source_star_borel d]
      exact (d.sylow : Subgroup d.Pstar).le_normalizer
    have hMB : M.subgroupOf d.Pstar ≤ B.subgroupOf d.Pstar := by
      rw [source_star_borel d]
      exact (rankOneSylowFacts_of_rankOneQuotient d.quotient d.sylow).unique_maximal _ hS
        (lt_top_iff_ne_top.mpr hstar)
    apply le_antisymm _ hBM
    intro x hx
    have hp : x ∈ (d.Pstar : Set G) * (B : Set G) := by
      rw [← source_star_product d]
      exact hMP hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hp
    have haM : a ∈ M := by
      have hh := M.mul_mem hx (M.inv_mem (hBM hb))
      simpa only [mul_inv_cancel_right] using hh
    exact B.mul_mem (hMB (show (⟨a, ha⟩ : d.Pstar) ∈ M.subgroupOf d.Pstar from haM)) hb

/-- Properness is witnessed by the actual starred Sylow normalizer. -/
theorem source_borel_lt {P B : Subgroup G} (d : LocalRankOneData P B) : B < P := by
  let := d.finite_P
  let : Finite d.Pstar := Finite.of_injective (inclusion d.Pstar_le) (inclusion_injective _)
  apply lt_of_le_of_ne (le_sup_right.trans d.supplement.le)
  intro he
  have hb : B.subgroupOf d.Pstar = ⊤ := by
    exact subgroupOf_eq_top.mpr (d.Pstar_le.trans he.ge)
  rw [source_star_borel d] at hb
  exact (rankOneSylowFacts_of_rankOneQuotient d.quotient d.sylow).proper.ne hb

/-- A normal subgroup outside the local action kernel covers the full Borel
cosets. Normality is relative to the endpoint. -/
theorem source_normal_sup_borel {P B : Subgroup G} (d : LocalRankOneData P B)
    (N : Subgroup G) (hNP : N ≤ P) (hn : P ≤ normalizer (N : Set G))
    (he : ¬ N ≤ Theory.GroupTheory.AmalgamLocalCores.localKernel P B) : N ⊔ B = P := by
  rcases source_borel_maximal d (N ⊔ B) le_sup_right
    (sup_le hNP (le_sup_right.trans d.supplement.le)) with h | h
  · exfalso
    apply he
    have hNB : N ≤ B := le_sup_left.trans h.le
    let : (N.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hNP).mpr hn
    have hc : N.subgroupOf P ≤ (B.subgroupOf P).normalCore :=
      normal_le_normalCore.mpr (comap_mono hNB)
    have hm := map_mono (f := P.subtype) hc
    rwa [map_subgroupOf_eq_of_le hNP] at hm
  · exact h

/-- Local cover by a normalizing subgroup kills every common normal subgroup
of the overlap. This is the algebraic source 3.2(c) used in 6.4(b). -/
theorem characteristic_core_eq_bot_of_cover {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B) (i : Fin 2)
    (X : Subgroup G) (hcover : X ⊔ B = P (other i))
    (K : Subgroup ((P i).pCoreIn 2)) [K.Characteristic]
    (hnK : X ≤ normalizer (K.map ((P i).pCoreIn 2).subtype : Set G)) : K = ⊥ := by
  let D := K.map ((P i).pCoreIn 2).subtype
  have hQi : P i ≤ normalizer ((P i).pCoreIn 2 : Set G) :=
    (P i).le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 (P i)))
  have hDi : P i ≤ normalizer (D : Set G) :=
    hQi.trans (normalizer_le_normalizer_characteristic_image _ K)
  have hDB : D ≤ B := (map_subtype_le _).trans
    (source_core_le_borel (Classical.choice (h.local_data i)))
  have hDj : P (other i) ≤ normalizer (D : Set G) := by
    rw [← hcover]
    apply sup_le hnK
    have hBi : B ≤ P i := by
      rw [← h.intersection]
      fin_cases i
      · exact inf_le_left
      · exact inf_le_right
    exact hBi.trans hDi
  have hgen : P i ⊔ P (other i) = ⊤ := by
    fin_cases i
    · exact h.generate
    · exact (sup_comm _ _).trans h.generate
  let : D.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp (hgen ▸ sup_le hDi hDj))
  exact (map_eq_bot_iff_of_injective _ ((P i).pCoreIn 2).subtype_injective).mp
    (h.faithful D inferInstance hDB)

private theorem core_normalized (P : Subgroup G) : P ≤ normalizer (P.pCoreIn 2 : Set G) :=
  P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))

/-- Nontriviality of the actual rank-one Sylow center forces a nonzero vertex core. -/
theorem source_core_ne_bot {P B : Subgroup G} (d : LocalRankOneData P B) : P.pCoreIn 2 ≠ ⊥ := by
  intro he
  apply source_centerSpan_ne_bot d
  apply eq_bot_iff.mpr
  exact ((sylowCenterSpan_le_coreOmega P (source_core_selfCentralizing d)).trans
    (map_subtype_le _)).trans he.le

/-- Under the contrary normality assumption of 6.4, one endpoint core cannot
lie in the other: it would be a common normal subgroup of the faithful overlap. -/
theorem core_not_le_of_inter_normal {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B) (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    ¬ (P i).pCoreIn 2 ≤ (P (other i)).pCoreIn 2 := by
  intro hle
  rw [inf_eq_left.mpr hle] at hn
  have hgen : P i ⊔ P (other i) = ⊤ := by
    fin_cases i
    · exact h.generate
    · exact (sup_comm _ _).trans h.generate
  let : ((P i).pCoreIn 2).Normal := normalizer_eq_top_iff.mp
    (top_le_iff.mp (hgen ▸ sup_le (core_normalized _) hn))
  exact source_core_ne_bot (Classical.choice (h.local_data i))
    (h.faithful _ inferInstance (source_core_le_borel (Classical.choice (h.local_data i))))

/-- A two-subgroup of the full local kernel lies in the vertex two-core when
the full Borel is two-closed. -/
theorem pGroup_le_vertex_core_of_le_kernel {P B : Subgroup G}
    (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (A : Subgroup G) (hA : IsPGroup 2 A)
    (hAU : A ≤ Theory.GroupTheory.AmalgamLocalCores.localKernel P B) : A ≤ P.pCoreIn 2 := by
  let := d.finite_P
  have hBP : B ≤ P := le_sup_right.trans d.supplement.le
  let : Finite B := Finite.of_injective (inclusion hBP) (inclusion_injective _)
  let U := Theory.GroupTheory.AmalgamLocalCores.localKernel P B
  have hUB : U ≤ B := Theory.GroupTheory.AmalgamLocalCores.localKernel_le_right _ _
  let : Finite U := Finite.of_injective (inclusion hUB) (inclusion_injective _)
  have hUc := core_sylow_of_le B U hUB hB
  exact (pGroup_le_core_of_core_sylow U A hAU hA hUc).trans
    (pCoreIn_mono_of_normalizes (Theory.GroupTheory.AmalgamLocalCores.localKernel_le_left _ _)
      (Theory.GroupTheory.AmalgamLocalCores.normalizes_localKernel _ _))

/-- Under the contrary hypothesis of 6.4, the literal normal closure of the
opposite core covers all neighboring Borel cosets. -/
theorem core_closure_sup_borel_of_inter_normal
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B) (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) ⊔ B = P (other i) := by
  let d := Classical.choice (h.local_data (other i))
  have hBP : B ≤ P (other i) := le_sup_right.trans d.supplement.le
  apply source_normal_sup_borel d _
    (conjugateSpanBy_le_self ((source_core_le_borel (Classical.choice (h.local_data i))).trans hBP))
    (le_normalizer_conjugateSpanBy _ _)
  intro hXU
  exact core_not_le_of_inter_normal h i hn
    (pGroup_le_vertex_core_of_le_kernel d hB _ (isPGroup_pCoreIn 2 _)
      ((le_conjugateSpanBy _ _).trans hXU))

/-- Source 6.4(b), with the literal opposite-core normal closure and every
local-cover premise discharged under its stated contrary normality assumption. -/
theorem characteristic_core_eq_bot_of_inter_normal
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B) (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (K : Subgroup ((P i).pCoreIn 2)) [K.Characteristic]
    (hK : conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) ≤
      normalizer (K.map ((P i).pCoreIn 2).subtype : Set G)) : K = ⊥ :=
  characteristic_core_eq_bot_of_cover h i _
    (core_closure_sup_borel_of_inter_normal h hB i hn) K hK


/-- The literal opposite-core normal closure has self-centralizing two-core,
by normal-subgroup inheritance inside the finite endpoint. -/
theorem core_closure_selfCentralizing {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B) (i : Fin 2) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    centralizer (pCore 2 X : Set X) ≤ pCore 2 X := by
  let d := Classical.choice (h.local_data (other i))
  let := d.finite_P
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  have hBP : B ≤ P (other i) := le_sup_right.trans d.supplement.le
  have hXP : X ≤ P (other i) := conjugateSpanBy_le_self
    ((source_core_le_borel (Classical.choice (h.local_data i))).trans hBP)
  let : Finite X := Finite.of_injective (inclusion hXP) (inclusion_injective _)
  let N := X.subgroupOf (P (other i))
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hXP).mpr (le_normalizer_conjugateSpanBy _ _)
  have hc := normal_core_selfCentralizing (source_core_selfCentralizing d) N
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hXP)).mp hc

/-- The elementary implication at the start of 6.5: if the opposite core
were Sylow in its literal normal closure, the core intersection would be
normal in the second endpoint. -/
theorem core_inter_normal_of_core_sylow {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B) (i : Fin 2)
    (hs : ∃ T : Sylow 2 (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))),
      (T : Subgroup (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))).map
        (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).subtype = (P i).pCoreIn 2) :
    P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G) := by
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  have hBP : B ≤ P (other i) :=
    le_sup_right.trans (Classical.choice (h.local_data (other i))).supplement.le
  have hXP : X ≤ P (other i) := conjugateSpanBy_le_self
    ((source_core_le_borel (Classical.choice (h.local_data i))).trans hBP)
  have hnX : P (other i) ≤ normalizer (X : Set G) := le_normalizer_conjugateSpanBy _ _
  obtain ⟨T, hT⟩ := hs
  have hc : (P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2 = X.pCoreIn 2 := by
    apply le_antisymm
    · exact (inf_le_inf_right _ (le_conjugateSpanBy _ _)).trans
        (inf_pCoreIn_le_of_le 2 hXP)
    · exact le_inf ((pCoreIn_le_sylow X T).trans_eq hT) (pCoreIn_mono_of_normalizes hXP hnX)
  rw [hc]
  exact hnX.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))

/-- The second conclusion of 6.5 follows from its adjacent-intersection
obstruction, for the same literal normal closure. -/
theorem core_not_sylow_of_inter_not_normal {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B) (i : Fin 2)
    (hn : ¬ P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))),
      (T : Subgroup (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))).map
        (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).subtype = (P i).pCoreIn 2 :=
  fun hs => hn (core_inter_normal_of_core_sylow h i hs)

/-- A literal cover of a vertex group by N and the full Borel is transitive
on the actual graph neighbors, with the same inclusion and left action. -/
theorem neighbor_transitive_of_borel_cover {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B) (i : Bool) (N : Subgroup G)
    (hn : family P i ≤ normalizer (N : Set G)) (hcover : N ⊔ B = family P i)
    (w : Vertex (family P)) (hw : (graph (family P)).Adj (base (family P) i) w) :
    ∃ n ∈ N, n • base (family P) (!i) = w := by
  have hB (j : Bool) : B ≤ family P j := by
    rw [← h.intersection]
    cases j
    · exact inf_le_left
    · exact inf_le_right
  have hbase : (graph (family P)).Adj (base (family P) i) (base (family P) (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨g, hg, he⟩ := locally_transitive (family P) hbase hw
  have hg' : g ∈ family P i := by
    change g ∈ MulAction.stabilizer G (Subgroup.CosetGeometry.base (family P) i) at hg
    rwa [Subgroup.CosetGeometry.stabilizer_base] at hg
  have hp : g ∈ (N : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left N B ((hB i).trans hn), hcover]
    exact hg'
  obtain ⟨n, hn, a, ha, rfl⟩ := hp
  have hafix : a • base (family P) (!i) = base (family P) (!i) := by
    change a ∈ MulAction.stabilizer G (Subgroup.CosetGeometry.base (family P) (!i))
    rw [Subgroup.CosetGeometry.stabilizer_base]
    exact hB (!i) ha
  exact ⟨n, hn, by simpa only [mul_smul, hafix] using he⟩

private theorem maximal_interval_map (e : G ≃* G) (B P : Subgroup G)
    (h : ∀ M, B ≤ M → M ≤ P → M = B ∨ M = P)
    (M : Subgroup G) (hBM : B.map e.toMonoidHom ≤ M) (hMP : M ≤ P.map e.toMonoidHom) :
    M = B.map e.toMonoidHom ∨ M = P.map e.toMonoidHom := by
  let f := e.mapSubgroup
  change f B ≤ M at hBM
  change M ≤ f P at hMP
  change M = f B ∨ M = f P
  have h1 : B ≤ f.symm M := by
    simpa only [OrderIso.symm_apply_apply] using f.symm.monotone hBM
  have h2 : f.symm M ≤ P := by
    simpa only [OrderIso.symm_apply_apply] using f.symm.monotone hMP
  rcases h (f.symm M) h1 h2 with he | he
  · exact Or.inl (by simpa only [OrderIso.apply_symm_apply] using congrArg f he)
  · exact Or.inr (by simpa only [OrderIso.apply_symm_apply] using congrArg f he)

/-- Conjugation identifies the full edge and its incident vertex with their
original marked Borel and endpoint, in a single common transport. -/
theorem source_edge_transport {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B) {v w : Vertex (family P)}
    (hvw : (graph (family P)).Adj v w) :
    ∃ g : G, stabilizer (family P) v = (family P v.type).map (MulAut.conj g).toMonoidHom ∧
      stabilizer (family P) v ⊓ stabilizer (family P) w = B.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hv, hw⟩ := incident_common_translate (family P) hvw.2
  have hb : family P v.type ⊓ family P w.type = B := by
    have hne := hvw.1
    cases hi : v.type <;> cases hj : w.type
    · exact (hne (hi.trans hj.symm)).elim
    · exact h.intersection
    · exact (inf_comm _ _).trans h.intersection
    · exact (hne (hi.trans hj.symm)).elim
  have hst (x : Vertex (family P)) :
      stabilizer (family P) (g • base (family P) x.type) =
        (family P x.type).map (MulAut.conj g).toMonoidHom := by
    rw [stabilizer_translate]
    change (MulAction.stabilizer G (Subgroup.CosetGeometry.base (family P) x.type)).map _ = _
    rw [Subgroup.CosetGeometry.stabilizer_base]
  refine ⟨g, hv ▸ hst v, ?_⟩
  rw [← hv, ← hw, hst, hst, ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hb]

/-- Every full edge stabilizer is maximal in each incident vertex group. -/
theorem source_edge_maximal {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B) {v w : Vertex (family P)}
    (hvw : (graph (family P)).Adj v w) (M : Subgroup G)
    (hEM : stabilizer (family P) v ⊓ stabilizer (family P) w ≤ M)
    (hMP : M ≤ stabilizer (family P) v) :
    M = stabilizer (family P) v ⊓ stabilizer (family P) w ∨ M = stabilizer (family P) v := by
  obtain ⟨g, hP, hE⟩ := source_edge_transport h hvw
  have hm : ∀ D, B ≤ D → D ≤ family P v.type → D = B ∨ D = family P v.type := by
    cases ht : v.type
    · exact source_borel_maximal (Classical.choice (h.local_data 0))
    · exact source_borel_maximal (Classical.choice (h.local_data 1))
  rw [hP] at hMP
  rw [hE] at hEM
  simpa only [← hP, ← hE] using maximal_interval_map (MulAut.conj g) B (family P v.type) hm M hEM hMP

/-- Normal-Sylow control of the full Borel transports to every actual edge. -/
theorem source_edge_core_sylow {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w) :
    ∃ T : Sylow 2 (stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G),
      (T : Subgroup (stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G)) =
        pCore 2 (stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G) := by
  let := (Classical.choice (h.local_data 0)).finite_P
  have hBP : B ≤ P 0 := h.intersection.ge.trans inf_le_left
  let : Finite B := Finite.of_injective (inclusion hBP) (inclusion_injective _)
  obtain ⟨g, _, hE⟩ := source_edge_transport h hvw
  rw [hE]
  exact core_sylow_equiv (B.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective) hB

/-- DGS 6.2(b): a normal subgroup which is not two-closed is transitive on
the actual neighbors. The full local kernel and all original actions are retained. -/
theorem source_nonclosed_normal_transitive {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (N : Subgroup G) (hNP : N ≤ stabilizer (family P) v)
    (hn : stabilizer (family P) v ≤ normalizer (N : Set G))
    (hclosed : ¬ ∃ T : Sylow 2 N, (T : Subgroup N) = pCore 2 N)
    (z : Vertex (family P)) (hvz : (graph (family P)).Adj v z) :
    ∃ n ∈ N, n • w = z := by
  let := finite_endpoints h
  let E := stabilizer (family P) v ⊓ stabilizer (family P) w
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer (family P) v from inf_le_left))
    (inclusion_injective _)
  have hcover : N ⊔ E = stabilizer (family P) v := by
    rcases source_edge_maximal h hvw (N ⊔ E) le_sup_right (sup_le hNP inf_le_left) with hle | he
    · exact (hclosed (core_sylow_of_le E N (le_sup_left.trans hle.le)
        (source_edge_core_sylow h hB hvw))).elim
    · exact he
  obtain ⟨g, hg, he⟩ := locally_transitive (family P) hvw hvz
  have hgprod : g ∈ (N : Set G) * (E : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left N E (inf_le_left.trans hn), hcover]
    exact hg
  obtain ⟨n, hn, a, ha, rfl⟩ := hgprod
  have haw : a • w = w := ha.2
  exact ⟨n, hn, by simpa only [mul_smul, haw] using he⟩

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Actual reduced F1.11 application of 6.4(b), preserving both marked
endpoint inclusions and the entire reduced overlap. -/
theorem reduced_characteristic_core_eq_bot_of_inter_normal (h : HypothesisF11 L S)
    (i : Fin 2)
    (hn : (P₀ L S (other i)).subgroupOf (G₀ L S) ≤ normalizer
      ((((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S)))
    (K : Subgroup (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)) [K.Characteristic]
    (hK : conjugateSpanBy (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)
        ((P₀ L S (other i)).subgroupOf (G₀ L S)) ≤
      normalizer (K.map (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2).subtype : Set (G₀ L S))) :
    K = ⊥ :=
  characteristic_core_eq_bot_of_inter_normal (reduced_triple h)
    (reduced_borel_core_sylow h) i hn K hK
/-- The self-centralizing-core premise for the actual reduced 6.4 normal closure. -/
theorem reduced_core_closure_selfCentralizing (h : HypothesisF11 L S) (i : Fin 2) :
    let X := conjugateSpanBy (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)
      ((P₀ L S (other i)).subgroupOf (G₀ L S))
    centralizer (pCore 2 X : Set X) ≤ pCore 2 X :=
  core_closure_selfCentralizing (reduced_triple h) i

/-- The normal-subgroup transitivity conclusion 6.2(b) on the actual reduced graph. -/
theorem reduced_nonclosed_normal_transitive (h : HypothesisF11 L S)
    {v w : Vertex (reducedFamily L S)} (hvw : (graph (reducedFamily L S)).Adj v w)
    (N : Subgroup (G₀ L S)) (hNP : N ≤ stabilizer (reducedFamily L S) v)
    (hn : stabilizer (reducedFamily L S) v ≤ normalizer (N : Set (G₀ L S)))
    (hclosed : ¬ ∃ T : Sylow 2 N, (T : Subgroup N) = pCore 2 N)
    (z : Vertex (reducedFamily L S)) (hvz : (graph (reducedFamily L S)).Adj v z) :
    ∃ n ∈ N, n • w = z :=
  source_nonclosed_normal_transitive (reduced_triple h) (reduced_borel_core_sylow h)
    hvw N hNP hn hclosed z hvz

end Reduction

end CFSG.Quasithin.ChapterF.Source.DGS85
