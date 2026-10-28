module
public import CFSG.Quasithin.ChapterF.Section01.SourceFaithfulTriple
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.Graph

/-!
# Audited Hypothesis A graph for the genuine source triple

The F1.9 local data imply DGS p94(i)--(iii) with the actual starred
endpoint, its original Sylow and quotient: same cores imply core containment,
characteristic two gives self-centralization, and relative normality turns
the supplement join into the stated set product. The whole Borel is the
edge stabilizer of the faithful connected coset graph. Vertex stabilizers
and neighbor sets are finite; no finite completion or tree is assumed.

The actual rank-one quotient makes each Sylow-center span nontrivial.
Faithfulness then constructs escape in both vertex orbits. The resulting
critical pair is attained, and Z <= Omega1 Z(Q), Q <= U give b > 0.
These are the setup and 3.8(a,b) input to the later Chapter 6 argument,
not its adjacent-core obstruction.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, pp.81--83 and 94--95; Aschbacher--Smith F.1.9, pp.261--262.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G]

/-- Bool labels are the two vertex orbits, in the original endpoint order. -/
def family (P : Fin 2 → Subgroup G) : Bool → Subgroup G
  | false => P 0
  | true => P 1

/-- The p94 containment follows from the same-core theorem, rather than being
an additional hypothesis on the F1.11 triple. -/
theorem source_core_le_star {P B : Subgroup G} (d : LocalRankOneData P B) :
    P.pCoreIn 2 ≤ d.Pstar := by
  change twoCore P ≤ d.Pstar
  rw [← d.same_core]
  exact map_subtype_le _

/-- The intrinsic characteristic-two clause is exactly p94(ii). -/
theorem source_core_selfCentralizing {P B : Subgroup G} (d : LocalRankOneData P B) :
    centralizer (pCore 2 P : Set P) ≤ pCore 2 P := by
  let := d.finite_P
  exact (ChapterA.generalizedFitting_eq_pCore_iff 2).mp d.characteristic_two

/-- Normality makes the displayed supplement the literal source set product. -/
theorem source_star_product {P B : Subgroup G} (d : LocalRankOneData P B) :
    (P : Set G) = (d.Pstar : Set G) * (B : Set G) := by
  calc
    (P : Set G) = (↑(d.Pstar ⊔ B) : Set G) := congrArg SetLike.coe d.supplement.symm
    _ = _ := coe_mul_of_right_le_normalizer_left _ _ ?_
  exact (le_sup_right.trans d.supplement.le).trans
    ((normal_subgroupOf_iff_le_normalizer d.Pstar_le).mp d.normal)

/-- The Borel marking is the normalizer of the specified Sylow in the
specified starred endpoint, with no replacement of the quotient or Sylow. -/
theorem source_star_borel {P B : Subgroup G} (d : LocalRankOneData P B) :
    B.subgroupOf d.Pstar = normalizer (d.sylow : Set d.Pstar) := by
  have hs : (((d.sylow : Subgroup d.Pstar).map d.Pstar.subtype).subgroupOf d.Pstar) =
      (d.sylow : Subgroup d.Pstar) := by
    apply map_injective d.Pstar.subtype_injective
    exact map_subgroupOf_eq_of_le (map_subtype_le _)
  apply map_injective d.Pstar.subtype_injective
  change (B.subgroupOf d.Pstar).map d.Pstar.subtype =
    (normalizer ((d.sylow : Subgroup d.Pstar) : Set d.Pstar)).map d.Pstar.subtype
  rw [← hs, ← subgroupOf_normalizer_eq (map_subtype_le _),
    subgroupOf_map_subtype, subgroupOf_map_subtype]
  simpa only [inf_comm] using d.borel_eq

/-- The actual vertex core lies in the whole Borel. -/
theorem source_core_le_borel {P B : Subgroup G} (d : LocalRankOneData P B) :
    P.pCoreIn 2 ≤ B := by
  change twoCore P ≤ B
  rw [← d.same_core]
  apply (pCoreIn_le_sylow _ d.sylow).trans
  intro x hx
  have h : x ∈ d.Pstar ⊓ normalizer
      (((d.sylow : Subgroup d.Pstar).map d.Pstar.subtype : Subgroup G) : Set G) :=
    ⟨map_subtype_le _ hx, ((d.sylow : Subgroup d.Pstar).map d.Pstar.subtype).le_normalizer hx⟩
  rw [← d.borel_eq] at h
  exact h.2

/-- The actual rank-one quotient supplies a nontrivial Sylow center span. -/
theorem source_centerSpan_ne_bot {P B : Subgroup G} (d : LocalRankOneData P B) :
    sylowCenterSpan P ≠ ⊥ := by
  let := d.finite_P
  let : Finite d.Pstar := Finite.of_injective (inclusion d.Pstar_le) (inclusion_injective _)
  have hstar : (d.sylow : Subgroup d.Pstar) ≠ ⊥ := by
    intro he
    have hp := (rankOneSylowFacts_of_rankOneQuotient d.quotient d.sylow).proper
    change normalizer ((d.sylow : Subgroup d.Pstar) : Set d.Pstar) < ⊤ at hp
    rw [he, coe_bot, normalizer_singleton] at hp
    have ht : centralizer ({1} : Set d.Pstar) = ⊤ := by
      ext x; simp [mem_centralizer_iff]
    rw [ht] at hp
    exact (lt_irrefl _ hp)
  obtain ⟨T, hT⟩ := (d.sylow.isPGroup'.map (inclusion d.Pstar_le)).exists_le_sylow
  apply sylowCenterSpan_ne_bot P T
  intro hTb
  apply hstar
  apply (map_eq_bot_iff_of_injective _ (inclusion_injective d.Pstar_le)).mp
  exact eq_bot_iff.mpr (hT.trans hTb.le)

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}

theorem finite_endpoints (h : LocallyRankOneTriple P B) : ∀ i, Finite (family P i) := by
  intro i
  cases i
  · exact (Classical.choice (h.local_data 0)).finite_P
  · exact (Classical.choice (h.local_data 1)).finite_P

/-- The original generating triple gives a connected graph, with no tree premise. -/
theorem connected_graph (h : LocallyRankOneTriple P B) : (graph (family P)).Connected :=
  connected _ h.generate

/-- Full-Borel faithfulness is exactly the kernel condition of the coset action. -/
theorem graph_kernel_bot (h : LocallyRankOneTriple P B) :
    (MulAction.toPermHom G (Vertex (family P))).ker = ⊥ := by
  rw [global_kernel]
  change (P 0 ⊓ P 1).normalCore = ⊥
  rw [h.intersection]
  exact h.faithful _ inferInstance B.normalCore_le

theorem faithful_graph (h : LocallyRankOneTriple P B) :
    FaithfulSMul G (Vertex (family P)) := by
  apply faithfulSMul_iff.mpr
  intro g hg
  have hk : g ∈ (MulAction.toPermHom G (Vertex (family P))).ker := Equiv.Perm.ext hg
  rw [graph_kernel_bot h] at hk
  exact hk

/-- The graph's unordered standard edge stabilizer is the whole original Borel. -/
theorem full_borel_edge_stabilizer (h : LocallyRankOneTriple P B) :
    MulAction.stabilizer G ({base (family P) false, base (family P) true} :
      Set (Vertex (family P))) = B := by
  rw [edge_stabilizer _ ⟨Bool.false_ne_true,
    Subgroup.CosetGeometry.incident_base _ false true⟩]
  simpa only [stabilizer, Subgroup.CosetGeometry.stabilizer_base, family] using h.intersection

/-- The two orbits cannot merge, even though all edges are in one orbit. -/
theorem not_vertex_transitive :
    ¬ (∀ v w : Vertex (family P), ∃ g : G, g • v = w) := by
  intro h
  have he := (same_orbit_iff (family P) (base (family P) false)
    (base (family P) true)).mp (h _ _)
  exact Bool.false_ne_true he

/-- The local action on the actual graph is finite at every vertex. -/
theorem graph_locally_finite (h : LocallyRankOneTriple P B) (v : Vertex (family P)) :
    Finite (stabilizer (family P) v) ∧ Finite ((graph (family P)).neighborSet v) := by
  let := finite_endpoints h
  exact ⟨inferInstance, finite_neighbors _ v⟩

/-- The source Z bound at each actual base endpoint. -/
theorem base_Z_le_coreOmega (h : LocallyRankOneTriple P B) (i : Bool) :
    Z (family P) (base (family P) i) ≤ omegaCenterIn (Q (family P) (base (family P) i)) := by
  change sylowCenterSpan (MulAction.stabilizer G (Subgroup.CosetGeometry.base (family P) i)) ≤
    omegaCenterIn ((MulAction.stabilizer G (Subgroup.CosetGeometry.base (family P) i)).pCoreIn 2)
  rw [Subgroup.CosetGeometry.stabilizer_base]
  apply sylowCenterSpan_le_coreOmega
  cases i
  · exact source_core_selfCentralizing (Classical.choice (h.local_data 0))
  · exact source_core_selfCentralizing (Classical.choice (h.local_data 1))

/-- The normal vertex core fixes every neighbor, without identifying Q with U. -/
theorem base_Q_le_U (h : LocallyRankOneTriple P B) (i : Bool) :
    Q (family P) (base (family P) i) ≤ U (family P) (base (family P) i) := by
  have hQ : (family P i).pCoreIn 2 ≤ B := by
    cases i
    · exact source_core_le_borel (Classical.choice (h.local_data 0))
    · exact source_core_le_borel (Classical.choice (h.local_data 1))
  have hU : U (family P) (base (family P) i) ≤ family P i := by
    simpa only [stabilizer, Subgroup.CosetGeometry.stabilizer_base] using
      U_le_stabilizer (family P) (base (family P) i)
  have hl : pCore 2 (family P i) ≤
      (U (family P) (base (family P) i)).subgroupOf (family P i) := by
    change pCore 2 (family P i) ≤
      (ballKernel (family P) (base (family P) i) 1).subgroupOf (family P i)
    rw [base_ballKernel_one]
    change pCore 2 (family P i) ≤ ((P 0 ⊓ P 1).subgroupOf (family P i)).normalCore
    rw [h.intersection]
    apply normal_le_normalCore.mpr
    intro x hx
    exact hQ (mem_map_of_mem (family P i).subtype hx)
  have hm := map_mono (f := (family P i).subtype) hl
  rw [map_subgroupOf_eq_of_le hU] at hm
  change (MulAction.stabilizer G (Subgroup.CosetGeometry.base (family P) i)).pCoreIn 2 ≤ _
  rw [Subgroup.CosetGeometry.stabilizer_base]
  exact hm

/-- Source 3.8(a,b) at all vertices of the actual graph. -/
theorem source_Z_Q_U (h : LocallyRankOneTriple P B) (v : Vertex (family P)) :
    Z (family P) v ≤ omegaCenterIn (Q (family P) v) ∧ Q (family P) v ≤ U (family P) v := by
  let := finite_endpoints h
  obtain ⟨g, hg⟩ := Subgroup.CosetGeometry.exists_smul_base (family P) v
  rw [← hg, Z_translate, Q_translate, U_translate,
    ← NilesRankOneKernel.omegaCenterIn_map_injective _ (MulAut.conj g).injective]
  exact ⟨map_mono (base_Z_le_coreOmega h _), map_mono (base_Q_le_U h _)⟩

/-- Both base centers, and hence both escape sets, are nontrivial. -/
theorem base_Z_ne_bot (h : LocallyRankOneTriple P B) (i : Bool) :
    Z (family P) (base (family P) i) ≠ ⊥ := by
  change sylowCenterSpan (MulAction.stabilizer G (Subgroup.CosetGeometry.base (family P) i)) ≠ ⊥
  rw [Subgroup.CosetGeometry.stabilizer_base]
  cases i
  · exact source_centerSpan_ne_bot (Classical.choice (h.local_data 0))
  · exact source_centerSpan_ne_bot (Classical.choice (h.local_data 1))

/-- The source escape minimum exists in both vertex orbits. -/
theorem base_criticalDistances_nonempty (h : LocallyRankOneTriple P B) (i : Bool) :
    (criticalDistancesAt (family P) (base (family P) i)).Nonempty := by
  let := faithful_graph h
  exact criticalDistancesAt_nonempty _ _ (base_Z_ne_bot h i)

/-- The actual faithful triple has the source two-sided minimum. -/
theorem source_b_eq_min (h : LocallyRankOneTriple P B) :
    b (family P) = min (bAt (family P) (base (family P) false))
      (bAt (family P) (base (family P) true)) := by
  let := finite_endpoints h
  exact b_eq_min _ (base_criticalDistances_nonempty h false)
    (base_criticalDistances_nonempty h true)

/-- The critical pair is attained, even for an infinite completion. -/
theorem source_exists_criticalPair (h : LocallyRankOneTriple P B) :
    ∃ v w : Vertex (family P), IsCriticalPair (family P) v w := by
  apply exists_criticalPair
  obtain ⟨n, hn⟩ := base_criticalDistances_nonempty h false
  exact ⟨n, base (family P) false, hn⟩

/-- Source 3.8(c) for an attained critical pair of the actual source triple. -/
theorem source_critical_centers (h : LocallyRankOneTriple P B) :
    ∃ v w : Vertex (family P), IsCriticalPair (family P) v w ∧
      Z (family P) w ≤ stabilizer (family P) v ∧
      ⁅Z (family P) v, Z (family P) w⁆ ≤ Z (family P) v ⊓ Z (family P) w := by
  let := finite_endpoints h
  obtain ⟨v, w, hc⟩ := source_exists_criticalPair h
  have hcc := criticalPair_centers (family P) h.generate hc
  exact ⟨v, w, hc, hcc⟩

/-- The attained critical distance is positive, as in source 3.8(b). -/
theorem source_b_positive (h : LocallyRankOneTriple P B) : 0 < b (family P) := by
  apply Nat.pos_of_ne_zero
  intro hb
  obtain ⟨v, w, hd, he⟩ := source_exists_criticalPair h
  have hvw : v = w := (connected_graph h).dist_eq_zero_iff.mp (hd.trans hb)
  subst w
  obtain ⟨hZ, hQ⟩ := source_Z_Q_U h v
  exact he (hZ.trans ((map_subtype_le _).trans hQ))

variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
/-- The full original F1.11 parabolics in their actual generated completion. -/
def fullFamily (L : Fin 2 → Subgroup G) (S : Subgroup G) :
    Bool → Subgroup (generated L S) :=
  family (fun i => (parabolic L S i).subgroupOf (generated L S))

/-- Actual F1.11 application: faithful connected graph, finite stabilizers and
finite local actions, with the original full Borel as the edge stabilizer. -/
theorem f11_full_graph (h : HypothesisF11 L S) :
    (graph (fullFamily L S)).Connected ∧
    FaithfulSMul (generated L S) (Vertex (fullFamily L S)) ∧
    (∀ v : Vertex (fullFamily L S),
      Finite (stabilizer (fullFamily L S) v) ∧ Finite ((graph (fullFamily L S)).neighborSet v)) ∧
    MulAction.stabilizer (generated L S)
      ({base (fullFamily L S) false, base (fullFamily L S) true} : Set (Vertex (fullFamily L S))) =
        (commonBorel L S).subgroupOf (generated L S) := by
  have ht := h.generatedLocallyRankOneTriple
  exact ⟨connected_graph ht, faithful_graph ht, graph_locally_finite ht,
    full_borel_edge_stabilizer ht⟩

end CFSG.Quasithin.ChapterF.Source.DGS85
