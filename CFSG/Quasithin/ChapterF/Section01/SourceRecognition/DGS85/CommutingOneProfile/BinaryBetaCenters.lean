module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.BinaryBetaCores
public import Theory.GroupTheory.DisjointConjugateCenter

/-!
# Full core and edge centers in the linear-alpha/binary-beta branch

The beta-core center is normalized by the full edge. If it escaped the
alpha core, normalizer invariance in the actual linear quotient would make
it supplement that core in the edge Sylow. Since the alpha core is its
elementary center, the first seed would then centralize the entire beta
core. The second seed is elementary too, contradicting the already proved
nonabelian pair span. Hence the beta-core center lies in the alpha core.

The full beta stabilizer transports this containment to every neighboring
alpha core. Their intersection is Z_beta, so Z(Q_beta) = Z_beta. Relative
self-centralization and the earlier local centrality give Z(S_0) = Z_beta
for the literal edge two-core as well. Decomposing an element over the
two elementary seeds then shows that each seed is self-centralizing in
Q_beta. No field-four or center-order
hypothesis is used. The earlier local data and genuine quotient markings
remain explicit; this does not select the field or complete Chapter 11.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.3), (11.6), (11.7)(e), printed pp.168--175; these center consequences
use the proved core and seed identities of the binary-beta branch.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k : Type*} [Field k] [Finite k] [CharP k 2]

/-- The entire beta-core center is the original beta center. -/
theorem source_linear_binary_core_center (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,ZMod 2))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    centerIn (Q (family P) b) = Z (family P) b := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let := source_center_elementary h c
  let C := centerIn (Q (family P) b)
  let E := Z (family P) a ⊓ Q (family P) b
  let F := Z (family P) c ⊓ Q (family P) b
  have hab := source_critical_one_adjacent hc hb
  have hs := source_linear_binary_beta_core_structure h hB d hc hb hcomm hbc hac Ma ea eb g hga hgb
  have hpair : Q (family P) b = E ⊔ F := hs.1
  have hQa := source_linear_binary_core_eq_center h hB d hc hb hcomm hbc hac Ma ea eb g hga hgb
  have hnC : stabilizer (family P) b ≤ normalizer (C : Set G) :=
    normalizes_centerIn (stabilizer_normalizes_Q (family P) b)
  have hCQ : C ≤ Q (family P) b := inf_le_left
  have hCa : C ≤ Q (family P) a := by
    by_contra he
    have hprod := source_linear_edge_supplement h hB d hab Ma ea C
      ((isPGroup_pCoreIn 2 _).to_le hCQ)
      (hCQ.trans (by simpa only [inf_comm] using
        ((source_Z_Q_U h b).2.trans (ballKernel_one_le_edge _ hab.symm))))
      (inf_le_right.trans hnC) he
    have hCb : C ≤ centralizer (Q (family P) b : Set G) := inf_le_right
    have hQE : Q (family P) b ≤ centralizer (E : Set G) := by
      have hQS := Noncommuting.graph_Q_le_edgeCore h hab.symm
      rw [inf_comm] at hQS
      apply hQS.trans
      rw [hprod,hQa]
      exact sup_le (hCb.trans (centralizer_le (show E ≤ Q (family P) b from inf_le_right)))
        ((le_centralizer_iff_isMulCommutative.mpr
          (inferInstance : IsMulCommutative (Z (family P) a))).trans
            (centralizer_le (show E ≤ Z (family P) a from inf_le_left)))
    have hQF : Q (family P) b ≤ centralizer (F : Set G) := by
      rw [hpair]
      exact sup_le ((le_centralizer_iff.mp hQE).trans
        (centralizer_le (show F ≤ Q (family P) b from inf_le_right)))
        (inf_le_left.trans ((le_centralizer_iff_isMulCommutative.mpr
          (inferInstance : IsMulCommutative (Z (family P) c))).trans
            (centralizer_le (show F ≤ Z (family P) c from inf_le_left))))
    apply hs.2.2.2.1
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (hpair.le.trans (sup_le (le_centralizer_iff.mp hQE) (le_centralizer_iff.mp hQF)))
  have hCI : C ≤ neighborCoreIntersection (family P) b := by
    apply le_iInf
    intro v
    obtain ⟨t,ht,hta⟩ := locally_transitive (family P) hab.symm v.property
    have hm := map_mono (f := (MulAut.conj t).toMonoidHom) hCa
    have heC : C.map (MulAut.conj t).toMonoidHom = C :=
      mem_normalizer_iff_map_conj_eq.mp (hnC ht)
    rw [heC,←Q_translate,hta] at hm
    exact hm
  apply le_antisymm
  · exact hCI.trans_eq (source_linear_binary_neighbor_intersection_eq_center
      h hB d hc hb hcomm hbc hac Ma ea eb g hga hgb)
  · exact le_inf ((source_Z_Q_U h b).1.trans (map_subtype_le _))
      (le_centralizer_iff.mp (source_core_centralizes_center h b))

/-- The full edge two-core has the same center as the beta core. -/
theorem source_linear_binary_edge_center (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,ZMod 2))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    centerIn ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) =
      Z (family P) b := by
  let := finite_endpoints h
  let S := (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2
  have hab := source_critical_one_adjacent hc hb
  have hQbS : Q (family P) b ≤ S := by
    simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab.symm
  have hcent := source_linear_binary_core_center h hB d hc hb hcomm hbc hac Ma ea eb g hga hgb
  apply le_antisymm
  · apply le_trans ?_ hcent.le
    have hC : centerIn S ≤ centralizer (Q (family P) b : Set G) :=
      inf_le_right.trans (centralizer_le hQbS)
    exact le_inf ((le_inf (inf_le_left.trans ((pCoreIn_le 2 _).trans inf_le_right)) hC).trans
      (source_core_selfCentralizing_in_vertex h b)) hC
  · apply le_inf (((source_Z_Q_U h b).1.trans (map_subtype_le _)).trans hQbS)
    obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab.symm
    have hSL : S ≤ d.localGroup b := by
      have hh := map_subtype_le (T : Subgroup (d.localGroup b))
      rw [hT,inf_comm] at hh
      exact hh
    have hz := critical_end_center_of_commuting (family P) h.generate
      (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2) hc hcomm
      (d.localGroup b) (d.sylow_or_center b)
    intro x hx
    rw [hz] at hx
    exact centralizer_le hSL ((mem_omegaCenterIn_iff _ _).mp hx).2.1

/-- Each literal neighboring seed is self-centralizing inside the beta core. -/
theorem source_linear_binary_seed_centralizer (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,ZMod 2))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    Q (family P) b ⊓ centralizer (Z (family P) a ⊓ Q (family P) b : Set G) =
      Z (family P) a ⊓ Q (family P) b := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let := source_center_elementary h c
  let E := Z (family P) a ⊓ Q (family P) b
  let C := Z (family P) c ⊓ Q (family P) b
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le (show E ≤ Z (family P) a from inf_le_left)
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le (show C ≤ Z (family P) c from inf_le_left)
  have hpair : Q (family P) b = E ⊔ C :=
    (source_linear_binary_beta_core_structure h hB d hc hb hcomm hbc hac Ma ea eb g hga hgb).1
  have hcenter := source_linear_binary_core_center h hB d hc hb hcomm hbc hac Ma ea eb g hga hgb
  have hI := source_linear_binary_neighbor_intersection_eq_center h hB d hc hb hcomm hbc hac Ma ea eb g hga hgb
  have hQa := source_linear_binary_core_eq_center h hB d hc hb hcomm hbc hac Ma ea eb g hga hgb
  have hZE : Z (family P) b ≤ E := le_inf
    ((hI.ge.trans (neighborCoreIntersection_le _ (source_critical_one_adjacent hc hb))).trans_eq hQa)
    ((source_Z_Q_U h b).1.trans (map_subtype_le _))
  have hn : E ≤ normalizer (C : Set G) := inf_le_right.trans
    ((le_inf (source_adjacent_core_normalizes_center h hbc.symm)
      (Q (family P) b).le_normalizer).trans inf_normalizer_le_normalizer_inf)
  change Q (family P) b ⊓ centralizer (E : Set G) = E
  apply le_antisymm
  · rintro x ⟨hx,hxE⟩
    have hxprod : x ∈ (E : Set G) * (C : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right E C hn,←hpair]
      exact hx
    obtain ⟨u,hu,v,hv,huv⟩ := hxprod
    have hvE : v ∈ centralizer (E : Set G) := by
      have hh := (centralizer (E : Set G)).mul_mem
        ((centralizer (E : Set G)).inv_mem (E.le_centralizer hu)) hxE
      rw [←huv] at hh
      simpa only [inv_mul_cancel_left] using hh
    have hQv : Q (family P) b ≤ centralizer ({v} : Set G) := by
      rw [hpair]
      exact sup_le (fun y hy => mem_centralizer_singleton_iff.mpr (hvE y hy))
        (fun y hy => mem_centralizer_singleton_iff.mpr (C.le_centralizer hv y hy))
    have hvZ : v ∈ centerIn (Q (family P) b) :=
      ⟨show v ∈ Q (family P) b from hv.2,
        fun y hy => mem_centralizer_singleton_iff.mp (hQv hy)⟩
    rw [hcenter] at hvZ
    rw [←huv]
    exact E.mul_mem hu (hZE hvZ)
  · exact le_inf inf_le_right E.le_centralizer


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
