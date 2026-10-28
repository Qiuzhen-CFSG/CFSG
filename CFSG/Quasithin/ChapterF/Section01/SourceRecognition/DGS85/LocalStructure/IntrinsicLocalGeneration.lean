module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicCriticalAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.RadiusOneBound

/-!
# Local generation and edge seeds without enlargement recognition

The original starred Sylow overgroup theorem forces an escaping two-subgroup
and the full edge two-core to generate the actual enlarged local actor.
Transport uses one common edge conjugator and preserves both stabilizers.
No model of the enlarged quotient is needed, including in the possible
order-144 projective-unitary case.

The same full-vertex Sylow identifies the edge-seed equality with the
central-center alternative for the intrinsic actor. Restricting the actual
centralizer Sylow gives the precise dichotomy and seed exclusion consumed
by `IntrinsicEpsilonOne`, which applies the existing Chapter 7 argument.
Source: DGS, *Groups and Graphs* (1985), 5.1, 6.0--6.2 and 6.6,
pp.104,118--119,123; the applications in 7.3--7.4, pp.127--128.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P B : Subgroup G}

/-- The original starred overgroup theorem generates the full enlargement. -/
theorem source_escaping_twoGroup_generates_enlargement (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∃ T : Sylow 2 P, (T : Subgroup P).map P.subtype ≤ B)
    (A : Subgroup G) (hp : IsPGroup 2 A) (hAP : A ≤ P) (hAB : ¬ A ≤ B) :
    A ⊔ B.pCoreIn 2 = localEnlargement d := by
  let := d.finite_P
  have hBP : B ≤ P := le_sup_right.trans d.supplement.le
  let : Finite B := Finite.of_injective (inclusion hBP) (inclusion_injective _)
  have hAL : A ≤ localEnlargement d := by
    rw [localEnlargement_eq_sylowGenerated d hB hS]
    exact pGroup_le_sylowGenerated P A hAP hp
  have hTS : (d.sylow : Subgroup d.Pstar).map d.Pstar.subtype ≤ B.pCoreIn 2 :=
    pGroup_le_core_of_core_sylow B _ (source_star_sylow_le_borel d)
      (d.sylow.isPGroup'.map _) hB
  rcases source_overgroup_star_or_borel d (A ⊔ B.pCoreIn 2)
    (sup_le hAP ((pCoreIn_le 2 B).trans hBP)) (hTS.trans le_sup_right) with hs | hb
  · exact le_antisymm (sup_le hAL le_sup_right) (sup_le hs le_sup_right)
  · exact (hAB (le_sup_left.trans hb)).elim

/-- An escaping two-subgroup and the literal edge core generate the intrinsic actor. -/
theorem graph_intrinsic_escaping_twoGroup_generates
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (he : (graph (family P)).Adj v w)
    (A : Subgroup G) (hp : IsPGroup 2 A) (hAP : A ≤ stabilizer (family P) v)
    (hAw : ¬ A ≤ stabilizer (family P) w) :
    A ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 =
      graphLocalGroup (family P) v := by
  let := finite_endpoints h
  obtain ⟨g,hP,hE⟩ := source_edge_transport h he
  let e := MulAut.conj g
  let A₀ := A.map e.symm.toMonoidHom
  have hA₀ : A₀.map e.toMonoidHom = A := by
    simp [A₀,Subgroup.map_map]
  have hA₀P : A₀ ≤ family P v.type := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [hA₀,←hP]
    exact hAP
  have hA₀B : ¬ A₀ ≤ B := by
    intro hh
    have hm := map_mono (f := e.toMonoidHom) hh
    rw [hA₀,←hE] at hm
    exact hAw (hm.trans inf_le_right)
  have hex : ∃ d : LocalRankOneData (family P v.type) B,
      ∃ T : Sylow 2 (family P v.type), (T : Subgroup _).map (family P v.type).subtype ≤ B := by
    cases hv : v.type
    · exact ⟨Classical.choice (h.local_data 0),hS 0⟩
    · exact ⟨Classical.choice (h.local_data 1),hS 1⟩
  obtain ⟨d,hs⟩ := hex
  have hh := source_escaping_twoGroup_generates_enlargement d hB hs A₀ (hp.map _)
    hA₀P hA₀B
  rw [localEnlargement_eq_sylowGenerated d hB hs] at hh
  have hm := congrArg (map e.toMonoidHom) hh
  rw [Subgroup.map_sup,hA₀,←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ e.injective,
    ←sylowGenerated_map e,←hP,←hE] at hm
  exact hm

/-- Every full edge two-core lies in the intrinsic actor at either endpoint. -/
theorem graph_intrinsic_edgeCore_le
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} :
    (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 ≤
      graphLocalGroup (family P) v := by
  let := finite_endpoints h
  exact pGroup_le_sylowGenerated _ _ ((pCoreIn_le 2 _).trans inf_le_left)
    (isPGroup_pCoreIn 2 _)

/-- The intrinsic actor supplements the full edge by a literal element factorization. -/
theorem graph_intrinsic_edge_factor
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (he : (graph (family P)).Adj v w)
    (a : G) (ha : a ∈ stabilizer (family P) v) :
    ∃ l ∈ graphLocalGroup (family P) v,
      ∃ t ∈ stabilizer (family P) v ⊓ stabilizer (family P) w, a = l*t := by
  let := finite_endpoints h
  have hh : a ∈ (graphLocalGroup (family P) v : Set G) *
      ((stabilizer (family P) v ⊓ stabilizer (family P) w : Subgroup G) : Set G) := by
    have hn : stabilizer (family P) v ⊓ stabilizer (family P) w ≤
        normalizer (graphLocalGroup (family P) v : Set G) :=
      inf_le_left.trans (sylowGenerated_normalized _)
    rw [←coe_mul_of_right_le_normalizer_left _ _ hn,graphLocalGroup_sup_edge h hB hS he]
    exact ha
  obtain ⟨l,hl,t,ht,he⟩ := hh
  exact ⟨l,hl,t,ht,he.symm⟩

/-- The edge-seed and intrinsic central-center equalities are equivalent. -/
theorem graph_intrinsic_seed_eq_iff
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (he : (graph (family P)).Adj v w) :
    Z (family P) v = omegaCenterIn ((stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2) ↔
      Z (family P) v = omegaCenterIn (graphLocalGroup (family P) v) := by
  let := finite_endpoints h
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow h hS he
  have hTe := sylow_image_eq_edge_core (stabilizer (family P) v)
    (stabilizer (family P) v ⊓ stabilizer (family P) w) inf_le_left
    (source_edge_core_sylow h hB he) T hT
  rw [←hTe]
  constructor
  · exact sylowCenterSpan_eq_generated_omega_of_seed _ (source_vertex_core_selfCentralizing h v) T
  · intro hz
    apply le_antisymm
    · intro z hZ
      obtain ⟨_,hc,hs⟩ := (mem_omegaCenterIn_iff _ _).mp (hz ▸ hZ)
      exact (mem_omegaCenterIn_iff _ _).mpr
        ⟨pCoreIn_le_sylow _ T (map_subtype_le _ ((source_Z_Q_U h v).1 hZ)),
          centralizer_le (sylow_le_sylowGenerated _ T) hc,hs⟩
    · change omegaCenterIn ((T : Subgroup (stabilizer (family P) v)).map
        (stabilizer (family P) v).subtype) ≤ sylowCenterSpan (stabilizer (family P) v)
      exact le_iSup (fun R : Sylow 2 (stabilizer (family P) v) =>
        omegaCenterIn ((R : Subgroup (stabilizer (family P) v)).map
          (stabilizer (family P) v).subtype)) T

/-- Source 6.2(c) for the actual intrinsic actor, without a quotient marking. -/
theorem graph_intrinsic_centralizer_dichotomy
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (v : Vertex (family P)) :
    Stellmacher.IsSylowSubgroupIn (Q (family P) v)
      (graphLocalGroup (family P) v ⊓ centralizer (Z (family P) v : Set G)) ∨
      Z (family P) v = omegaCenterIn (graphLocalGroup (family P) v) := by
  let := finite_endpoints h
  rcases graphLocalGroup_sylow_or_center h hB hS v with ⟨T,hT⟩ | hc
  · left
    let K := graphLocalGroup (family P) v ⊓ centralizer (Z (family P) v : Set G)
    have hQK : Q (family P) v ≤ K := le_inf
      (pGroup_le_sylowGenerated _ _ (pCoreIn_le 2 _) (isPGroup_pCoreIn 2 _))
      (Noncommuting.graph_Q_centralizes_Z h v)
    obtain ⟨R,hR⟩ := T.exists_map_subtype_eq_of_le
      (H := K) (inf_le_inf_right _ (sylowGenerated_le _)) (hT ▸ hQK)
    exact ⟨R,hR.trans hT⟩
  · exact Or.inr hc

/-- The centralizer-Sylow alternative excludes equality with the full edge seed. -/
theorem graph_intrinsic_seed_ne_of_centralizerSylow
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (he : (graph (family P)).Adj v w)
    (hCS : Stellmacher.IsSylowSubgroupIn (Q (family P) v)
      (graphLocalGroup (family P) v ⊓ centralizer (Z (family P) v : Set G))) :
    Z (family P) v ≠ omegaCenterIn
      ((stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2) := by
  let := finite_endpoints h
  intro hseed
  have hZ := (graph_intrinsic_seed_eq_iff h hB hS he).mp hseed
  have hLC : graphLocalGroup (family P) v ≤ centralizer (Z (family P) v : Set G) := by
    rw [le_centralizer_iff,hZ]
    exact fun z hz => ((mem_omegaCenterIn_iff _ _).mp hz).2.1
  rw [inf_of_le_left hLC] at hCS
  obtain ⟨T,hT⟩ := hCS
  apply graphLocalGroup_not_closed h hB hS v
  refine ⟨T,?_⟩
  apply map_injective (graphLocalGroup (family P) v).subtype_injective
  exact hT.trans (sylowGenerated_core _).symm
end CFSG.Quasithin.ChapterF.Source.DGS85
