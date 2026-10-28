module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.LocalActor
public import Theory.SpecificGroups.SL2.SylowCosetExchange

/-!
# Exchanging actual neighbors through the binary linear local quotient

The full edge normalizes its own Sylow two-core. Maximality of the edge
and nonclosedness of the local actor identify its vertex normalizer exactly.
Transporting that same Sylow to L and then L/O₂(L) identifies the actual
neighbor stabilizer with a Sylow normalizer in the quotient. A matrix
involution therefore lifts to an element of L swapping any two neighbors,
with square in the original Q. This keeps the full kernel U distinct from Q.

`ReverseDisplacement` uses this to finish the exchange in 9.2 from the
Chapter 8 distance and actual linear-quotient conclusions. Source: DGS,
*Groups and Graphs* (1985), 6.0--6.2 and 9.2, pp.118--119 and 142.
-/

open Subgroup
open scoped MatrixGroups
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The full edge is exactly the vertex normalizer of its embedded two-core. -/
theorem local_edge_core_normalizer (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w) :
    let E := stabilizer (family P) v ⊓ stabilizer (family P) w
    stabilizer (family P) v ⊓ normalizer (E.pCoreIn 2 : Set G) = E := by
  let := finite_endpoints h
  let R := stabilizer (family P) v
  let E := R ⊓ stabilizer (family P) w
  let : Finite E := Finite.of_injective (inclusion (show E ≤ R from inf_le_left)) (inclusion_injective _)
  have hEN : E ≤ normalizer (E.pCoreIn 2 : Set G) := E.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image E (pCore 2 E))
  rcases source_edge_maximal h hvw (R ⊓ normalizer (E.pCoreIn 2 : Set G))
      (le_inf inf_le_left hEN) inf_le_left with he | he
  · exact he
  have hRN : R ≤ normalizer (E.pCoreIn 2 : Set G) := he.ge.trans inf_le_right
  have hcore : E.pCoreIn 2 ≤ R.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 E) ((map_subtype_le _).trans inf_le_left) hRN
  obtain ⟨T, hT⟩ := source_edge_vertex_sylow h hS hvw
  have hTS := sylow_image_eq_edge_core R E inf_le_left (source_edge_core_sylow h hB hvw) T hT
  have hclosed : ∃ T : Sylow 2 R, (T : Subgroup R) = pCore 2 R := by
    refine ⟨T, le_antisymm ?_ (pCore_isPGroup.le_sylow_of_normal T)⟩
    exact (map_le_map_iff_of_injective R.subtype_injective).mp (hTS.le.trans hcore)
  exact (graphLocalGroup_not_closed h hB hS v
    (core_sylow_of_le R (graphLocalGroup (family P) v) (sylowGenerated_le _) hclosed)).elim

/-- The same full edge core is an actual Sylow subgroup of the intrinsic local actor. -/
theorem local_edge_sylow (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w) :
    ∃ T : Sylow 2 (graphLocalGroup (family P) v),
      (T : Subgroup (graphLocalGroup (family P) v)).map
        (graphLocalGroup (family P) v).subtype =
          (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 := by
  let := finite_endpoints h
  let R := stabilizer (family P) v
  let H := graphLocalGroup (family P) v
  let K := H.subgroupOf R
  obtain ⟨T, hT⟩ := source_edge_vertex_sylow h hS hvw
  have hTK : (T : Subgroup R) ≤ K := fun x hx =>
    sylow_le_sylowGenerated R T (mem_map_of_mem _ hx)
  let eK := subgroupOfEquivOfLe (show H ≤ R from sylowGenerated_le _)
  let U := (T.subtype hTK).mapSurjective (f := eK.toMonoidHom) eK.surjective
  refine ⟨U, ?_⟩
  have he : (U : Subgroup H).map H.subtype = (T : Subgroup R).map R.subtype := by
    change (((T : Subgroup R).subgroupOf K).map eK.toMonoidHom).map H.subtype = _
    rw [Subgroup.map_map]
    change ((T : Subgroup R).subgroupOf K).map (R.subtype.comp K.subtype) = _
    rw [← Subgroup.map_map, map_subgroupOf_eq_of_le hTK]
  exact he.trans (sylow_image_eq_edge_core R _ inf_le_left (source_edge_core_sylow h hB hvw) T hT)

/-- The literal neighbor stabilizer maps to the normalizer of a quotient Sylow. -/
theorem local_quotient_neighbor_stabilizer (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {D : Type*} [Group D]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* D) :
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) v)))
    ∃ T : Sylow 2 D, ∀ l : graphLocalGroup (family P) v,
      q l ∈ normalizer (T : Set D) ↔ (l : G) • w = w := by
  let := finite_endpoints h
  let H := graphLocalGroup (family P) v
  let E := stabilizer (family P) v ⊓ stabilizer (family P) w
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 H := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 H) x) = 1 ↔ x ∈ pCore 2 H
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  obtain ⟨U, hU⟩ := local_edge_sylow h hB hS hvw
  let T := U.mapSurjective (f := q) hq
  have hcoreH : E.pCoreIn 2 ≤ H := hU.ge.trans (map_subtype_le _)
  have heU : (U : Subgroup H) = (E.pCoreIn 2).subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hcoreH]
    exact hU
  have hn : (normalizer (T : Set D)).comap q = normalizer (U : Set H) := by
    change (normalizer ((U : Subgroup H).map q : Set D)).comap q = _
    rw [comap_normalizer_eq_of_surjective _ hq,
      comap_map_eq_self (show q.ker ≤ (U : Subgroup H) by
        rw [hker]; exact pCore_isPGroup.le_sylow_of_normal U)]
    rfl
  refine ⟨T, ?_⟩
  intro l
  change l ∈ (normalizer (T : Set D)).comap q ↔ _
  rw [hn]
  change l ∈ normalizer ((U : Subgroup H) : Set H) ↔ _
  rw [heU, ← subgroupOf_normalizer_eq hcoreH]
  change (l : G) ∈ normalizer (E.pCoreIn 2 : Set G) ↔ _
  have hlR := sylowGenerated_le (stabilizer (family P) v) l.property
  constructor
  · intro hl
    exact ((local_edge_core_normalizer h hB hS hvw).le ⟨hlR, hl⟩).2
  · intro hl
    exact ((local_edge_core_normalizer h hB hS hvw).ge ⟨hlR, hl⟩).2

/-- A binary SL₂ local quotient exchanges any two actual neighbors. The lift lies
in the original local actor and its square lies in the original vertex core. -/
theorem linear_local_neighbor_exchange (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v x y : Vertex (family P)} (hx : (graph (family P)).Adj v x)
    (hy : (graph (family P)).Adj v y)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F)) :
    ∃ t : graphLocalGroup (family P) v, (t : G) • x = y ∧ (t : G) • y = x ∧
      (t : G) * t ∈ Q (family P) v := by
  let := finite_endpoints h
  let H := graphLocalGroup (family P) v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨S, hSfix⟩ := local_quotient_neighbor_stabilizer h hB hS hx e
  obtain ⟨g, hgH, hg⟩ := graphLocalGroup_transitive h hB hS v ⟨x, hx⟩ ⟨y, hy⟩
  let k : H := ⟨g, hgH⟩
  obtain ⟨u, hu, huk⟩ := Matrix.SpecialLinearGroup.sylow_coset_exchange S (q k)
  obtain ⟨t, ht⟩ := hq u
  have hty : (t : G) • y = x := by
    have hh : q (t * k) ∈ normalizer (S : Set SL(2,F)) := by
      rw [q.map_mul, ht]
      exact huk
    have hh' := (hSfix (t * k)).mp hh
    change ((t : G) * g) • x = x at hh'
    rwa [mul_smul, hg] at hh'
  have htt : q (t * t) = 1 := by rw [q.map_mul, ht, hu]
  have httfix : ((t : G) * t) • x = x :=
    (hSfix (t * t)).mp (htt ▸ one_mem _)
  have htx : (t : G) • x = y := by
    apply (MulAction.injective (t : G))
    change (t : G) • ((t : G) • x) = (t : G) • y
    rw [← mul_smul, httfix, hty]
  have htc : t * t ∈ pCore 2 H := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply e.injective
    exact htt.trans e.map_one.symm
  refine ⟨t, htx, hty, ?_⟩
  rw [← graphLocalGroup_core h v]
  exact mem_map_of_mem H.subtype htc

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
