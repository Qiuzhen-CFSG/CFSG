module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CentralLayers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CubicIntersections
public import Theory.SpecificGroups.PSL2.SylowFixedQuotients.Five

/-!
# Comparing the alpha core and center in the mixed Chapter 11 row

The opposite seed maps onto the Sylow four-group in the actual A₅
quotient. Its kernel is Zβ by `CentralLayers`; combined with the cubic
seed index this gives |Zα| = 8 |Zβ|. The adjacent-core intersection maps
into a Sylow four-group at the remote alpha vertex, with kernel the full
neighboring-core intersection Iβ. Thus |Qα| ≤ 8 |Iβ|. Once Iβ = Zβ,
these comparisons prove Qα = Zα by inclusion and finite cardinality.

The two-core is kept distinct from the full local kernel. Finite vertex
stabilizers suffice; the ambient completion may be infinite. The literal
mixed-pair application and its original-Sylow count are in `MixedCentralLayers`.
Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.5)--(11.7), printed pp.172--175.
-/
public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem core_sup_index (Q C : Subgroup G)
    (hCQ : C ≤ normalizer (Q : Set G)) : Q.relIndex (Q ⊔ C) = Q.relIndex C := by
  let H := Q ⊔ C
  let : (Q.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le Q.le_normalizer hCQ)
  have he := relIndex_sup_left (C.subgroupOf H) (Q.subgroupOf H)
  rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at he
  exact he

private theorem a5_core_index {H : Type*} [Group H] [Finite H]
    (e : (H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 5)) (T : Sylow 2 H) :
    (pCore 2 H).relIndex T = 4 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    ext x
    change e ((QuotientGroup.mk' (pCore 2 H)) x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff x
  rw [←hk,relIndex_ker]
  exact Theory.PSL2.SylowFixedQuotients.alternating_sylow_card (T.mapSurjective hq)

private theorem source_a5_edge_core_index (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5)) :
    (Q (family P) a).relIndex ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) = 4 := by
  let := finite_endpoints h
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow h hS hab
  have he := sylow_image_eq_edge_core (stabilizer (family P) a)
    (stabilizer (family P) a ⊓ stabilizer (family P) b) inf_le_left
    (source_edge_core_sylow h hB hab) T hT
  rw [←he]
  change ((pCore 2 (stabilizer (family P) a)).map (stabilizer (family P) a).subtype).relIndex _ = _
  rw [relIndex_map_map_of_injective _ _ (stabilizer (family P) a).subtype_injective]
  exact a5_core_index e T

/-- The alpha center has eight times the order of the beta center. -/
theorem source_cubic_a5_center_card_ratio (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5)) :
    Nat.card (Z (family P) a) = 8 * Nat.card (Z (family P) b) := by
  let := finite_endpoints h
  let C := Z (family P) c ⊓ Q (family P) b
  let : Finite C := Finite.of_injective
    (inclusion (inf_le_right.trans (Q_le_stabilizer _ b))) (inclusion_injective _)
  have hab := source_critical_one_adjacent hc hb
  have hi := source_a5_edge_core_index h hB hS hab e
  have hCQa : C ≤ normalizer (Q (family P) a : Set G) :=
    inf_le_right.trans (source_adjacent_core_normalizes_core h hab.symm)
  rw [source_cubic_a5_edge_core_eq_seed_sup_core h hB hS hc hb hbc hac hcard e,
    sup_comm,core_sup_index _ C hCQa] at hi
  have hic : Q (family P) a ⊓ C = Z (family P) b := by
    have he := (source_cubic_core_inf_center h hc hb hbc hac hcard).trans
      (source_cubic_a5_center_intersection h hB hS hc hb hcomm hbc hac hcard e)
    change Q (family P) a ⊓ (Z (family P) c ⊓ Q (family P) b) = _
    rw [←inf_assoc,he,inf_eq_left.mpr ((source_Z_Q_U h b).1.trans (map_subtype_le _))]
  have hZC : Z (family P) b ≤ C := hic ▸ inf_le_right
  have hidx : (Z (family P) b).relIndex C = 4 := by
    rw [←hic,inf_relIndex_right]
    exact hi
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup G) (Z (family P) b) C bot_le hZC
  rw [relIndex_bot_left,relIndex_bot_left,hidx] at hcount
  obtain ⟨g,_,_,_,he⟩ := source_neighbor_conjugate h hab hbc
  have hconj : Nat.card C = Nat.card (Z (family P) a ⊓ Q (family P) b : Subgroup G) := by
    change Nat.card (Z (family P) c ⊓ Q (family P) b : Subgroup G) = _
    rw [←he,card_map_of_injective (MulAut.conj g).injective]
  have hindex := source_cubic_seed_index h hc hb hcard (source_kernel_sylow h hB hS b)
  have hcount' := relIndex_mul_relIndex (⊥ : Subgroup G) (Z (family P) a ⊓ Q (family P) b)
    (Z (family P) a) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hindex,←hconj] at hcount'
  omega


private theorem two_subgroup_a5_core_index_le_four {H : Type*} [Group H] [Finite H]
    (e : (H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 5)) (A : Subgroup H)
    (hp : IsPGroup 2 A) : (pCore 2 H).relIndex A ≤ 4 := by
  obtain ⟨T,hT⟩ := hp.exists_le_sylow
  have hi : (pCore 2 H).relIndex A ≤ (pCore 2 H).relIndex T := by
    rw [←QuotientGroup.ker_mk' (pCore 2 H),relIndex_ker,relIndex_ker]
    exact card_le_of_le (map_mono hT)
  exact hi.trans_eq (a5_core_index e T)

private def quotient_at_neighbor (_h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5)) :
    (stabilizer (family P) c ⧸ pCore 2 (stabilizer (family P) c)) ≃*
      alternatingGroup (Fin 5) := by
  let t := Classical.choose (locally_transitive (family P) hab.symm hbc)
  have hta := (Classical.choose_spec (locally_transitive (family P) hab.symm hbc)).2
  have hs : stabilizer (family P) c = (stabilizer (family P) a).map (MulAut.conj t).toMonoidHom := by
    rw [←hta,stabilizer_translate]
  let es := (MulEquiv.subgroupCongr hs).trans
    ((stabilizer (family P) a).equivMapOfInjective
      (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).symm
  exact (QuotientGroup.congr _ _ es (pCore_map_iso 2 es)).trans e

/-- The alpha core has order at most eight times its neighboring-core intersection. -/
theorem source_cubic_a5_core_card_le_intersection (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5)) :
    Nat.card (Q (family P) a) ≤ 8 * Nat.card (neighborCoreIntersection (family P) b) := by
  let := finite_endpoints h
  let K := Q (family P) a ⊓ Q (family P) b
  let H := stabilizer (family P) c
  let I := neighborCoreIntersection (family P) b
  have hab := source_critical_one_adjacent hc hb
  have hKH : K ≤ H := inf_le_right.trans ((source_Z_Q_U h b).2.trans
    ((ballKernel_one_le_edge _ hbc).trans inf_le_right))
  let : Finite (Q (family P) a) := Finite.of_injective
    (inclusion (Q_le_stabilizer _ a)) (inclusion_injective _)
  let : Finite K := Finite.of_injective (inclusion (show K ≤ Q (family P) a from inf_le_left))
    (inclusion_injective _)
  have hi := two_subgroup_a5_core_index_le_four (quotient_at_neighbor h hab hbc e)
    (K.subgroupOf H) (((isPGroup_pCoreIn 2 _).to_le (show K ≤ Q (family P) a from inf_le_left)).comap_subtype)
  have hi' : (Q (family P) c).relIndex K ≤ 4 := by
    rw [←relIndex_map_map_of_injective _ _ H.subtype_injective,
      map_subgroupOf_eq_of_le hKH] at hi
    exact hi
  have hKI : Q (family P) c ⊓ K = I := by
    have hp := source_cubic_core_pair_eq_neighbor_intersection h hc hb hbc hac hcard
    apply le_antisymm
    · exact (le_inf (inf_le_right.trans inf_le_left) inf_le_left).trans hp.le
    · exact le_inf (neighborCoreIntersection_le _ hbc.symm)
        (le_inf (neighborCoreIntersection_le _ hab) (source_neighborCoreIntersection_le_core h hab))
  have hIK : I ≤ K := hKI ▸ inf_le_right
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup G) I K bot_le hIK
  rw [relIndex_bot_left,relIndex_bot_left] at hcount
  have hidx : I.relIndex K ≤ 4 := by rw [←hKI,inf_relIndex_right];exact hi'
  have hKcard : Nat.card K ≤ Nat.card I * 4 :=
    hcount.symm.trans_le (Nat.mul_le_mul_left _ hidx)
  have hkernel := source_kernel_sylow h hB hS b
  obtain ⟨hN,hquot,_⟩ := source_cubic_edge_core_quotient h hc hb hcard hkernel
  have hindex : (Q (family P) b).relIndex
      ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) = 2 := hquot
  rw [source_cubic_edge_core_eq_cores h hc hb hcard hkernel,sup_comm,
    core_sup_index _ _ (source_adjacent_core_normalizes_core h hab)] at hindex
  have hKindex : K.relIndex (Q (family P) a) = 2 := by
    change (Q (family P) a ⊓ Q (family P) b).relIndex (Q (family P) a) = 2
    rw [inf_relIndex_left]
    exact hindex
  have hcount' := relIndex_mul_relIndex (⊥ : Subgroup G) K (Q (family P) a) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hKindex] at hcount'
  change Nat.card (Q (family P) a) ≤ 8 * Nat.card I
  omega


/-- The neighboring-core identity forces Qα = Zα in the cubic A₅ branch. -/
theorem source_cubic_a5_core_eq_center_of_intersection (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5))
    (hi : neighborCoreIntersection (family P) b = Z (family P) b) :
    Q (family P) a = Z (family P) a := by
  let := finite_endpoints h
  let : Finite (Q (family P) a) := Finite.of_injective
    (inclusion (Q_le_stabilizer _ a)) (inclusion_injective _)
  have hbound := source_cubic_a5_core_card_le_intersection h hB hS hc hb hbc hac hcard e
  have hratio := source_cubic_a5_center_card_ratio h hB hS hc hb hcomm hbc hac hcard e
  rw [hi,←hratio] at hbound
  exact (eq_of_le_of_card_ge ((source_Z_Q_U h a).1.trans (map_subtype_le _)) hbound).symm

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
