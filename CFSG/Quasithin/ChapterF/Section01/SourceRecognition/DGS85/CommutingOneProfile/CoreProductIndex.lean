module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedPairCoreSpan

/-!
# The two local calculations of the Chapter 11 core-product index

The general pair-core span and the opposite-seed omega calculation identify
Q_beta Q_alpha / Q_alpha with the full omega-center of the alpha Sylow.
Thus the literal index t = |S : Q_alpha Q_beta| is the index of that
omega-center. At beta, the critical-center image lies in the alpha-core
image and gives the opposite inequality for t. These calculations do not
select either endpoint, and use the product rather than the intersection
as the denominator.

The source-path application supplies the Cartan invariance from 6.7.
CoreProductOrders evaluates these indices in the actual nonlinear models;
the remaining module-size comparison of (11.3)(g) is still needed to
finish general (11.4). The already proved elementary branch is unchanged.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(c,h) and (11.4), printed pp.169--172.
-/

public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The beta core has exactly the alpha Sylow omega-center as its image. -/
theorem source_beta_core_image_omega_of_supplement
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hcover : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 ⊔
      ((stabilizer (family P) a ⊓ stabilizer (family P) b) ⊓ stabilizer (family P) c) =
        stabilizer (family P) a ⊓ stabilizer (family P) b)
    (T : Sylow 2 (d.localGroup a))
    (hT : (T : Subgroup (d.localGroup a)).map (d.localGroup a).subtype =
      (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) :
    ((Q (family P) b).subgroupOf (d.localGroup a)).map
        (QuotientGroup.mk' (pCore 2 (d.localGroup a))) =
      omegaCenterIn ((T : Subgroup (d.localGroup a)).map
        (QuotientGroup.mk' (pCore 2 (d.localGroup a)))) := by
  let L := d.localGroup a
  let q := QuotientGroup.mk' (pCore 2 L)
  let E := Z (family P) a ⊓ Q (family P) b
  let F := Z (family P) c ⊓ Q (family P) b
  let I := Q (family P) a ⊓ Q (family P) b
  have hab := source_critical_one_adjacent hc hb
  have hQbS : Q (family P) b ≤ (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 := by
    simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab.symm
  have hQbL : Q (family P) b ≤ L := hQbS.trans (hT ▸ map_subtype_le _)
  have hqbot (A : Subgroup G) (hA : A ≤ Q (family P) a) : (A.subgroupOf L).map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
    intro x hx
    obtain ⟨y,hy,he⟩ := (show x.val ∈ (pCore 2 L).map L.subtype by
      change x.val ∈ (d.localGroup a).pCoreIn 2
      rw [localGroup_core_eq (family P) d a]; exact hA hx)
    exact (Subtype.ext he : y = x) ▸ hy
  have hcore := source_rankOne_pair_core_span_of_supplement h hB d hc hb hbc hac Ma Mb hcover
  change Q (family P) b = (E ⊔ F) ⊔ I at hcore
  have him := congrArg (fun A : Subgroup G => (A.subgroupOf L).map q) hcore
  rw [subgroupOf_sup (sup_le (inf_le_right.trans hQbL) (inf_le_right.trans hQbL))
      (inf_le_right.trans hQbL),subgroupOf_sup (inf_le_right.trans hQbL) (inf_le_right.trans hQbL),
    Subgroup.map_sup,Subgroup.map_sup,
    hqbot E (inf_le_left.trans ((source_Z_Q_U h a).1.trans (map_subtype_le _))),
    hqbot I inf_le_left,bot_sup_eq,sup_bot_eq] at him
  exact him.trans (source_opposite_seed_image_omega_of_supplement h hB d hc hb hbc hac Ma Mb hcover T hT)

private theorem local_core_product_index
    (h : LocallyRankOneTriple P B) (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (T : Sylow 2 (d.localGroup a))
    (hT : (T : Subgroup (d.localGroup a)).map (d.localGroup a).subtype =
      (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) :
    (Q (family P) a ⊔ Q (family P) b).relIndex
      ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) =
      (((Q (family P) b).subgroupOf (d.localGroup a)).map
        (QuotientGroup.mk' (pCore 2 (d.localGroup a)))).relIndex
      ((T : Subgroup (d.localGroup a)).map (QuotientGroup.mk' (pCore 2 (d.localGroup a)))) := by
  let L := d.localGroup a
  let q := QuotientGroup.mk' (pCore 2 L)
  have hQS : Q (family P) b ≤ (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 := by
    simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab.symm
  have hQL : Q (family P) b ≤ L := hQS.trans (hT ▸ map_subtype_le _)
  rw [relIndex_map_map,QuotientGroup.ker_mk',
    sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal T)]
  rw [←relIndex_map_map_of_injective _ _ L.subtype_injective,
    Subgroup.map_sup,map_subgroupOf_eq_of_le hQL]
  have hcore : (pCore 2 L).map L.subtype = Q (family P) a := localGroup_core_eq (family P) d a
  rw [hcore,hT,sup_comm]

/-- The source index t is the index of the full omega-center in the alpha Sylow. -/
theorem source_core_product_index_eq_alpha_omega_of_supplement
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hcover : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 ⊔
      ((stabilizer (family P) a ⊓ stabilizer (family P) b) ⊓ stabilizer (family P) c) =
        stabilizer (family P) a ⊓ stabilizer (family P) b)
    (T : Sylow 2 (d.localGroup a))
    (hT : (T : Subgroup (d.localGroup a)).map (d.localGroup a).subtype =
      (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) :
    (Q (family P) a ⊔ Q (family P) b).relIndex
      ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) =
      (omegaCenterIn ((T : Subgroup (d.localGroup a)).map
        (QuotientGroup.mk' (pCore 2 (d.localGroup a))))).relIndex
      ((T : Subgroup (d.localGroup a)).map (QuotientGroup.mk' (pCore 2 (d.localGroup a)))) := by
  rw [local_core_product_index h d (source_critical_one_adjacent hc hb) T hT,
    source_beta_core_image_omega_of_supplement h hB d hc hb hbc hac Ma Mb hcover T hT]

/-- At beta, the critical center gives the complementary upper bound for t. -/
theorem source_core_product_index_le_beta_omega
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (T : Sylow 2 (d.localGroup b))
    (hT : (T : Subgroup (d.localGroup b)).map (d.localGroup b).subtype =
      (stabilizer (family P) b ⊓ stabilizer (family P) a).pCoreIn 2) :
    (Q (family P) a ⊔ Q (family P) b).relIndex
      ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ≤
      (omegaCenterIn ((T : Subgroup (d.localGroup b)).map
        (QuotientGroup.mk' (pCore 2 (d.localGroup b))))).relIndex
      ((T : Subgroup (d.localGroup b)).map (QuotientGroup.mk' (pCore 2 (d.localGroup b)))) := by
  let := finite_endpoints h
  let L := d.localGroup b
  let : Finite L := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  let : Finite (L ⧸ pCore 2 L) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  rw [sup_comm (Q (family P) a),inf_comm (stabilizer (family P) a),
    local_core_product_index h d (source_critical_one_adjacent hc hb).symm T hT,
    ←source_rankOne_center_image_omega h hB d hc hb Mb T hT]
  apply relIndex_le_of_le_left
  · exact map_mono (comap_mono ((source_Z_Q_U h a).1.trans (map_subtype_le _)))
  · exact index_ne_zero_of_finite

private theorem local_image_card (d : EarlierLocalTheorems (family P))
    (a : Vertex (family P)) (A : Subgroup G) (hA : A ≤ d.localGroup a) :
    Nat.card ((A.subgroupOf (d.localGroup a)).map (QuotientGroup.mk' (pCore 2 (d.localGroup a)))) =
      (Q (family P) a).relIndex A := by
  rw [←relIndex_ker,QuotientGroup.ker_mk',
    ←relIndex_map_map_of_injective _ _ (d.localGroup a).subtype_injective,
    map_subgroupOf_eq_of_le hA]
  exact congrArg (fun R : Subgroup G => R.relIndex A) (localGroup_core_eq (family P) d a)

open SimpleGraph SimpleGraph.PathTransitivePolygon

/-- Both calculations of the source index on the actual path. The alpha
calculation is an equality; the beta calculation is an upper bound. -/
theorem source_core_product_indices_on_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    {v : Vertex (family P)} {n : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (n+1))
    (p : BasedWalk (graph (family P)) (n+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) :
    let t := (Q (family P) a ⊔ Q (family P) b).relIndex
      ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)
    ∃ Ta : Sylow 2 (d.localGroup a ⧸ pCore 2 (d.localGroup a)),
      ∃ Tb : Sylow 2 (d.localGroup b ⧸ pCore 2 (d.localGroup b)),
        t = (omegaCenterIn (Ta : Subgroup (d.localGroup a ⧸ pCore 2 (d.localGroup a)))).relIndex (Ta : Subgroup _) ∧
        t ≤ (omegaCenterIn (Tb : Subgroup (d.localGroup b ⧸ pCore 2 (d.localGroup b)))).relIndex (Tb : Subgroup _) ∧
        Nat.card (omegaCenterIn (Ta : Subgroup (d.localGroup a ⧸ pCore 2 (d.localGroup a)))) =
          (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b) ∧
        Nat.card (omegaCenterIn (Tb : Subgroup (d.localGroup b ⧸ pCore 2 (d.localGroup b)))) =
          (Q (family P) b).relIndex (Z (family P) a) := by
  let := finite_endpoints h
  let : Finite (d.localGroup a) := Finite.of_injective (inclusion (d.local_le a)) (inclusion_injective _)
  let : Finite (d.localGroup b) := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨Ta,hTa⟩ := source_edge_core_local_sylow h hB d hab
  obtain ⟨Tb,hTb⟩ := source_edge_core_local_sylow h hB d hab.symm
  refine ⟨Ta.mapSurjective (QuotientGroup.mk'_surjective _),
    Tb.mapSurjective (QuotientGroup.mk'_surjective _),?_,?_,?_,?_⟩
  · exact source_core_product_index_eq_alpha_omega_of_supplement h hB d hc hb hbc hac Ma Mb
      (source_opposite_seed_path_supplement h hB ht p hp hab ha hb' hc') Ta hTa
  · exact source_core_product_index_le_beta_omega h hB d hc hb Mb Tb hTb
  · change Nat.card (omegaCenterIn ((Ta : Subgroup (d.localGroup a)).map
      (QuotientGroup.mk' (pCore 2 (d.localGroup a))))) = _
    rw [←source_opposite_seed_image_omega_of_supplement h hB d hc hb hbc hac Ma Mb
      (source_opposite_seed_path_supplement h hB ht p hp hab ha hb' hc') Ta hTa]
    apply local_image_card
    exact inf_le_right.trans ((show Q (family P) b ≤
      (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 from
      by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab.symm).trans
        (hTa ▸ map_subtype_le _))
  · change Nat.card (omegaCenterIn ((Tb : Subgroup (d.localGroup b)).map
      (QuotientGroup.mk' (pCore 2 (d.localGroup b))))) = _
    rw [←source_rankOne_center_image_omega h hB d hc hb Mb Tb hTb]
    apply local_image_card
    exact ((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
      ((show Q (family P) a ≤ (stabilizer (family P) b ⊓ stabilizer (family P) a).pCoreIn 2 from
        by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab).trans
          (hTb ▸ map_subtype_le _))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

