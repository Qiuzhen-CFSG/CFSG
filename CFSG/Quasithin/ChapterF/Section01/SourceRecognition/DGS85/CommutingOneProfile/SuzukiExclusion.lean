module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SuzukiCoreGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SourceCenterOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.GraphExclusions

/-!
# Suzuki exclusion and the actual unitary beta alternative

In the Suzuki row, the pair-core orbit identifies Q_alpha intersect
Q_gamma with the full neighboring-core intersection. The proved (11.6)(a)
identifies it with Z_beta. The adjacent-core identity and (11.3)(h) then
give Q_beta=V_beta, its exact source order, and an elementary S/Q_beta
by the Frattini argument. Every Suzuki Sylow, including Sz(2), has
nontrivial index over its omega-center, so this is impossible.

The actual nonelementary-beta catalogue consequently reduces to U3 or
SU3. Both markings and every positive fixed-field degree are retained.
No core-order, alpha-row, or Suzuki-exclusion hypothesis remains. The
earlier local/catalogue inputs, path transitivity and escaping source-path
choice remain explicit for their source producers and final assembly.
ReducedSuzukiExclusion applies the result through the original inclusion
and on the full original Borel. The remaining (11.8) radical layers,
natural section, field relation and path fixers are separate duties.
Source: DGS85, Groups and Graphs (1985), (11.8)(c) and its Suzuki
contradiction, printed pp.175--176, using (11.3)(h), (11.4) and (11.6).
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open BenderSuzuki.MatrixGroups
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The Suzuki candidate forces its exact pair core and elementary edge quotient. -/
theorem source_suzuki_core_and_elementary_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    (m : ℕ) (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    Q (family P) a ⊓ Q (family P) c = Z (family P) b ∧
      Q (family P) b = pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ∧
      Nat.card (Q (family P) b) =
        ((Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b))^2 *
          (Q (family P) b).relIndex (Z (family P) a) ∧
      ∃ hN : ((Q (family P) b).subgroupOf
          ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)).Normal,
        letI := hN
        IsElementaryAbelian 2 (((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ⧸
          (Q (family P) b).subgroupOf
            ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)) := by
  let Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := .suzuki m ⟨eb⟩
  have hab := source_critical_one_adjacent hc hb
  have hD := (source_suzuki_core_pair_eq_neighbor_intersection h hB d hc hb hbc hac m eb).trans
      (source_neighbor_intersection_eq_center_on_escaping_path h hB hS d hc hb hcomm
        hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp)
  have hZE : Z (family P) b ≤ Z (family P) a ⊓ Q (family P) b := le_inf
    (source_commuting_one_center_le_neighbor h hB hS hc hb hcomm hab.symm)
    ((source_Z_Q_U h b).1.trans (map_subtype_le _))
  have hI := source_pair_adjacent_core_intersection h hB d hc hb hbc hac Mb
  rw [hD,sup_eq_left.mpr hZE] at hI
  have hpair := source_rankOne_pair_core_span_on_path h hB d hc hb hbc hac Ma Mb ht p hp ha hbp hcp
  rw [hI,sup_eq_left.mpr (show Z (family P) a ⊓ Q (family P) b ≤
    pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) from le_sup_left)] at hpair
  have hcount := (source_center_seed_pair_orders_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp).2.2.2
  have hprod := (source_core_product_and_alpha_on_path h hB d hc hb hcomm hbc hac
    Ma Mb ht p hp ha hbp hcp).1
  refine ⟨hD,hpair,(congrArg (fun A : Subgroup G => Nat.card A) hpair).trans hcount,?_⟩
  have he := source_beta_quotient_elementary_of_core_intersection h hab _ hprod
    (hI.le.trans inf_le_left)
  exact ⟨_,he⟩

/-- Every Suzuki marking contradicts the source core geometry, including Sz(2).
The literal S/Q_beta becomes elementary, whereas its marked Sylow has
nontrivial index over its omega-center. -/
theorem source_suzuki_exclusion_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    (m : ℕ) (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : False := by
  let : Finite (d.localGroup b ⧸ pCore 2 (d.localGroup b)) :=
    Finite.of_equiv (SuzukiMatrixGroup m) eb.symm.toEquiv
  obtain ⟨_,_,_,helem⟩ := source_suzuki_core_and_elementary_on_escaping_path
    h hB hS d hc hb hcomm hbc hac Ma g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp m eb
  have helem' : ∃ hN : ((Q (family P) b).subgroupOf
        ((stabilizer (family P) b ⊓ stabilizer (family P) a).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2
        (((stabilizer (family P) b ⊓ stabilizer (family P) a).pCoreIn 2) ⧸
          (Q (family P) b).subgroupOf ((stabilizer (family P) b ⊓ stabilizer (family P) a).pCoreIn 2)) := by
    rw [inf_comm (stabilizer (family P) b) (stabilizer (family P) a)]
    exact helem
  obtain ⟨hN,he⟩ := helem'
  let := hN
  let := he
  obtain ⟨T,⟨e⟩⟩ := source_edge_core_quotient_sylow h hB d (source_critical_one_adjacent hc hb).symm
  let : IsElementaryAbelian 2 T := IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  let U := T.mapSurjective (f := eb.toMonoidHom) eb.surjective
  let : IsElementaryAbelian 2 U :=
    IsElementaryAbelian.map (A := (T : Subgroup (d.localGroup b ⧸ pCore 2 (d.localGroup b)))) eb.toMonoidHom
  have hω : omegaCenterIn (U : Subgroup (SuzukiMatrixGroup m)) = U := by
    apply le_antisymm (map_subtype_le _)
    intro x hx
    exact (mem_omegaCenterIn_iff _ _).mpr ⟨hx,
      fun y hy => congrArg Subtype.val (mul_comm (⟨y,hy⟩ : U) (⟨x,hx⟩ : U)),
      elemPow_eq_one_of_isElementaryAbelian x hx⟩
  have hi := (suzukiSylow_omegaCenter_card_index m U).2
  rw [hω,relIndex_self] at hi
  have hp := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by omega : 2*m+1 ≠ 0)
  omega

/-- Source (11.8)(c): the nonelementary-beta branch has either the projective
or the full special-unitary marking; all Suzuki alternatives are discharged. -/
theorem source_unitary_beta_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    (hne : ∃ hN : ((Q (family P) b).subgroupOf
        ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ⧸
        (Q (family P) b).subgroupOf ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2))) :
    ∃ n, 0 < n ∧ (ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n)) := by
  have hne' : ∃ hN : ((Q (family P) b).subgroupOf
        ((stabilizer (family P) b ⊓ stabilizer (family P) a).pCoreIn 2)).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (((stabilizer (family P) b ⊓ stabilizer (family P) a).pCoreIn 2) ⧸
        (Q (family P) b).subgroupOf ((stabilizer (family P) b ⊓ stabilizer (family P) a).pCoreIn 2)) := by
    rw [inf_comm (stabilizer (family P) b) (stabilizer (family P) a)]
    exact hne
  rcases source_nonlinear_of_nonElementary_edge h hB d
    (source_critical_one_adjacent hc hb).symm Mb hne' with ⟨m,⟨eb⟩⟩ | hu
  · exact (source_suzuki_exclusion_on_escaping_path h hB hS d hc hb hcomm hbc hac Ma
      g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp m eb).elim
  · exact hu

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
