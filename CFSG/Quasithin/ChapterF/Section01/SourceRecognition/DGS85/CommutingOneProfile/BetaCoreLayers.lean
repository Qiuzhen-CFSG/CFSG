module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SourceCenterOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.GraphExclusions
public import Theory.GroupTheory.CommutatorPreimageFrattini

/-!
# Central elementary quotients of the full beta core

The proved pair span and edge-core product make S/Q_alpha elementary.
Its restriction puts the Frattini subgroup of Q_beta in Q_alpha.
Characteristic invariance and beta-star transitivity place that subgroup
in every neighboring alpha core. The escaping-path identity I_beta=Z_beta
therefore makes the literal Q_beta/Z_beta elementary, with central derived
subgroup and exponent dividing four. The nonabelian pair proves that the
whole core has nontrivial derived subgroup.

In the nonelementary S/Q_beta branch, equality of the whole core with its
two-seed span would put the adjacent-core intersection in Z_alpha, forcing
S/Q_beta elementary. The checked seed count thus gives the strict bounds
|Q_beta|>q_alpha² q_beta and |Q_beta:Z_beta|>q_alpha².
ReducedBetaCoreLayers applies both conclusions under the original inclusion
and retains both unitary quotient markings. No equality of the Frattini,
derived and central layers, or exact unitary core order, is assumed or
claimed. Those remaining (11.8) duties stay with the source assembly.
Source: DGS85, Groups and Graphs (1985), (11.3)(e,h), (11.4)--(11.6)
and (11.8), printed pp.169--176.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem beta_frattini_le_intersection
    (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hprod : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      Q (family P) a ⊔ Q (family P) b)
    (hcore : Q (family P) b = pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ⊔
      (Q (family P) a ⊓ Q (family P) b)) :
    (frattini (Q (family P) b)).map (Q (family P) b).subtype ≤
      neighborCoreIntersection (family P) b := by
  let := finite_endpoints h
  let R := Q (family P) b
  let S := (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2
  let N := (frattini R).map R.subtype
  let : Finite R := Finite.of_injective (inclusion (Q_le_stabilizer _ b)) (inclusion_injective _)
  let : Finite S := Finite.of_injective
    (inclusion ((pCoreIn_le 2 _).trans inf_le_left)) (inclusion_injective _)
  let : IsElementaryAbelian 2 (Z (family P) c) := source_center_elementary h c
  let : ((Q (family P) a).subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer
    (((pCoreIn_le 2 _).trans inf_le_left).trans (stabilizer_normalizes_Q _ a))
  let T := S ⧸ (Q (family P) a).subgroupOf S
  let : IsElementaryAbelian 2 T := alpha_quotient_elementary_of_pair_generation
    _ _ _ _ _ hprod hcore ((source_Z_Q_U h a).1.trans (map_subtype_le _))
  let f : R →* T := (QuotientGroup.mk' ((Q (family P) a).subgroupOf S)).comp
    (inclusion (show R ≤ S from by rw [show S = _ from hprod]; exact le_sup_right))
  let : Fact (IsPGroup 2 R) := ⟨isPGroup_pCoreIn 2 _⟩
  let : Fact (IsPGroup 2 T) := ⟨IsElementaryAbelian.isPGroup 2 T⟩
  have hf := frattini_map_le_of_isPGroup (p := 2) f
  rw [frattini_eq_bot_of_isElementaryAbelian (R := T) (p := 2)] at hf
  have hNa : N ≤ Q (family P) a := by
    rintro x ⟨y,hy,rfl⟩
    have hh : f y = 1 := mem_bot.mp (hf (mem_map_of_mem f hy))
    exact (QuotientGroup.eq_one_iff (N := (Q (family P) a).subgroupOf S) _).mp hh
  have hn : stabilizer (family P) b ≤ normalizer (N : Set G) :=
    (stabilizer_normalizes_Q _ b).trans (normalizer_le_normalizer_characteristic_image R (frattini R))
  intro x hx
  apply mem_iInf.mpr
  intro w
  obtain ⟨t,ht,hta⟩ := locally_transitive (family P) hab.symm w.property
  have hx' := le_normalizer_iff.mp hn t⁻¹ ((stabilizer (family P) b).inv_mem ht) x hx
  have hm := mem_map_of_mem (MulAut.conj t).toMonoidHom (hNa hx')
  rw [←Q_translate,hta] at hm
  simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,mul_assoc,mul_inv_cancel,inv_mul_cancel,one_mul,mul_one,mul_inv_cancel_left] using hm

/-- The whole beta core has a central elementary quotient, with all core
and neighboring-intersection premises discharged on the escaping path. -/
theorem source_beta_core_layers_on_escaping_path
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
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices)  :
    (frattini (Q (family P) b)).map (Q (family P) b).subtype ≤ Z (family P) b ∧
      ⁅Q (family P) b,Q (family P) b⁆ ≤ Z (family P) b ∧
      ⁅⁅Q (family P) b,Q (family P) b⁆,Q (family P) b⁆ = ⊥ ∧
      (∀ x ∈ Q (family P) b, x^4 = 1) ∧
      ⁅Q (family P) b,Q (family P) b⁆ ≠ ⊥ ∧
      ∃ hN : ((Z (family P) b).subgroupOf (Q (family P) b)).Normal,
        letI := hN
        IsElementaryAbelian 2 (Q (family P) b ⧸ (Z (family P) b).subgroupOf (Q (family P) b)) := by
  let := finite_endpoints h
  let R := Q (family P) b
  let : Finite R := Finite.of_injective (inclusion (Q_le_stabilizer _ b)) (inclusion_injective _)
  let hpR : IsPGroup 2 R := isPGroup_pCoreIn 2 _
  let : Fact (IsPGroup 2 R) := ⟨hpR⟩
  have hprod := (source_core_product_and_alpha_on_path h hB d hc hb hcomm hbc hac Ma Mb
    ht p hp ha hbp hcp).1
  have hcore := source_rankOne_pair_core_span_on_path h hB d hc hb hbc hac Ma Mb ht p hp ha hbp hcp
  have hI := source_neighbor_intersection_eq_center_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  have hphi := (beta_frattini_le_intersection h (source_critical_one_adjacent hc hb) hprod hcore).trans hI.le
  have hder : ⁅R,R⁆ ≤ Z (family P) b := by
    rw [←map_subtype_commutator]
    exact (map_mono (commutator_le_frattini_of_isPGroup (p := 2))).trans hphi
  have hcl : ⁅⁅R,R⁆,R⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hder.trans (le_centralizer_iff.mp (source_core_centralizes_center h b)))
  have hpow (x : G) (hx : x ∈ R) : x^4 = 1 := by
    have hs : x^2 ∈ Z (family P) b := hphi
      (mem_map_of_mem R.subtype (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨x,hx⟩ : R)))
    let := source_center_elementary h b
    have hh := elemPow_eq_one_of_isElementaryAbelian (p := 2) (x^2) hs
    simpa only [←pow_mul] using hh
  have hnon : ⁅R,R⁆ ≠ ⊥ := by
    intro he
    have hh := (source_seed_nonquadratic_and_pair_nonabelian_on_path h hB d hc hb hcomm
      hbc hac Ma Mb ht p hp ha hbp hcp).2
    apply hh
    apply bot_unique
    exact (commutator_mono (pairSpan_le_core _ _ _) (pairSpan_le_core _ _ _)).trans he.le
  let hN : ((Z (family P) b).subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer
    ((Q_le_stabilizer _ b).trans ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ b)).mp (Z_normal _ b)))
  refine ⟨hphi,hder,hcl,hpow,hnon,hN,?_⟩
  apply elementary_quotient_of_frattini_le hpR
  intro x hx
  exact hphi (mem_map_of_mem R.subtype hx)

/-- The nonelementary edge quotient forces a strict order gap between the
whole beta core and its two-seed span, also on the literal central quotient. -/
theorem source_nonElementary_beta_core_lower_bound_on_escaping_path
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
    let qα := (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b)
    let qβ := (Q (family P) b).relIndex (Z (family P) a)
    qα^2*qβ < Nat.card (Q (family P) b) ∧
      qα^2 < (Z (family P) b).relIndex (Q (family P) b) := by
  let := finite_endpoints h
  let R := Q (family P) b
  let V := pairSpan (Z (family P) a) (Z (family P) c) R
  let : Finite R := Finite.of_injective (inclusion (Q_le_stabilizer _ b)) (inclusion_injective _)
  have hs := source_center_seed_pair_orders_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  have hprod := (source_core_product_and_alpha_on_path h hB d hc hb hcomm hbc hac Ma Mb
    ht p hp ha hbp hcp).1
  have hbound : Nat.card V < Nat.card R := by
    by_contra hn
    have heq : R = V := (eq_of_le_of_card_ge (pairSpan_le_core _ _ _) (Nat.le_of_not_gt hn)).symm
    have hi := (source_rankOne_pair_core_seed_intersections h hB d hc hb hbc hac Ma Mb).1
    have hle : Q (family P) a ⊓ R ≤ Z (family P) a := by
      rw [heq,hi]
      exact inf_le_left
    obtain ⟨hN,hnon⟩ := hne
    let := hN
    exact hnon (source_beta_quotient_elementary_of_core_intersection h
      (source_critical_one_adjacent hc hb) _ hprod hle)
  have hbound' := hs.2.2.2.symm ▸ hbound
  have hzR : Z (family P) b ≤ R := (source_Z_Q_U h b).1.trans (map_subtype_le _)
  have hcard := relIndex_mul_relIndex (⊥ : Subgroup G) (Z (family P) b) R bot_le hzR
  rw [relIndex_bot_left,relIndex_bot_left,hs.1] at hcard
  refine ⟨hbound',?_⟩
  by_contra hn
  have hm := Nat.mul_le_mul_left ((Q (family P) b).relIndex (Z (family P) a)) (Nat.le_of_not_gt hn)
  rw [hcard] at hm
  nlinarith

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
