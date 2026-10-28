module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceInvolutions
public import Theory.GroupTheory.InvolutionOddProduct

/-!
# Fixed cosets and the remaining second-centralizer premise

Fusion control and full centralizer containment give uniqueness of a fixed
coset. Apply this first to the marked point class inside the actual generated
subgroup L. If the full centralizer of the second marked involution is also
contained in L, both classes have unique fixed cosets. A proper subgroup with
that property cannot contain two distinct involution classes: the dihedral
argument makes an inside involution conjugate to an outside involution.

This proves the generation and literal SourceComparison consequences of the
remaining centralizer premise in Aschbacher, *Sporadic Groups* (1994), 7.3,
7.5 and 41.1, printed pp.19–20,220. The premise remains explicit here; the
argument inside C_G(t) that discharges it is not assumed.
-/

public noncomputable section
open Subgroup
open Theory.GroupTheory.GraphUniquenessSystem.Cosets
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear

private theorem unique_coset_of_fusion_centralizer {G : Type*} [Group G]
    (H : Subgroup G) (a : H) (hC : centralizer ({(a : G)} : Set G) ≤ H)
    (hF : ∀ b : H, IsConj (a : G) (b : G) → IsConj a b)
    (v : G ⧸ H) (hv : (a : G) • v = v) : v = vertex H 1 := by
  obtain ⟨g, rfl⟩ := transitive H v
  have hv' : (a : G) ∈ MulAction.stabilizer G (vertex H g) := by
    simpa only [smul_vertex, mul_one] using (MulAction.mem_stabilizer_iff.mpr hv)
  rw [stabilizer_vertex] at hv'
  let b : H := ⟨g⁻¹ * (a : G) * g, by simpa [MulAut.conj_apply] using hv'⟩
  obtain ⟨k, hk⟩ := isConj_iff.mp (hF b (isConj_iff.mpr ⟨g⁻¹, by simp [b]⟩))
  have he : (k : G) * (a : G) * (k : G)⁻¹ = g⁻¹ * (a : G) * g :=
    congrArg Subtype.val hk
  have hgk : g * (k : G) ∈ centralizer ({(a : G)} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (fun y : G => g * y * (k : G)) he
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
      inv_mul_cancel, mul_one] using hh
  have hg : g ∈ H := by
    simpa only [mul_inv_cancel_right] using H.mul_mem (hC hgk) (H.inv_mem k.property)
  simpa only [smul_vertex, mul_one] using (vertex_eq_base H g).mpr hg

private theorem centralizer_le_of_subgroup_conj {G : Type*} [Group G]
    (H : Subgroup G) {a b : H} (h : IsConj a b)
    (hc : centralizer ({(a : G)} : Set G) ≤ H) :
    centralizer ({(b : G)} : Set G) ≤ H := by
  obtain ⟨k, hk⟩ := isConj_iff.mp h
  have he := congrArg Subtype.val hk
  change (k : G) * (a : G) * (k : G)⁻¹ = (b : G) at he
  intro g hg
  have hh : (k : G)⁻¹ * g * k ∈ centralizer ({(a : G)} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (fun x : G => (k : G)⁻¹ * x * k)
      (mem_centralizer_singleton_iff.mp hg)
    rw [← he] at hh
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
      mul_inv_cancel, one_mul, inv_mul_cancel, mul_one] using hh
  have hm := H.mul_mem (H.mul_mem k.property (hc hh)) (H.inv_mem k.property)
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using hm

private theorem commuting_involution_in_product {G : Type*} [Group G] [Finite G]
    {s t : G} (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) (he : Even (orderOf (s * t))) :
    ∃ w : G, orderOf w = 2 ∧ Commute s w ∧ Commute t w := by
  have hdiv : 2 ∣ Nat.card (zpowers (s * t)) := by
    simpa only [Nat.card_zpowers] using he.two_dvd
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := zpowers (s * t)) 2 hdiv
  have hwo : orderOf (w : G) = 2 := (Subgroup.orderOf_coe w).trans hw
  have hwi : (w : G)⁻¹ = w := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two, hwo] using pow_orderOf_eq_one (w : G))
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs)
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ht)
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp w.property
  have hss : s * s = 1 := by simpa only [pow_two] using hs
  have hsemS : SemiconjBy s (s * t) (s * t)⁻¹ := by
    change s * (s * t) = (s * t)⁻¹ * s
    rw [mul_inv_rev, hsi, hti, ← mul_assoc, hss, one_mul,
      mul_assoc, hss, mul_one]
  have hsemT : SemiconjBy t (s * t) (s * t)⁻¹ := by
    change t * (s * t) = (s * t)⁻¹ * t
    simp [mul_inv_rev, hsi, hti, mul_assoc]
  refine ⟨w, hwo, ?_, ?_⟩
  · have hh := hsemS.zpow_right n
    apply (commute_iff_eq _ _).mpr
    simpa only [inv_zpow, hn, hwi] using hh.eq
  · have hh := hsemT.zpow_right n
    apply (commute_iff_eq _ _).mpr
    simpa only [inv_zpow, hn, hwi] using hh.eq

private theorem top_of_two_classes_unique_fixed {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (a b : H) (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hne : ¬ IsConj (a : G) (b : G))
    (hfix : ∀ x : G, orderOf x = 2 → ∃! v : G ⧸ H, x • v = v) : H = ⊤ := by
  apply top_unique
  intro g _
  by_contra hg
  let v₀ : G ⧸ H := vertex H 1
  have hbase (x : H) : (x : G) • v₀ = v₀ := by
    simpa only [v₀, smul_vertex, mul_one] using (vertex_eq_base H x).mpr x.property
  have haG : orderOf (a : G) = 2 := (Subgroup.orderOf_coe a).trans ha
  have hbG : orderOf (b : G) = 2 := (Subgroup.orderOf_coe b).trans hb
  let u := g * (a : G) * g⁻¹
  have hu : orderOf u = 2 := ((MulAut.conj g).orderOf_eq (a : G)).trans haG
  have hug : u • (g • v₀) = g • v₀ := by
    simp only [u, mul_smul, inv_smul_smul, hbase]
  have huH : u ∉ H := by
    intro hm
    have h := (hfix u hu).unique hug (hbase ⟨u, hm⟩)
    exact hg ((vertex_eq_base H g).mp (by simpa only [v₀, smul_vertex, mul_one] using h))
  have ho : Odd (orderOf ((b : G) * u)) := by
    apply Nat.not_even_iff_odd.mp
    intro he
    obtain ⟨w, hw, hbw, huw⟩ := commuting_involution_in_product
      (by simpa only [hbG] using pow_orderOf_eq_one (b : G))
      (by simpa only [hu] using pow_orderOf_eq_one u) he
    obtain ⟨v, hv, hvunique⟩ := hfix w hw
    have move {c : G} (hc : Commute c w) : c • v = v := by
      apply hvunique
      rw [← mul_smul, ← hc.eq, mul_smul, hv]
    have hvbase : v = v₀ := (hfix (b : G) hbG).unique (move hbw) (hbase b)
    have huBase : u • v₀ = v₀ := hvbase ▸ move huw
    apply huH
    exact (vertex_eq_base H u).mp (by simpa only [v₀, smul_vertex, mul_one] using huBase)
  have hbu := isConj_of_involutions_odd_product (b : G) u
    (by simpa only [hbG] using pow_orderOf_eq_one (b : G))
    (by simpa only [hu] using pow_orderOf_eq_one u) ho
  exact hne ((isConj_iff.mpr ⟨g, rfl⟩ : IsConj (a : G) u).trans hbu.symm)

private theorem unique_coset_restrict {G : Type*} [Group G]
    (H M : Subgroup G) (a : M)
    (hunique : ∀ v : G ⧸ H, (a : G) • v = v → v = vertex H 1)
    (v : M ⧸ H.subgroupOf M) (hv : a • v = v) :
    v = vertex (H.subgroupOf M) 1 := by
  obtain ⟨g, rfl⟩ := transitive (H.subgroupOf M) v
  have hm : a ∈ MulAction.stabilizer M (vertex (H.subgroupOf M) g) := by
    simpa only [smul_vertex, mul_one] using (MulAction.mem_stabilizer_iff.mpr hv)
  rw [stabilizer_vertex] at hm
  have hm' : (g : G)⁻¹ * (a : G) * g ∈ H := by
    simpa [Subgroup.mem_comap, Subgroup.mem_subgroupOf, MulAut.conj_apply] using hm
  have hgfix : (a : G) • vertex H (g : G) = vertex H (g : G) := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [stabilizer_vertex]
    simpa [Subgroup.mem_comap, Subgroup.mem_subgroupOf, MulAut.conj_apply] using hm'
  have hgH : (g : G) ∈ H := (vertex_eq_base H g).mp (hunique _ hgfix)
  simpa only [smul_vertex, mul_one] using (vertex_eq_base (H.subgroupOf M) g).mpr hgH

variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

/-- The class of the marked point has no fusion outside the generated
subgroup when both endpoints lie in that subgroup. -/
theorem normalizerSpan_point_fusion (hlinear : F.LinearFusion)
    (a : normalizerSpan F) (ha : IsConj z (a : G)) :
    IsConj (overgroupPoint (normalizerSpan F) (point_centralizer_le_normalizerSpan F)) a := by
  apply normalizerSpan_involution_fusion F hlinear _ a
    (normalizerSpanMarking F).point_orderOf
  · obtain ⟨g, hg⟩ := isConj_iff.mp ha
    have ho : orderOf (a : G) = 2 := by
      rw [← hg]
      exact ((MulAut.conj g).orderOf_eq z).trans F.point_orderOf
    exact (Subgroup.orderOf_coe a).symm.trans ho
  · simpa only [overgroupPoint_val] using ha

/-- Every returning conjugate of the distinguished point has its full
ambient centralizer inside the actual normalizer-generated subgroup. -/
theorem normalizerSpan_point_centralizer_le (hlinear : F.LinearFusion)
    (a : normalizerSpan F) (ha : IsConj z (a : G)) :
    centralizer ({(a : G)} : Set G) ≤ normalizerSpan F :=
  centralizer_le_of_subgroup_conj _ (normalizerSpan_point_fusion F hlinear a ha)
    (by simpa only [overgroupPoint_val] using point_centralizer_le_normalizerSpan F)

/-- Source 7.3 applied to the first involution class in 41.1: the literal
identity coset in G/L is its unique fixed point. -/
theorem normalizerSpan_point_unique_fixed (hlinear : F.LinearFusion)
    (a : normalizerSpan F) (ha : IsConj z (a : G))
    (v : G ⧸ normalizerSpan F) (hv : (a : G) • v = v) :
    v = vertex (normalizerSpan F) 1 := by
  apply unique_coset_of_fusion_centralizer _ a
    (normalizerSpan_point_centralizer_le F hlinear a ha) ?_ v hv
  intro b hab
  exact (normalizerSpan_point_fusion F hlinear a ha).symm.trans
    (normalizerSpan_point_fusion F hlinear b (ha.trans hab))

/-- The same unique fixed coset survives restriction to the literal full
centralizer of an arbitrary element. For the second marked involution this
is precisely the action of M=C_G(t) on M/(L∩M) in source 41.1. -/
theorem normalizerSpan_point_unique_fixed_in_centralizer (hlinear : F.LinearFusion)
    (t : G) (a : centralizer ({t} : Set G)) (haL : (a : G) ∈ normalizerSpan F)
    (ha : IsConj z (a : G))
    (v : centralizer ({t} : Set G) ⧸ (normalizerSpan F).subgroupOf (centralizer ({t} : Set G)))
    (hv : a • v = v) :
    v = vertex ((normalizerSpan F).subgroupOf (centralizer ({t} : Set G))) 1 := by
  apply unique_coset_restrict (normalizerSpan F) (centralizer ({t} : Set G)) a ?_ v hv
  intro w hw
  exact normalizerSpan_point_unique_fixed F hlinear ⟨a, haL⟩ ha w hw

/-- Every involution has a unique fixed coset once the second class's full
ambient centralizer is contained. The first-class centralizer and both fusion
conditions have already been proved from the original marking and counts. -/
theorem normalizerSpan_all_involution_unique_fixed (hlinear : F.LinearFusion)
    (hsecond : centralizer ({planeSecondPoint F} : Set G) ≤ normalizerSpan F)
    (x : G) (hx : orderOf x = 2) :
    ∃! v : G ⧸ normalizerSpan F, x • v = v := by
  let L := normalizerSpan F
  have hsecond' : centralizer ({((planeSecondPoint (normalizerSpanMarking F) : L) : G)} : Set G) ≤ L := by
    rw [normalizerSpan_secondPoint_val]
    exact hsecond
  have hcentral (a : L) (ha : orderOf a = 2) :
      centralizer ({(a : G)} : Set G) ≤ L := by
    rcases normalizerSpan_two_involution_classes F hlinear a ha with hp | ht
    · exact centralizer_le_of_subgroup_conj L hp (by simpa only [overgroupPoint_val] using point_centralizer_le_normalizerSpan F)
    · exact centralizer_le_of_subgroup_conj L ht hsecond'
  have hbase (a : L) : (a : G) • vertex L 1 = vertex L 1 := by
    simpa only [smul_vertex, mul_one] using (vertex_eq_base L a).mpr a.property
  have hunique (a : L) (ha : orderOf a = 2) (v : G ⧸ L) (hv : (a : G) • v = v) :
      v = vertex L 1 := by
    apply unique_coset_of_fusion_centralizer L a (hcentral a ha) ?_ v hv
    intro b hab
    have hb : orderOf b = 2 := by
      obtain ⟨g, hg⟩ := isConj_iff.mp hab
      have ho := (MulAut.conj g).orderOf_eq (a : G)
      change orderOf (g * (a : G) * g⁻¹) = orderOf (a : G) at ho
      rw [hg, Subgroup.orderOf_coe, Subgroup.orderOf_coe, ha] at ho
      exact ho
    exact normalizerSpan_involution_fusion F hlinear a b ha hb hab
  obtain ⟨a, ha⟩ := involution_conjugate_into_normalizerSpan F x hx
  obtain ⟨g, hg⟩ := isConj_iff.mp ha
  have hao : orderOf a = 2 := by
    have hh := (MulAut.conj g).orderOf_eq x
    change orderOf (g * x * g⁻¹) = orderOf x at hh
    rwa [hg, Subgroup.orderOf_coe, hx] at hh
  refine ⟨g⁻¹ • vertex L 1, ?_, ?_⟩
  · apply (MulAction.injective g)
    have hh := hbase a
    rw [← hg, mul_smul, mul_smul] at hh
    simpa only [smul_inv_smul] using hh
  · intro v hv
    have hav : (a : G) • (g • v) = g • v := by
      rw [← hg, mul_smul, mul_smul, inv_smul_smul, hv]
    exact (eq_inv_smul_iff).mpr (hunique a hao _ hav)

/-- The source generation argument now needs just the second involution's
full ambient centralizer. Two distinct involution classes rule out a proper
subgroup in which every involution has a unique fixed coset. -/
theorem normalizerSpan_eq_top_of_second_centralizer (hlinear : F.LinearFusion)
    (hsecond : centralizer ({planeSecondPoint F} : Set G) ≤ normalizerSpan F) :
    normalizerSpan F = ⊤ := by
  apply top_of_two_classes_unique_fixed (normalizerSpan F)
    (overgroupPoint (normalizerSpan F) (point_centralizer_le_normalizerSpan F))
    (planeSecondPoint (normalizerSpanMarking F))
    (normalizerSpanMarking F).point_orderOf (planeSecondPoint_order _)
  · intro h
    apply planeSecondPoint_not_conjugate F hlinear
    simpa only [overgroupPoint_val, normalizerSpan_secondPoint_val] using h
  · exact normalizerSpan_all_involution_unique_fixed F hlinear hsecond

/-- Literal ambient generation by the row and three-space normalizers,
conditional only on the remaining second-class centralizer containment. -/
theorem normalizer_generation_of_second_centralizer (hlinear : F.LinearFusion)
    (hsecond : centralizer ({planeSecondPoint F} : Set G) ≤ normalizerSpan F) :
    rowNormalizer F ⊔ sourceThreeSpaceNormalizer F = ⊤ := by
  have hh := normalizerSpan_eq_top_of_second_centralizer F hlinear hsecond
  rw [normalizerSpan_eq, SourceGeometry.normalizer_span_eq F hlinear] at hh
  exact hh

/-- Apply the fixed-coset generation argument to the original source comparison.
The second involution centralizer is an explicit, still-undischarged premise. -/
theorem nonempty_sourceComparison_of_second_centralizer (hlinear : F.LinearFusion)
    (hsecond : centralizer ({planeSecondPoint F} : Set G) ≤ normalizerSpan F) :
    Nonempty (SourceComparison F) :=
  nonempty_sourceComparison_of_generation F hlinear
    (normalizer_generation_of_second_centralizer F hlinear hsecond)

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
