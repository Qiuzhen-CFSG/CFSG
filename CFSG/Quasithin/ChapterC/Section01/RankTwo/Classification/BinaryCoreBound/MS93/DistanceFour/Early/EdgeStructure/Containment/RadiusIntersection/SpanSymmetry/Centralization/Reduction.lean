module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.RadiusIntersection.SpanSymmetry.Index

/-!
# Reducing paired fixed-intersection centralization to radius displacement

The escaping span supplies a critical pair starting at the paired midpoint
and passing through the initial vertex. Source (2.2)(iv) makes the join of
these two Z-layers nonnormal in the initial stabilizer. If the midpoint
Z-layer lay in B, the quotient-fixed definition and local generation would
normalize that join. Thus the midpoint Z-layer is not contained in B.

Put D = [U_e,V_a], using the actual natural subgroup and radius. The initial
centrality assertion makes D central in V_a, and critical escape makes it
nontrivial. Its order is two or four. In the order-four case, D is the whole
intersection U_e with B_a: a larger intersection would contain U_e and,
after adjoining the local fixed summand, all of Z_e. Splitting off that
fixed summand proves that Z_e intersect B_a centralizes V_a.

The remaining order-two case is identified precisely: D is the original
order-two displacement [Z_d,Q_a]. These results do not exclude that case
and do not yet prove the unconditional centralization assertion.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (2.2)(iv), printed pp.856--857, and (4.6.4), second paragraph,
printed p.902. All normality is relative to the stated local stabilizer;
no finiteness of the free amalgam is imposed.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanSymmetry
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry)

include common in
/-- Critical escape makes the midpoint Z-layer strictly larger than its B-intersection. -/
theorem paired_midpoint_not_le_B
    (hb : geometry.b R = 4) (a b d : Vertex R) (ha : color R a = false)
    (p : SpanOffender.PairedSpans geometry a b d ha) :
    ¬ Z R p.e ≤ B R a (geometry.Z_normal a) := by
  classical
  have hd : color R d = false := by
    have hh := p.hr
    rw [← p.transport_seed, action_preserves_color] at hh
    exact hh
  have hda : (cosetGraph R).dist d a = 2 := by
    have hh := p.far
    rw [← p.transport_seed, ← p.transport_vertex, dist_act, SimpleGraph.dist_comm] at hh
    exact hh
  obtain ⟨g,hg⟩ : ∃ g : stabilizer R a,
      ¬ (Z R d).map (MulAut.conj (g : FreeAmalgam R)).toMonoidHom ≤ Q R p.e := by
    by_contra! h
    exact p.escape_left (iSup_le h)
  let t := act R (g : FreeAmalgam R)⁻¹ d
  have ht : color R t = false := by simpa only [t, action_preserves_color] using hd
  have hfix : act R (g : FreeAmalgam R)⁻¹ a = a := (stabilizer R a).inv_mem g.property
  have hta : (cosetGraph R).dist t a = 2 := by
    have hh := dist_act R (g : FreeAmalgam R)⁻¹ d a
    simpa only [hfix, hda, t] using hh
  have hesc : ¬ Z R t ≤ Q R p.e := by simpa only [t, Z_act, inv_inv] using hg
  have hte : (cosetGraph R).dist t p.e = 4 := by
    have hlo := criticalDistance_le R t (geometry.exists_critical t ht) hesc
    rw [geometry.distance_constant t ht] at hlo
    change geometry.b R ≤ _ at hlo
    have hhi := (cosetGraph_connected R).dist_triangle (u := t) (v := a) (w := p.e)
    have hn := p.near
    omega
  have hcrit : CriticalPair R t p.e (geometry.exists_critical t ht) :=
    ⟨by rw [geometry.distance_constant t ht]; exact hte.trans hb.symm, hesc⟩
  have hnon := (critical_nonnormal_forward R geometry common.centralizer p.e p.he
    (by rw [geometry.distance_constant p.e p.he]; exact lt_trans (by decide) common.large_distance)
    t (common.critical_reverse t ht p.e p.he hcrit) a
    (by rw [SimpleGraph.dist_comm]; exact p.near) (by
      rw [SimpleGraph.dist_comm (u := a), hta, SimpleGraph.dist_comm (u := p.e), hte])).2
  rw [common.X_eq_Z a ha] at hnon
  intro hB
  apply hnon
  apply normal_subgroupOf_of_le_normalizer
  rw [← source.local_generation a ha]
  apply sup_le
  · apply le_normalizer_iff.mpr
    intro l hl x hx
    have hm : (Z R p.e ⊔ Z R a).map (MulAut.conj l).toMonoidHom ≤ Z R p.e ⊔ Z R a := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨y,hy,rfl⟩
        change l * y * l⁻¹ ∈ Z R p.e ⊔ Z R a
        have hc := ((mem_B_iff R a (geometry.Z_normal a)
          ((radius_le_Q common a ha).trans (fun _ hx => hx.1)) y).mp (hB hy)).2 l hl
        rw [show l * y * l⁻¹ = ⁅l,y⁆ * y by simp [commutatorElement_def, mul_assoc]]
        exact (Z R p.e ⊔ Z R a).mul_mem (mem_sup_right hc) (mem_sup_left hy)
      · rintro _ ⟨y,hy,rfl⟩
        exact mem_sup_right ((Z_normalized R a ((Ltilde_le_stabilizer a) hl) y).mp hy)
    exact hm (mem_map_of_mem (MulAut.conj l).toMonoidHom hx)
  · exact (le_inf
      ((Q_le_stabilizer_of_dist_two R a p.e ha p.near).trans (Z_normalized R p.e))
      ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (Z_normalized R a))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)

private theorem four_subgroup_eq_of_proper {G : Type*} [Group G]
    (U D K : Subgroup G) [Finite U]
    (hU : Nat.card U = 8) (hD : Nat.card D = 4)
    (hDU : D ≤ U) (hDK : D ≤ K) (hnot : ¬ U ≤ K) : U ⊓ K = D := by
  have hDI : D ≤ U ⊓ K := le_inf hDU hDK
  let : Finite (U ⊓ K : Subgroup G) :=
    Finite.of_injective (inclusion (show U ⊓ K ≤ U from inf_le_left)) (inclusion_injective _)
  have hdiv : Nat.card (U ⊓ K : Subgroup G) ∣ 8 := hU ▸ card_dvd_of_le (show U ⊓ K ≤ U from inf_le_left)
  have hne : Nat.card (U ⊓ K : Subgroup G) ≠ 8 := by
    intro h
    have heq : U ⊓ K = U := eq_of_le_of_card_ge inf_le_left (by omega)
    exact hnot (heq ▸ (show U ⊓ K ≤ K from inf_le_right))
  have hh := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1,2,4,8} : Finset ℕ) by decide] at hh
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  exact (eq_of_le_of_card_ge hDI (by omega)).symm

include common in
/-- An order-four radius displacement proves the source fixed-intersection centralization.
The displacement order remains an explicit premise. -/
theorem paired_fixed_centralizes_radius_of_displacement_card
    (initial : InitialFacts R geometry) (hb : geometry.b R = 4)
    (a b d : Vertex R) (ha : color R a = false)
    (p : SpanOffender.PairedSpans geometry a b d ha)
    (hcard : Nat.card (⁅U R p.e,V R a⁆ : Subgroup (FreeAmalgam R)) = 4) :
    Z R p.e ⊓ B R a (geometry.Z_normal a) ≤
      centralizer (V R a : Set (FreeAmalgam R)) := by
  let C := Z R p.e ⊓ centralizer (stabilizer R p.e : Set (FreeAmalgam R))
  let D := ⁅U R p.e,V R a⁆
  have hZeV : Z R p.e ≤ V R a := le_iSup_of_le p.e (le_iSup_of_le
    (by rw [SimpleGraph.dist_comm]; exact p.near.le) le_rfl)
  have hVGe : V R a ≤ stabilizer R p.e := (radius_le_Q common a ha).trans
    (Q_le_stabilizer_of_dist_two R a p.e ha p.near)
  have hDcent : D ≤ (center (V R a)).map (V R a).subtype :=
    (commutator_mono ((U_le_Z p.e).trans hZeV) (radius_le_Q common a ha)).trans
      (initial.commutator_central a ha)
  have hDC : D ≤ centralizer (V R a : Set (FreeAmalgam R)) := by
    rintro x hx v hv
    obtain ⟨z,hz,rfl⟩ := hDcent hx
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨v,hv⟩)
  have hDU : D ≤ U R p.e := le_normalizer_iff_commutator_le_left.mp
    (hVGe.trans (U_normalized p.e))
  have hDB : D ≤ B R a (geometry.Z_normal a) := hDcent.trans (initial.center_le_B a ha)
  have hCB : C ≤ B R a (geometry.Z_normal a) :=
    (midpoint_fixed_le_Z common a p.e ha p.he p.near).trans (Z_le_B common a ha)
  have hCC : C ≤ centralizer (V R a : Set (FreeAmalgam R)) :=
    inf_le_right.trans (centralizer_le hVGe)
  have hsplit : Z R p.e = U R p.e ⊔ C :=
    (show BinaryNaturalStructure source from
      ⟨common.X_eq_Z, common.natural, common.decomposition, common.disjoint⟩).decomposition_at p.e p.he
  have hnot : ¬ U R p.e ≤ B R a (geometry.Z_normal a) := by
    intro hU
    apply paired_midpoint_not_le_B common hb a b d ha p
    rw [hsplit]
    exact sup_le hU hCB
  let : Finite (U R p.e) := Nat.finite_of_card_ne_zero (by
    rw [common.natural.card_at p.e p.he]; decide)
  have heq := four_subgroup_eq_of_proper (U R p.e) D (B R a (geometry.Z_normal a))
    (common.natural.card_at p.e p.he) hcard hDU hDB hnot
  have hCU : C ≤ normalizer (U R p.e : Set (FreeAmalgam R)) :=
    (inf_le_left.trans (Z_le_stabilizer R p.e)).trans (U_normalized p.e)
  intro x hx
  have hmul : x ∈ (U R p.e : Set (FreeAmalgam R)) * (C : Set (FreeAmalgam R)) := by
    rw [← coe_mul_of_right_le_normalizer_left (U R p.e) C hCU, ← hsplit]
    exact hx.1
  obtain ⟨u,hu,c,hc,rfl⟩ := hmul
  have huB : u ∈ B R a (geometry.Z_normal a) := by
    simpa only [mul_inv_cancel_right] using
      (B R a (geometry.Z_normal a)).mul_mem hx.2 ((B R a (geometry.Z_normal a)).inv_mem (hCB hc))
  exact (centralizer (V R a : Set (FreeAmalgam R))).mul_mem
    (hDC (heq ▸ (show u ∈ U R p.e ⊓ B R a (geometry.Z_normal a) from ⟨hu,huB⟩))) (hCC hc)

include common in
/-- The actual radius displacement is a nonzero central line or plane in the two layers. -/
theorem paired_radius_displacement_structure
    (initial : InitialFacts R geometry)
    (a b d : Vertex R) (ha : color R a = false)
    (p : SpanOffender.PairedSpans geometry a b d ha) :
    let D := ⁅U R p.e,V R a⁆
    (Nat.card D = 2 ∨ Nat.card D = 4) ∧
      D ≤ Z R a ⊓ U R p.e ∧
      D ≤ centralizer (V R a : Set (FreeAmalgam R)) := by
  let D := ⁅U R p.e,V R a⁆
  have hZeV : Z R p.e ≤ V R a := le_iSup_of_le p.e (le_iSup_of_le
    (by rw [SimpleGraph.dist_comm]; exact p.near.le) le_rfl)
  have hVGe : V R a ≤ stabilizer R p.e := (radius_le_Q common a ha).trans
    (Q_le_stabilizer_of_dist_two R a p.e ha p.near)
  have hDcent : D ≤ (center (V R a)).map (V R a).subtype :=
    (commutator_mono ((U_le_Z p.e).trans hZeV) (radius_le_Q common a ha)).trans
      (initial.commutator_central a ha)
  have hDC : D ≤ centralizer (V R a : Set (FreeAmalgam R)) := by
    rintro x hx v hv
    obtain ⟨z,hz,rfl⟩ := hDcent hx
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨v,hv⟩)
  have hDU : D ≤ U R p.e := le_normalizer_iff_commutator_le_left.mp
    (hVGe.trans (U_normalized p.e))
  have hDZ : D ≤ Z R a :=
    (commutator_mono ((U_le_Z p.e).trans hZeV) le_rfl).trans
      (derived_le_Z_of_commutator_central common a ha (initial.commutator_central a ha))
  have hnon : D ≠ ⊥ := by
    intro hz
    have hVc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)
    have hVQ : V R a ≤ Q R p.e := by
      rw [← common.natural.centralizer p.e p.he]
      exact le_inf hVGe hVc
    apply p.escape_left
    apply (neighborSpan_le_radius a d ?_).trans hVQ
    have hh := p.far
    rw [← p.transport_seed, ← p.transport_vertex, dist_act, SimpleGraph.dist_comm] at hh
    exact hh.le
  let : Finite (U R p.e) := Nat.finite_of_card_ne_zero (by
    rw [common.natural.card_at p.e p.he]; decide)
  let : Finite D := Finite.of_injective (inclusion hDU) (inclusion_injective _)
  have hge := (one_lt_card_iff_ne_bot D).mpr hnon
  have hdiv : Nat.card D ∣ 8 := common.natural.card_at p.e p.he ▸ card_dvd_of_le hDU
  have hne : Nat.card D ≠ 8 := by
    intro hc
    have heq : D = U R p.e := eq_of_le_of_card_ge hDU (by
      rw [common.natural.card_at p.e p.he, hc])
    apply hnon
    exact commutator_eq_bot_iff_le_centralizer.mpr (heq ▸ hDC)
  have hh := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1,2,4,8} : Finset ℕ) by decide] at hh
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  have hcards : Nat.card D = 2 ∨ Nat.card D = 4 := by omega
  exact ⟨hcards, le_inf hDZ hDU, hDC⟩

include common in
/-- In the remaining line case, the radius displacement is the original central displacement. -/
theorem paired_radius_line_eq_original_displacement
    (a b d : Vertex R) (ha : color R a = false)
    (p : SpanOffender.PairedSpans geometry a b d ha)
    (hcard : Nat.card (⁅U R p.e,V R a⁆ : Subgroup (FreeAmalgam R)) = 2) :
    ⁅U R p.e,V R a⁆ = ⁅Z R d,Q R a⁆ := by
  let D := ⁅U R p.e,V R a⁆
  let W := neighborSpan a d
  have hWV : W ≤ V R a := by
    apply neighborSpan_le_radius a d
    have hh := p.far
    rw [← p.transport_seed, ← p.transport_vertex, dist_act, SimpleGraph.dist_comm] at hh
    exact hh.le
  have hZeV : Z R p.e ≤ V R a := le_iSup_of_le p.e (le_iSup_of_le
    (by rw [SimpleGraph.dist_comm]; exact p.near.le) le_rfl)
  have hWGe : W ≤ stabilizer R p.e := (hWV.trans (radius_le_Q common a ha)).trans
    (Q_le_stabilizer_of_dist_two R a p.e ha p.near)
  have hAD : ⁅U R p.e,W⁆ ≤ D := commutator_mono le_rfl hWV
  have hnon : ⁅U R p.e,W⁆ ≠ ⊥ := by
    intro hz
    apply p.escape_left
    rw [← common.natural.centralizer p.e p.he]
    exact le_inf hWGe (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz))
  let : Finite D := Nat.finite_of_card_ne_zero (by change Nat.card D = 2 at hcard; omega)
  let : Finite (⁅U R p.e,W⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hAD) (inclusion_injective _)
  have heq : ⁅U R p.e,W⁆ = D := by
    apply eq_of_le_of_card_ge hAD
    have hh := (one_lt_card_iff_ne_bot _).mpr hnon
    change Nat.card D = 2 at hcard
    omega
  have hDold : D ≤ ⁅Z R d,Q R a⁆ := by
    rw [← heq, ← p.displacement_left, commutator_comm]
    exact commutator_mono le_rfl ((U_le_Z p.e).trans (hZeV.trans (radius_le_Q common a ha)))
  let : Finite (⁅Z R d,Q R a⁆ : Subgroup (FreeAmalgam R)) :=
    Nat.finite_of_card_ne_zero (by rw [p.card_left]; decide)
  exact eq_of_le_of_card_ge hDold (by change Nat.card D = 2 at hcard; rw [p.card_left, hcard])
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanSymmetry
