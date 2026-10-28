module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Center.Transfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Center.FailureOffender.Index
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.Geometry
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# Escaping-generator intersection bounds under radius-center failure

Assume the critical distance is four and the center of V_a is not contained
in B_a. An escaping layer Z_d at distance two from c forms a critical pair
with a. Put C = Z(V_a). The already proved containment C ≤ Q_c puts
[C,Z_d] inside [Q_c,Z_d].

The subgroup [C,Z_d] cannot lie in Z_a: the relative normal subgroup of G_a
centralizing C modulo Z_a would contain Z_d, hence the local two-residual,
which would put C in B_a. It also contains the nontrivial critical
commutator [Z_a,Z_d] inside Z_a. The actual natural module bounds
[Q_c,Z_d] by order four, so these two facts force [C,Z_d] = [Q_c,Z_d].
Since Z_d normalizes C, this proves [V_a ∩ Q_c,Z_d] ≤ C.

Conjugation transports center failure to c and gives the reciprocal bound.
The escaping condition on Z_d is retained throughout. The argument does not
assume that Q acts trivially on V/Z(V), or use later center or FF conclusions.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), first paragraph of (4.6.1), printed p.900; the order-four calculation
is the binary specialization of the natural-module displacement there.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem eq_of_small_overgroup {G : Type*} [Group G]
    (J K H D : Subgroup G) [Finite H]
    (hJK : J ≤ K) (hKH : K ≤ H) (hJD : J ≤ D)
    (hJ : J ≠ ⊥) (hK : ¬ K ≤ D) (hH : Nat.card H ≤ 4) : K = H := by
  let : Finite K := Finite.of_injective (inclusion hKH) (inclusion_injective _)
  let : Finite J := Finite.of_injective (inclusion hJK) (inclusion_injective _)
  have hJcard := J.one_lt_card_iff_ne_bot.mpr hJ
  have hJKcard : Nat.card J < Nat.card K := by
    by_contra! h
    exact hK ((eq_of_le_of_card_ge hJK h).symm.le.trans hJD)
  by_contra hne
  have hKHcard : Nat.card K < Nat.card H := by
    by_contra! h
    exact hne (eq_of_le_of_card_ge hKH h)
  have hKcard : Nat.card K = 3 := by omega
  have hHcard : Nat.card H = 4 := by omega
  have hdiv := card_dvd_of_le hKH
  rw [hKcard, hHcard] at hdiv
  norm_num at hdiv

private theorem center_commutator_not_le_Z
    (common : CommonFacts R source geometry)
    (a d : Vertex R) (ha : color R a = false)
    (hfail : ¬ (center (V R a)).map (V R a).subtype ≤ B R a (geometry.Z_normal a))
    (hda : Z R d ≤ stabilizer R a) (hout : ¬ Z R d ≤ Q R a) :
    ¬ ⁅(center (V R a)).map (V R a).subtype, Z R d⁆ ≤ Z R a := by
  intro hcomm
  let C := (center (V R a)).map (V R a).subtype
  let P := commutatorPreimage (stabilizer R a) C (Z R a)
  have hP : P ≤ stabilizer R a := commutatorPreimage_le _ _ _
  have hn : (P.subgroupOf (stabilizer R a)).Normal :=
    normal_subgroupOf_of_le_normalizer
      (commutatorPreimage_normalized _ _ _ _ (Z_normalized R a)
        (stabilizer R a).le_normalizer (radius_center_normalized a) (Z_normalized R a))
  have hdP : Z R d ≤ P := le_commutatorPreimage hda (by
    rw [commutator_comm]; exact hcomm)
  have hLP : Ltilde R a ≤ P :=
    NaturalStructure.Exclusion.residual_le_of_normal_not_le source a ha P hP hn
      (fun h => hout (hdP.trans h))
  have hLC : ⁅Ltilde R a, C⁆ ≤ Z R a :=
    (commutator_mono hLP le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ (Z_normalized R a))
  apply hfail
  intro x hx
  apply (mem_B_iff R a (geometry.Z_normal a)
    ((radius_le_Q common a ha).trans (fun _ hv => hv.1)) x).mpr
  exact ⟨map_subtype_le _ hx, fun l hl =>
    hLC (commutator_mem_commutator hl hx)⟩

private theorem center_failure_at
    (common : CommonFacts R source geometry)
    (a c : Vertex R) (ha : color R a = false) (hc : color R c = false)
    (hfail : ¬ (center (V R a)).map (V R a).subtype ≤ B R a (geometry.Z_normal a)) :
    ¬ (center (V R c)).map (V R c).subtype ≤ B R c (geometry.Z_normal c) := by
  obtain ⟨u, hu⟩ := exists_mVertex_of_color R ha
  obtain ⟨v, hv⟩ := exists_mVertex_of_color R hc
  let g := u⁻¹ * v
  have hg : act R g a = c := by
    rw [hu, act_mVertex]
    simpa only [g, mul_inv_cancel_left] using hv.symm
  intro h
  have h' : (center (V R (act R g a))).map (V R (act R g a)).subtype ≤
      B R (act R g a) (geometry.Z_normal _) := by rw [hg]; exact h
  rw [Escape.PairingControl.FirstPairing.B_act common.large_distance g a ha,
    V_act, ← map_embeddedCenter _ _ (MulAut.conj g⁻¹).injective] at h'
  exact hfail ((map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp h')

/-- The source intersection bound for each escaping generator. The critical
pair needed in the proof follows from escape and the two radius distances. -/
theorem radiusCenterIntersectionBound_of_center_failure
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a c : Vertex R) (ha : color R a = false)
    (hac : (cosetGraph R).dist a c = 2)
    (hfail : ¬ (center (V R a)).map (V R a).subtype ≤ B R a (geometry.Z_normal a)) :
    RadiusCenterIntersectionBound a c := by
  intro d hd hdc hout
  have hc : color R c = false :=
    (color_eq_of_dist_even R a c (by rw [hac]; decide)).symm.trans ha
  have hda : (cosetGraph R).dist d a = 4 := by
    have hlo := criticalDistance_le R d (geometry.exists_critical d hd) hout
    rw [geometry.distance_constant d hd] at hlo
    change geometry.b R ≤ _ at hlo
    have hhi := (cosetGraph_connected R).dist_triangle (u := d) (v := c) (w := a)
    rw [hdc, SimpleGraph.dist_comm (u := c), hac] at hhi
    omega
  have hcrit : CriticalPair R d a (geometry.exists_critical d hd) := by
    refine ⟨?_, hout⟩
    rw [hda, geometry.distance_constant d hd]
    exact hb.symm
  have hnon : ⁅Z R a, Z R d⁆ ≠ ⊥ := by
    rw [commutator_comm]
    exact common.critical_noncommutation d hd a hcrit
  have hdS : Z R d ≤ stabilizer R a :=
    geometry.Z_le_stabilizer_of_dist_le_b d hd a (by rw [hda, hb])
  let C := (center (V R a)).map (V R a).subtype
  let K := ⁅C, Z R d⁆
  let H := ⁅Q R c, Z R d⁆
  have hCQ : C ≤ Q R c := radius_center_le_Q_of_dist_two common a c ha hac
  have hKH : K ≤ H := commutator_mono hCQ le_rfl
  have hKC : K ≤ C :=
    le_normalizer_iff_commutator_le_left.mp (hdS.trans (radius_center_normalized a))
  have hJK : ⁅Z R a, Z R d⁆ ≤ K :=
    commutator_mono (Z_le_radius_center common a ha) le_rfl
  have hJZ : ⁅Z R a, Z R d⁆ ≤ Z R a :=
    le_normalizer_iff_commutator_le_left.mp (hdS.trans (Z_normalized R a))
  have hKZ : ¬ K ≤ Z R a := center_commutator_not_le_Z common a d ha hfail hdS hout
  obtain ⟨t, hct, hdt⟩ := exists_common_neighbor_of_dist_two R c d (by
    rw [SimpleGraph.dist_comm, hdc])
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hct
    cases h : color R t <;> simp_all
  have hHt : H ≤ ⁅Z R d, Q R t⁆ := by
    dsimp only [H]
    rw [commutator_comm]
    exact commutator_mono le_rfl (Q_le_adjacent_h R ht hct)
  have htU := Escape.EdgeTransfer.edge_commutator_le_natural
    common.large_distance (moduleFacts common) d t hd hdt
  let : Finite (U R d) := Nat.finite_of_card_ne_zero (by
    rw [common.natural.card_at d hd]; decide)
  let : Finite (⁅Z R d, Q R t⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion htU) (inclusion_injective _)
  let : Finite H := Finite.of_injective (inclusion hHt) (inclusion_injective _)
  have hHcard : Nat.card H ≤ 4 := (card_le_of_le hHt).trans
    (Escape.EdgeTransfer.edge_displacement_card_le_four
      common.large_distance (moduleFacts common) d t hd hdt)
  have heq : K = H := eq_of_small_overgroup ⁅Z R a, Z R d⁆ K H (Z R a)
    hJK hKH hJZ hnon hKZ hHcard
  exact (commutator_mono inf_le_right le_rfl).trans (heq.symm.le.trans hKC)

/-- Both bounds required by the parent offender construction on a critical
midpoint. The one-direction argument works at every vertex at distance two,
while the chosen critical endpoint supplies the midpoint's color here. -/
theorem radiusCenterIntersectionBounds_of_center_failure
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a : Vertex R) (ha : color R a = false)
    (hfail : ¬ (center (V R a)).map (V R a).subtype ≤ B R a (geometry.Z_normal a))
    (a' c : Vertex R)
    (hcrit : CriticalPair R a a' (geometry.exists_critical a ha))
    (hac : (cosetGraph R).dist a c = 2) (hca' : (cosetGraph R).dist c a' = 2) :
    RadiusCenterIntersectionBound a c ∧ RadiusCenterIntersectionBound c a := by
  have ha' := critical_endpoint_color R a ha (geometry.exists_critical a ha) hcrit
  have hc : color R c = false :=
    (color_eq_of_dist_even R c a' (by rw [hca']; decide)).trans ha'
  exact ⟨radiusCenterIntersectionBound_of_center_failure common hb a c ha hac hfail,
    radiusCenterIntersectionBound_of_center_failure common hb c a hc
      (by rw [SimpleGraph.dist_comm, hac]) (center_failure_at common a c ha hc hfail)⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
