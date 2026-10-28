module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Center.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.Geometry
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# Center failure and the opposite kernel displacement

Center failure makes its commutator with an escaping Z-layer larger than
its nontrivial intersection with the central Z-layer. The natural-module
order-four bound then identifies this commutator with the entire opposite
kernel displacement. In particular that displacement lies in the radius
center. Conjugation transports center failure between M-vertices.

This strengthens the intersection conclusion to the kernel displacement
actually established by its proof, as needed by simultaneous escape.
Adapted from the checked calculation in Center/FailureOffender/Intersection,
retaining its original proof and avoiding a dependency on offender assembly.
Source: Meierfrankenfeld--Stellmacher (1993), (4.6.1), pp.900--901.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial.DerivedFixed
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

theorem center_failure_at
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

/-- Center failure controls the whole opposite kernel displacement for an
escaping generator, not just its restriction to the radius intersection. -/
theorem center_failure_displacement
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a c : Vertex R) (ha : color R a = false)
    (hac : (cosetGraph R).dist a c = 2)
    (hfail : ¬ (center (V R a)).map (V R a).subtype ≤ B R a (geometry.Z_normal a))
    (d : Vertex R) (hd : color R d = false) (hdc : (cosetGraph R).dist d c = 2)
    (hout : ¬ Z R d ≤ Q R a) :
    ⁅Q R c, Z R d⁆ ≤ (center (V R a)).map (V R a).subtype := by
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
  exact heq.symm.le.trans hKC

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial.DerivedFixed
