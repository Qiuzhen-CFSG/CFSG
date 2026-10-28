module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.RadiusIndex
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.RadiusIntersection.SpanSymmetry
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# From the radius action to the literal Z-intersection index

The eight-element natural subgroup at the opposite midpoint has a fixed
plane when the B-intersection has index at most two and centralizes the
radius. The radius image has order greater than two. Evaluation on the
one-dimensional quotient therefore identifies its displacement with the
whole fixed plane. The three-subgroups lemma makes that plane central in
the initial kernel. Removing the local fixed summand then puts the entire
B-intersection in the initial omega-center Z.

The actual conjugation retained by PairedSpans identifies the two Z-layer
orders. This converts the resulting index bound into the literal index
[Z_alpha : Z_alpha intersection Z_e] = 2; criticality excludes index one.
Finiteness is only used for local subgroups, not for the free amalgam.

The final witness theorem supplies the span-symmetry bound and
fixed-intersection centralization from the escaping neighbor, discharging
both premises of the index calculation for the same transported pair.
The terminal contradiction and final source (4.6.4) assembly belong to the
Containment consumer.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.4), second paragraph, printed p.902.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.RadiusIntersection

private theorem fixed_plane_centralizes {G : Type*} [Group G]
    (U A T : Subgroup G) [Finite U] [IsMulCommutative U]
    (hU : Nat.card U = 8) (hAU : A ≤ normalizer (U : Set G))
    (hTU : T ≤ normalizer (U : Set G)) (hTA : T ≤ normalizer (A : Set G))
    (hAT : ⁅A,T⁆ ≤ centralizer (U : Set G))
    (hi : (U ⊓ centralizer (A : Set G)).relIndex U = 2)
    (hlarge : 2 < (centralizer (U : Set G)).relIndex A) :
    U ⊓ centralizer (A : Set G) ≤ centralizer (T : Set G) := by
  let F := U ⊓ centralizer (A : Set G)
  have hAF : A ≤ normalizer F :=
    (le_centralizer_iff.mp (show F ≤ centralizer (A : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hDF : ⁅U,A⁆ ≤ F :=
    commutator_le_of_normalized_index_two U F A inf_le_left hi hAU hAF
  have hcard : Nat.card F = 4 := by
    have hh := (F.subgroupOf U).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show F ≤ U from inf_le_left)).toEquiv,
      show (F.subgroupOf U).index = 2 from hi, hU] at hh
    omega
  have hDcard := actor_index_eq_displacement_card_of_fixed_index_two U A hAU
    (hDF.trans inf_le_right) hi
  have hdiv : Nat.card (⁅U,A⁆ : Subgroup G) ∣ 4 := hcard ▸ card_dvd_of_le hDF
  have hbound : Nat.card (⁅U,A⁆ : Subgroup G) = 4 := by
    have hh := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 4 ≠ 0)⟩
    rw [show Nat.divisors 4 = ({1,2,4} : Finset ℕ) by decide] at hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    omega
  let : Finite F := Finite.of_injective (inclusion (show F ≤ U from inf_le_left))
    (inclusion_injective _)
  have heq : ⁅U,A⁆ = F := eq_of_le_of_card_ge hDF (by omega)
  have hTF : T ≤ normalizer F :=
    (le_inf hTU (hTA.trans (normalizer_le_normalizer_centralizer A))).trans
      inf_normalizer_le_normalizer_inf
  have hUTF : ⁅U,T⁆ ≤ F :=
    commutator_le_of_normalized_index_two U F T inf_le_left hi hTU hTF
  have hzero₁ : ⁅⁅A,T⁆,U⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hAT
  have hzero₂ : ⁅⁅T,U⁆,A⁆ = ⊥ := by
    rw [commutator_comm T U]
    exact commutator_eq_bot_iff_le_centralizer.mpr (hUTF.trans inf_le_right)
  have hzero := commutator_commutator_eq_bot_of_rotate hzero₁ hzero₂
  rw [heq] at hzero
  exact commutator_eq_bot_iff_le_centralizer.mp hzero

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry)

include common in
/-- Once the source span bounds hold, the fixed part of the opposite
Z-layer centralizes the initial kernel. The proof uses the actual natural
group and the strict radius-image inequality, with no edge-containment
or later radius-center equality assumption. -/
theorem paired_fixed_centralizes_kernel
    (initial : InitialFacts R geometry) (hb : geometry.b R = 4)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d,Q R b⁆ ≤ B R a (geometry.Z_normal a))
    (p : SpanOffender.PairedSpans geometry a b d ha)
    (hsmall : (B R a (geometry.Z_normal a)).relIndex (Z R p.e) ≤ 2)
    (hfixed : Z R p.e ⊓ B R a (geometry.Z_normal a) ≤
      centralizer (V R a : Set (FreeAmalgam R))) :
    Z R p.e ⊓ centralizer (V R a : Set (FreeAmalgam R)) ≤
      centralizer (Q R a : Set (FreeAmalgam R)) := by
  let Ue := U R p.e
  let A := V R a
  let T := Q R a
  let F := Ue ⊓ centralizer (A : Set (FreeAmalgam R))
  have hcolb : color R b = true := by
    have hh := adjacent_color_ne R hab
    cases hc : color R b <;> simp_all
  have hTGe : T ≤ stabilizer R p.e :=
    (Q_le_adjacent_h R hcolb hab).trans (fun _ hx => hx.2 p.e (adjacent_symm R p.edge))
  have hAT : A ≤ T := radius_le_Q common a ha
  have hAGe := hAT.trans hTGe
  have hZeA : Z R p.e ≤ A := le_iSup_of_le p.e (le_iSup_of_le
    (by rw [SimpleGraph.dist_comm]; exact p.near.le) le_rfl)
  have hlarge := two_lt_paired_radius_image common initial hb a b d ha hab hdb hbad p
  have hkernel : (Q R p.e).subgroupOf A =
      (centralizer (Ue : Set (FreeAmalgam R))).subgroupOf A := by
    ext x
    change (x : FreeAmalgam R) ∈ Q R p.e ↔
      (x : FreeAmalgam R) ∈ centralizer (Ue : Set (FreeAmalgam R))
    rw [← common.natural.centralizer p.e p.he, mem_inf]
    exact and_iff_right (hAGe x.property)
  have hlarge' : 2 < (centralizer (Ue : Set (FreeAmalgam R))).relIndex A := by
    change 2 < ((Q R p.e).subgroupOf A).index at hlarge
    rwa [hkernel] at hlarge
  let : Finite (Z R p.e) := by
    let := finite_stabilizer R p.e
    exact Finite.of_injective (inclusion (Z_le_stabilizer R p.e)) (inclusion_injective _)
  let : Finite Ue := Nat.finite_of_card_ne_zero (by
    change Nat.card (U R p.e) ≠ 0
    rw [common.natural.card_at p.e p.he]; decide)
  let := geometry.U_elementary (lt_trans (by decide : 0 < 2) common.large_distance) p.e p.he
  have hsmall' : (centralizer (A : Set (FreeAmalgam R))).relIndex (Z R p.e) ≤ 2 := by
    have hh := relIndex_le_of_le_left hfixed
      (show (Z R p.e ⊓ B R a (geometry.Z_normal a)).relIndex (Z R p.e) ≠ 0 from
        index_ne_zero_of_finite)
    rw [inf_relIndex_left] at hh
    exact hh.trans hsmall
  have hFsmall : F.relIndex Ue ≤ 2 := by
    rw [show F = Ue ⊓ centralizer (A : Set (FreeAmalgam R)) from rfl, inf_relIndex_left]
    exact (relIndex_le_of_le_right (U_le_Z p.e) index_ne_zero_of_finite).trans hsmall'
  have hFone : F.relIndex Ue ≠ 1 := by
    intro hi
    have hUA : Ue ≤ centralizer (A : Set (FreeAmalgam R)) :=
      (relIndex_eq_one.mp hi).trans inf_le_right
    have hh : (centralizer (Ue : Set (FreeAmalgam R))).relIndex A = 1 :=
      relIndex_eq_one.mpr (le_centralizer_iff.mp hUA)
    omega
  have hFi : F.relIndex Ue = 2 := by
    have hz : F.relIndex Ue ≠ 0 := index_ne_zero_of_finite
    omega
  have hATC : ⁅A,T⁆ ≤ centralizer (Ue : Set (FreeAmalgam R)) := by
    intro x hx u hu
    obtain ⟨v,hv,rfl⟩ := initial.commutator_central a ha hx
    exact congrArg Subtype.val ((mem_center_iff.mp hv) ⟨u,hZeA (U_le_Z p.e hu)⟩)
  have hFC : F ≤ centralizer (T : Set (FreeAmalgam R)) :=
    fixed_plane_centralizes Ue A T (common.natural.card_at p.e p.he)
      (hAGe.trans (U_normalized p.e)) (hTGe.trans (U_normalized p.e))
      ((show T ≤ stabilizer R a from fun _ hx => hx.1).trans (V_normalized a))
      hATC hFi hlarge'
  let C := Z R p.e ⊓ centralizer (stabilizer R p.e : Set (FreeAmalgam R))
  have hCA : C ≤ centralizer (A : Set (FreeAmalgam R)) :=
    inf_le_right.trans (centralizer_le hAGe)
  have hCT : C ≤ centralizer (T : Set (FreeAmalgam R)) :=
    inf_le_right.trans (centralizer_le hTGe)
  have hCU : C ≤ normalizer (Ue : Set (FreeAmalgam R)) :=
    ((inf_le_left.trans (Z_le_stabilizer R p.e))).trans (U_normalized p.e)
  have hsplit : Z R p.e = Ue ⊔ C :=
    (show BinaryNaturalStructure source from
      ⟨common.X_eq_Z, common.natural, common.decomposition, common.disjoint⟩).decomposition_at p.e p.he
  intro x hx
  have hmul : x ∈ (Ue : Set (FreeAmalgam R)) * (C : Set (FreeAmalgam R)) := by
    rw [← coe_mul_of_right_le_normalizer_left Ue C hCU, ← hsplit]
    exact hx.1
  obtain ⟨u,hu,c,hc,rfl⟩ := hmul
  have huC : u ∈ centralizer (A : Set (FreeAmalgam R)) := by
    simpa only [mul_inv_cancel_right] using
      (centralizer (A : Set (FreeAmalgam R))).mul_mem hx.2
        ((centralizer (A : Set (FreeAmalgam R))).inv_mem (hCA hc))
  exact (centralizer (T : Set (FreeAmalgam R))).mul_mem (hFC ⟨hu,huC⟩) (hCT hc)

include common in
/-- The last intersection calculation on p.902. The two preceding span
conclusions remain explicit: the B-intersection has index at most two and
centralizes the radius. They are not consequences assumed in PairedSpans. -/
theorem paired_index_of_span_bounds
    (initial : InitialFacts R geometry) (hb : geometry.b R = 4)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d,Q R b⁆ ≤ B R a (geometry.Z_normal a))
    (p : SpanOffender.PairedSpans geometry a b d ha)
    (hsmall : (B R a (geometry.Z_normal a)).relIndex (Z R p.e) ≤ 2)
    (hfixed : Z R p.e ⊓ B R a (geometry.Z_normal a) ≤
      centralizer (V R a : Set (FreeAmalgam R))) :
    (Z R p.e).relIndex (Z R a) = 2 := by
  have hcentral := paired_fixed_centralizes_kernel common initial hb a b d ha hab hdb hbad
    p hsmall hfixed
  let := geometry.Z_elementary (lt_trans (by decide : 0 < 2) common.large_distance) p.e p.he
  have hKZ : Z R p.e ⊓ B R a (geometry.Z_normal a) ≤ Z R a := by
    intro x hx
    rw [← common.X_eq_Z a ha]
    apply mem_omegaCenter_iff.mpr
    have hZeV : Z R p.e ≤ V R a := le_iSup_of_le p.e (le_iSup_of_le
      (by rw [SimpleGraph.dist_comm]; exact p.near.le) le_rfl)
    exact ⟨radius_le_Q common a ha (hZeV hx.1),
      elemPow_eq_one_of_isElementaryAbelian x hx.1, hcentral ⟨hx.1,hfixed hx⟩⟩
  let : Finite (Z R a) := by
    let := finite_stabilizer R a
    exact Finite.of_injective (inclusion (Z_le_stabilizer R a)) (inclusion_injective _)
  let : Finite (Z R p.e) := by
    let := finite_stabilizer R p.e
    exact Finite.of_injective (inclusion (Z_le_stabilizer R p.e)) (inclusion_injective _)
  have hcard : Nat.card (Z R p.e) = Nat.card (Z R a) := by
    rw [← p.transport_vertex, Z_act, card_map_of_injective (MulAut.conj p.f⁻¹).injective]
  have hsmall' : (Z R a).relIndex (Z R p.e) ≤ 2 := by
    have hh := relIndex_le_of_le_left hKZ
      (show (Z R p.e ⊓ B R a (geometry.Z_normal a)).relIndex (Z R p.e) ≠ 0 from
        index_ne_zero_of_finite)
    rw [inf_relIndex_left] at hh
    exact hh.trans hsmall
  have hnotone : (Z R a).relIndex (Z R p.e) ≠ 1 := by
    intro hi
    have heq : Z R p.e = Z R a := eq_of_le_of_card_ge (relIndex_eq_one.mp hi) hcard.ge
    apply p.critical.2
    rw [← heq]
    exact Z_le_Q_of_dist_lt R p.e (geometry.exists_critical p.e p.he) (by
      rw [p.far, geometry.distance_constant p.e p.he]
      exact common.large_distance)
  have hi : (Z R a).relIndex (Z R p.e) = 2 := by
    have hz : (Z R a).relIndex (Z R p.e) ≠ 0 := index_ne_zero_of_finite
    omega
  let I := Z R a ⊓ Z R p.e
  let : Finite I := Finite.of_injective (inclusion (show I ≤ Z R a from inf_le_left))
    (inclusion_injective _)
  have hleft := (I.subgroupOf (Z R a)).card_mul_index
  have hright := (I.subgroupOf (Z R p.e)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show I ≤ Z R a from inf_le_left)).toEquiv] at hleft
  rw [Nat.card_congr (subgroupOfEquivOfLe (show I ≤ Z R p.e from inf_le_right)).toEquiv] at hright
  change Nat.card I * I.relIndex (Z R a) = Nat.card (Z R a) at hleft
  change Nat.card I * I.relIndex (Z R p.e) = Nat.card (Z R p.e) at hright
  rw [show I.relIndex (Z R a) = (Z R p.e).relIndex (Z R a) by
    exact inf_relIndex_left _ _] at hleft
  rw [show I.relIndex (Z R p.e) = (Z R a).relIndex (Z R p.e) by
    exact inf_relIndex_right _ _, hi, hcard] at hright
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hleft.trans hright.symm)

include common in
/-- An escaping neighbor supplies an actual paired critical path with the
literal intersection index [Z_a : Z_a intersect Z_e] equal to two.
Both span premises are proved from the early source hypotheses, and the
chosen pair retains its conjugating element and critical-path geometry. -/
theorem paired_index_witness
    (initial : InitialFacts R geometry) (hb : geometry.b R = 4)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d,Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    ∃ p : SpanOffender.PairedSpans geometry a b d ha,
      (Z R p.e).relIndex (Z R a) = 2 := by
  obtain ⟨p, hsmall, hfixed⟩ :=
    SpanSymmetry.paired_span_bounds common initial hb a b d ha hab hdb hbad
  exact ⟨p, paired_index_of_span_bounds common initial hb a b d ha hab hdb hbad
    p hsmall hfixed⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.RadiusIntersection
