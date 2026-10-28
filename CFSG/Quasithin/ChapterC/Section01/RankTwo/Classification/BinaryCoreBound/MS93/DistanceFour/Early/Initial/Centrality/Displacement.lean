module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Centrality.Offender
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.SplitAndCentral.Split.Endpoints
public import Theory.Representation.PSL3Two.FourGroupGeometry.Normalizers.FourGroupCoverage
public import Theory.Representation.PSL3Two.FourGroupGeometry.Normalizers.PointModel

/-!
# The first displacement calculation in MS93 (4.6.3)

At a noncentral radius-generator pair, the middle kernel normalizes the
opposite critical image in the actual marked SL₃(2) quotient. An image of
order at most two would be centralized and make the mixed triple trivial.
The elementary rank bound therefore forces order four.

The image of V_delta intersect Q_alpha centralizes this four-group, whose
centralizer in SL₃(2) is itself. Lifting through the exact kernel Q_lambda
puts its commutator with Z_lambda inside [Z_delta,Z_lambda], hence Z_delta.
Thus that intersection fixes the literal quotient V_delta/Z_delta. The
radius image at alpha is elementary: its projection factors through the
already proved elementary quotient V_delta/Z_delta, with containment of
Z_delta in Q_alpha proved from distance two. Its order is at most four.
Critical index reciprocity gives the required displacement comparison and
discharges the last premise of the existing offender application.

All projections retain their actual kernels; all finiteness is local to
vertex stabilizers. No InitialFacts or later centrality result is assumed.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), first paragraph of (4.6.3), printed pp.901--902.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
open ModuleAlternatives.SourceCalculation ModuleAlternatives.SourceCalculation.Split
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem small_normalizer {G : Type*} [Group G]
    (D : Subgroup G) [Finite D] (hD : Nat.card D ≤ 2) :
    normalizer (D : Set G) ≤ centralizer (D : Set G) := by
  by_cases hsmall : Nat.card D ≤ 1
  · rw [eq_bot_of_card_le D hsmall]
    intro g _ x hx
    have hxone : x = 1 := hx
    simp [hxone]
  · have htwo : Nat.card D = 2 := by omega
    obtain ⟨z, _, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : D)).mp htwo
    intro g hg x hx
    by_cases hxone : x = 1
    · simp [hxone]
    let xD : D := ⟨x, hx⟩
    let yD : D := ⟨g * x * g⁻¹, (hg x).mp hx⟩
    have hyne : yD ≠ 1 := by
      intro hy
      apply hxone
      have hy' : g * x * g⁻¹ = 1 := congrArg Subtype.val hy
      have hh := congrArg (fun a : G => g⁻¹ * a * g) hy'
      simpa [mul_assoc] using hh
    have heq : yD = xD := (hzuniq yD hyne).trans (hzuniq xD (by
      intro hx'; exact hxone (congrArg Subtype.val hx'))).symm
    have heq' : g * x * g⁻¹ = x := congrArg Subtype.val heq
    have hh := congrArg (fun a : G => a * g) heq'
    simpa [mul_assoc] using hh.symm

omit [Finite M] in
private theorem image_normalizes {c : Vertex R} (frame : Frame R c)
    (A P : Subgroup (FreeAmalgam R)) (hA : A ≤ stabilizer R c)
    (hn : P ≤ normalizer (A : Set (FreeAmalgam R))) :
    endpointImage source frame P ≤ normalizer (endpointImage source frame A : Set SL) := by
  apply le_trans (map_mono (show P.subgroupOf (stabilizer R c) ≤
      normalizer (A.subgroupOf (stabilizer R c) : Set (stabilizer R c)) from ?_))
    ((A.subgroupOf (stabilizer R c)).le_normalizer_map (frame.projection source))
  intro x hx
  rw [← subgroupOf_normalizer_eq hA]
  exact hn hx

private theorem commutator_le_kernel_of_images {c : Vertex R} (frame : Frame R c)
    (A P : Subgroup (FreeAmalgam R)) (hA : A ≤ stabilizer R c)
    (hP : P ≤ stabilizer R c)
    (hc : endpointImage source frame P ≤ centralizer (endpointImage source frame A : Set SL)) :
    ⁅A,P⁆ ≤ Q R c := by
  apply commutator_le.mpr
  intro x hx y hy
  let xS : stabilizer R c := ⟨x,hA hx⟩
  let yS : stabilizer R c := ⟨y,hP hy⟩
  have hc' := hc (mem_map_of_mem (frame.projection source)
      (show yS ∈ P.subgroupOf (stabilizer R c) from hy))
    (frame.projection source xS) (mem_map_of_mem (frame.projection source)
      (show xS ∈ A.subgroupOf (stabilizer R c) from hx))
  have hcomm : frame.projection source ⁅xS,yS⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc'
  have hm : ⁅xS,yS⁆ ∈ (frame.projection source).ker := hcomm
  rw [frame.projection_kernel source] at hm
  exact hm

private theorem fourGroup_centralizer (E : Subgroup SL) [IsElementaryAbelian 2 E]
    (hcard : Nat.card E = 4) : centralizer (E : Set SL) ≤ E := by
  open BinaryLinearThree.FourGroupGeometry.Normalizers in
  obtain ⟨f, hf⟩ := fourGroup_map_point E hcard
  intro x hx
  have hpoint : f x ∈ centralizer (Matrix.PSL3Two.MarkedAutomorphisms.pointV : Set SL) := by
    rw [← hf]
    rintro _ ⟨y, hy, rfl⟩
    change f y * f x = f x * f y
    rw [← map_mul, ← map_mul, hx y hy]
  have hi : MulAut.conj (f x) ∈
      BinaryLinearThree.FourGroupGeometry.Normalizers.innerPoint := by
    rw [← BinaryLinearThree.FourGroupGeometry.Normalizers.point_centralizer]
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hpoint y hy]
  have hm : f x ∈ Matrix.PSL3Two.MarkedAutomorphisms.pointV :=
    (mem_map_iff_mem Matrix.PSL3Two.MarkedAutomorphisms.conj_injective).mp hi
  rw [← hf] at hm
  exact (mem_map_iff_mem f.injective).mp hm

private theorem le_sup_kernel_of_image_le {c : Vertex R} (frame : Frame R c)
    (A P : Subgroup (FreeAmalgam R)) (hP : P ≤ stabilizer R c)
    (himage : endpointImage source frame P ≤ endpointImage source frame A) :
    P ≤ Q R c ⊔ A := by
  intro x hx
  obtain ⟨y, hy, he⟩ := himage (mem_map_of_mem (frame.projection source)
    (show (⟨x,hP hx⟩ : stabilizer R c) ∈ P.subgroupOf _ from hx))
  have hk : (⟨x,hP hx⟩ : stabilizer R c) * y⁻¹ ∈ (frame.projection source).ker := by
    change frame.projection source (⟨x,hP hx⟩ * y⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  rw [frame.projection_kernel source] at hk
  have hm := (Q R c ⊔ A).mul_mem
    ((show Q R c ≤ Q R c ⊔ A from le_sup_left) hk)
    ((show A ≤ Q R c ⊔ A from le_sup_right) hy)
  change (x * (y : FreeAmalgam R)⁻¹) * (y : FreeAmalgam R) ∈ Q R c ⊔ A at hm
  simpa only [inv_mul_cancel_right] using hm

private theorem elementary_card_le_four (E : Subgroup SL) [IsElementaryAbelian 2 E] :
    Nat.card E ≤ 4 := by
  by_cases hn : E = ⊥
  · simp [hn]
  have htwo : Representation.BinaryOffender.IsElementaryTwo E := ⟨hn, inferInstance⟩
  rw [htwo.card_eq_two_pow_rank]
  exact Nat.pow_le_pow_right (by decide : 0 < 2)
    (AbelianCore.QuotientRecognition.ExtensionControl.elementary_rank_le_two _ inferInstance)

private theorem radius_image_elementary
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (d a : Vertex R) (hd : color R d = false) (frame : Frame R a)
    (hVS : V R d ≤ stabilizer R a) (hZQ : Z R d ≤ Q R a) :
    IsElementaryAbelian 2 (endpointImage source frame (V R d)) := by
  let := radiusZ_normal common d hd
  let := radiusQuotient_elementary common hb d hd
  let N := (Z R d).subgroupOf (V R d)
  let f : V R d →* endpointImage source frame (V R d) :=
    ((frame.projection source).comp (inclusion hVS)).codRestrict _ (fun v =>
      mem_map_of_mem (frame.projection source)
        (show (inclusion hVS v) ∈ (V R d).subgroupOf (stabilizer R a) from v.property))
  have hsurj : Function.Surjective f := by
    rintro ⟨x, y, hy, rfl⟩
    exact ⟨⟨y,hy⟩, rfl⟩
  have hker : N ≤ f.ker := by
    intro x hx
    apply Subtype.ext
    change frame.projection source (inclusion hVS x) = 1
    change inclusion hVS x ∈ (frame.projection source).ker
    rw [frame.projection_kernel source]
    exact hZQ hx
  exact IsElementaryAbelian.of_surjective (QuotientGroup.lift N f hker)
    (QuotientGroup.lift_surjective_of_surjective N f hsurj hker)

namespace NoncentralPair
variable {a d e : Vertex R}

/-- Noncentrality of the mixed triple forces the actual critical image to have order four. -/
theorem actor_index (h : NoncentralPair R a d e)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4) :
    (Q R e).relIndex (Z R d) = 4 := by
  obtain ⟨frame⟩ := exists_frame e h.color_e
  have hdS := (source.critical_Z_le_stabilizer geometry d h.color_d e
    (h.critical_pair common hb)).1
  have haS : Q R a ≤ stabilizer R e :=
    Q_le_stabilizer_of_dist_le_two a e h.color_a h.color_e (by
      rw [SimpleGraph.dist_comm, h.dist_ea])
  have hn : Q R a ≤ normalizer (Z R d : Set (FreeAmalgam R)) :=
    (Q_le_stabilizer_of_dist_le_two a d h.color_a h.color_d (by
      rw [SimpleGraph.dist_comm, h.dist_da])).trans (Z_normalized R d)
  let := geometry.Z_elementary (by omega) d h.color_d
  have hupp := endpointImage_card_le_four source frame (Z R d) hdS
  have hnot : ¬ Nat.card (endpointImage source frame (Z R d)) ≤ 2 := by
    intro hc
    have hcentral := (image_normalizes frame (Z R d) (Q R a) hdS hn).trans
      (small_normalizer _ hc)
    have hcomm := commutator_le_kernel_of_images frame (Z R d) (Q R a) hdS haS hcentral
    apply h.triple_ne_bot
    apply le_bot_iff.mp
    exact (commutator_mono hcomm le_rfl).trans (by
      rw [commutator_comm, geometry.centralizes e h.color_e])
  let := endpointImage_elementary source frame (Z R d) hdS
  obtain ⟨n, hncard⟩ := (IsElementaryAbelian.isPGroup 2
    (endpointImage source frame (Z R d))).exists_card_eq
  have heq : Nat.card (endpointImage source frame (Z R d)) = 4 := by
    have hnle : n ≤ 2 := by
      by_contra! hn
      have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hn
      omega
    interval_cases n <;> norm_num only [pow_zero, pow_one, Nat.reducePow] at hncard <;> omega
  rwa [endpointImage_card source frame (Z R d) hdS] at heq

/-- The full intersection displacement lies in the critical pair commutator. -/
theorem intersection_commutator (h : NoncentralPair R a d e)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4) :
    ⁅V R d ⊓ Q R a,Z R e⁆ ≤ ⁅Z R d,Z R e⁆ := by
  obtain ⟨frame⟩ := exists_frame e h.color_e
  obtain ⟨hdS,heS⟩ := source.critical_Z_le_stabilizer geometry d h.color_d e
    (h.critical_pair common hb)
  have haS : Q R a ≤ stabilizer R e :=
    Q_le_stabilizer_of_dist_le_two a e h.color_a h.color_e (by
      rw [SimpleGraph.dist_comm, h.dist_ea])
  have hYS : V R d ⊓ Q R a ≤ stabilizer R e := inf_le_right.trans haS
  let := geometry.Z_elementary (by omega) d h.color_d
  let := endpointImage_elementary source frame (Z R d) hdS
  have hfour : Nat.card (endpointImage source frame (Z R d)) = 4 := by
    rw [endpointImage_card source frame (Z R d) hdS, h.actor_index common hb]
  have hcent : endpointImage source frame (V R d ⊓ Q R a) ≤
      centralizer (endpointImage source frame (Z R d) : Set SL) := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul]
    apply congrArg (frame.projection source)
    apply Subtype.ext
    exact (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes d h.color_d)) hz (y : FreeAmalgam R)
        (radius_le_Q common d h.color_d hy.1) |>.symm
  have hle : V R d ⊓ Q R a ≤ Q R e ⊔ Z R d :=
    le_sup_kernel_of_image_le frame _ _ hYS
      (hcent.trans (fourGroup_centralizer _ hfour))
  have heq : ⁅Z R e,Z R d⁆ = ⁅Z R e,Q R e ⊔ Z R d⁆ :=
    commutator_eq_of_centralizing_sup rfl
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes e h.color_e))) (hdS.trans (Z_normalized R e))
  calc
    ⁅V R d ⊓ Q R a,Z R e⁆ ≤ ⁅Q R e ⊔ Z R d,Z R e⁆ :=
      commutator_mono hle le_rfl
    _ = ⁅Z R d,Z R e⁆ := by
      rw [commutator_comm _ (Z R e), ← heq, commutator_comm]

/-- The intersection fixes the radius quotient by its own Z-layer. -/
theorem intersection_commutator_le_Z (h : NoncentralPair R a d e)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4) :
    ⁅V R d ⊓ Q R a,Z R e⁆ ≤ Z R d :=
  (h.intersection_commutator common hb).trans
    (le_normalizer_iff_commutator_le_left.mp
      ((source.critical_Z_le_stabilizer geometry d h.color_d e
        (h.critical_pair common hb)).2.trans (Z_normalized R d)))

private theorem radius_index_le_four (h : NoncentralPair R a d e)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4) :
    (Q R a).relIndex (V R d) ≤ 4 := by
  obtain ⟨frame⟩ := exists_frame a h.color_a
  have hVS : V R d ≤ stabilizer R a := (radius_le_Q common d h.color_d).trans
    (Q_le_stabilizer_of_dist_le_two d a h.color_d h.color_a h.dist_da.le)
  have hZQ : Z R d ≤ Q R a :=
    Z_le_Q_of_dist_lt R d (geometry.exists_critical d h.color_d) (by
      rw [geometry.distance_constant d h.color_d, h.dist_da]; exact common.large_distance)
  let := radius_image_elementary common hb d a h.color_d frame hVS hZQ
  rw [← endpointImage_card source frame (V R d) hVS]
  exact elementary_card_le_four _

/-- The source bound uses precisely the published quotient-centralizer preimage. -/
theorem small_displacement (h : NoncentralPair R a d e)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4) :
    (radiusFixed geometry d (Z R e)).relIndex (V R d) ≤
      (Q R d).relIndex (Z R e) := by
  have hcrit := h.critical_pair common hb
  have hrev := common.critical_reverse d h.color_d e h.color_e hcrit
  have heq : (Q R d).relIndex (Z R e) = 4 := by
    rw [(naturalStructure common).critical_Z_index_eq_U geometry e h.color_e d hrev,
      ← (moduleFacts common).critical_U_index d h.color_d e hcrit,
      ← (naturalStructure common).critical_Z_index_eq_U geometry d h.color_d e hcrit,
      h.actor_index common hb]
  rw [heq]
  have heS := (source.critical_Z_le_stabilizer geometry d h.color_d e hcrit).2
  have hfix : V R d ⊓ Q R a ≤ radiusFixed geometry d (Z R e) := by
    intro x hx
    apply (mem_radiusFixed_iff common d h.color_d (Z R e) heS x).mpr
    refine ⟨hx.1, fun g hg => ?_⟩
    have hc := h.intersection_commutator_le_Z common hb
    rw [commutator_comm] at hc
    exact hc (commutator_mem_commutator hg hx)
  let := finite_radius common d h.color_d
  calc
    (radiusFixed geometry d (Z R e)).relIndex (V R d) ≤
        (V R d ⊓ Q R a).relIndex (V R d) :=
      relIndex_le_of_le_left hfix (index_ne_zero_of_finite (H :=
        (V R d ⊓ Q R a).subgroupOf (V R d)))
    _ = (Q R a).relIndex (V R d) := inf_relIndex_left _ _
    _ ≤ 4 := h.radius_index_le_four common hb

/-- The first geometric calculation in original MS93 (4.6.3), at the actual pair. -/
theorem displacement (h : NoncentralPair R a d e)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4) :
    (Q R e).relIndex (Z R d) = 4 ∧
      ⁅V R d ⊓ Q R a,Z R e⁆ ≤ Z R d ∧
      (radiusFixed geometry d (Z R e)).relIndex (V R d) ≤
        (Q R d).relIndex (Z R e) :=
  ⟨h.actor_index common hb, h.intersection_commutator_le_Z common hb,
    h.small_displacement common hb⟩

/-- The source offender application, with its displacement premise discharged. -/
theorem derived_eq_U (h : NoncentralPair R a d e)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4) :
    ⁅V R d,V R d⁆ = U R d :=
  h.derived_eq_U_of_small_displacement common hb (h.small_displacement common hb)
end NoncentralPair
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
