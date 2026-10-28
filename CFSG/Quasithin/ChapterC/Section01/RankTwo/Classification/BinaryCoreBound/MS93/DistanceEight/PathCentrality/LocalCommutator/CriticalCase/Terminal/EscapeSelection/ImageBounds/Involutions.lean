module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.EscapeSelection.Path
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting
public import Theory.GroupAction.CyclicQuotientRestrictionBound

/-!
# Small image orders and actual radius involutions

Let d and v be the backward vertex and predecessor in MS93 (4.4.1).
If V_v has image of order at most two modulo Q_c, claim (3) puts
[V_v cap Q_c,Z_d] in Z_v. Choose an element of Z_d outside Q_v using
the retained critical pair. The displacement homomorphism on V_v/Z_v
then has image of order at most two. We retain this actual involution,
its kernel nonmembership and its displacement on the full quotient.

The all-rho hypothesis separately supplies the residual triple bound.
The already proved faithful radius-head action and binary recognition
therefore construct the complete natural section at v, without a
contrary configuration from (4.3). Simultaneous conjugation transports
the full-quotient involution to any M-type center.

This does not yet exclude that involution using the original local-span
condition: that recognition step remains an explicit assembly input.
A natural section of the radius head alone must not be confused with
one for an arbitrary local span with its own radical quotient.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1), printed p.892, immediately after claim (3); the earlier
binary representation calculations implement (1.4)--(1.5), pp.842--843.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.EscapeSelection.ImageBounds
open Escape.Initial.Natural Escape.Initial.Natural.Splitting
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
/-- A genuine involution outside the neighborhood kernel, with at most
one-dimensional displacement on the literal full radius quotient V/Z. -/
def HasSmallRadiusInvolution (v : Vertex R) : Prop :=
  ∃ x : stabilizer R v, (x : FreeAmalgam R) ∉ Q R v ∧ x ^ 2 = 1 ∧
    (Z R v).relIndex ⁅V R v, zpowers (x : FreeAmalgam R)⁆ ≤ 2

/-- Recognize and lift the actual radius-head action from a small involution
on the full radius quotient and the residual triple bound. -/
theorem radius_section_of_small_displacement
    (common : CommonFacts R source geometry) (hb : 2 < geometry.b R)
    {v : Vertex R} (hv : color R v = false)
    (htriple : ⁅⁅V R v, Q R v⁆, Ltilde R v⁆ ≤ Z R v)
    (x : stabilizer R v) (hx : (x : FreeAmalgam R) ∉ Q R v)
    (htwo : x ^ 2 = 1)
    (hsmall : (Z R v).relIndex ⁅V R v, zpowers (x : FreeAmalgam R)⁆ ≤ 2) :
    Nonempty (Escape.NaturalSectionAt v (V R v) (Z R v)) := by
  let S := stabilizer R v
  let H := localRadius v
  let N := Escape.Initial.Natural.Splitting.localZ v
  let Q₀ := localKernel v
  let π := localProjection source v hv
  let ρ := radiusHeadAction source geometry v hv
  let := finite_stabilizer R v
  let := geometry.Z_normal v
  let := radiusHead_elementary source geometry hb (moduleFacts common) v hv
  have hπx : π x ≠ 1 := by
    intro he
    have hk : x ∈ π.ker := he
    rw [localProjection_kernel] at hk
    exact hx hk
  have hdisp : Nat.card (commutatorAction (zpowers (ρ (π x)))
      (RadiusHead geometry v)) ≤ 2 := by
    have hmap : (zpowers x).map (ρ.comp π) = zpowers (ρ (π x)) :=
      MonoidHom.map_zpowers _ _
    rw [← hmap]
    change Nat.card (commutatorAction ((zpowers x).map
      ((headAction H N Q₀ π (localProjection_surjective source v hv)
        (localProjection_kernel source v hv)).comp π))
      (H ⧸ (Escape.radicalPreimage Q₀ H N).subgroupOf H)) ≤ 2
    rw [headAction_comp, quotientAction_displacement_card]
    have hi := relIndex_map_map_of_injective N ⁅H, zpowers x⁆ S.subtype_injective
    rw [map_subgroupOf_eq_of_le (Z_le_stabilizer R v), map_commutator,
      map_subgroupOf_eq_of_le ((geometry.V_le_Q hb v hv).trans (fun _ hy => hy.1)),
      MonoidHom.map_zpowers] at hi
    have hsmall' : N.relIndex ⁅H, zpowers x⁆ ≤ 2 := by
      rw [← hi]
      exact hsmall
    exact (relIndex_le_of_le_left
      (show N ≤ Escape.radicalPreimage Q₀ H N from le_sup_left)
      (by exact index_ne_zero_of_finite)).trans hsmall'
  obtain ⟨s⟩ := naturalActionSplitting_of_small_involution ρ
    (radiusHeadAction_injective_of_triple source geometry hb (moduleFacts common) v hv htriple)
    ⟨π x, hπx, by rw [← map_pow, htwo, map_one], hdisp⟩
  obtain ⟨ss⟩ := singleNaturalSection_of_head_splitting H N Q₀
    (pResidual 2 S) π (localProjection_surjective source v hv)
    (localProjection_kernel source v hv)
    (fun _ hy => Z_le_VBall R v 2 hy)
    (elementary_radius_quotient source geometry hb (moduleFacts common) v hv)
    (local_triple geometry hb v hv htriple) s
  exact ⟨{
    local_group := (geometry.V_le_Q hb v hv).trans (fun _ hy => hy.1)
    kernel_le := Z_le_VBall R v 2
    projection := π
    module_section := ss }⟩

/-- Claim (3) and a small predecessor image produce an actual involution
with displacement of order at most two on the full predecessor quotient. -/
theorem small_radius_involution_of_small_image
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (hsmall : (Q R c).relIndex (V R w.predecessor) ≤ 2) :
    HasSmallRadiusInvolution w.predecessor := by
  let v := w.predecessor
  let S := stabilizer R v
  let H := localRadius v
  let N := Escape.Initial.Natural.Splitting.localZ v
  let K := (V R v ⊓ Q R c).subgroupOf S
  have hHS : V R v ≤ S :=
    (geometry.V_le_Q (by omega) v w.predecessor_color).trans (fun _ hy => hy.1)
  have hZS : Z R w.backward ≤ S :=
    ((w.shifted ha (by omega)).reverse common).endpoint_Z_le_start_stabilizer (by omega)
  obtain ⟨z, hz, hzQ⟩ := Set.not_subset.mp w.noncontainment
  let x : S := ⟨z, hZS hz⟩
  have htwo : x ^ 2 = 1 := by
    let := geometry.Z_elementary (by omega) w.backward (w.backward_color ha)
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian z hz)
  have hKN : ⁅K, zpowers x⁆ ≤ N := by
    intro y hy
    have hm := mem_map_of_mem S.subtype hy
    rw [map_commutator, map_subgroupOf_eq_of_le (inf_le_left.trans hHS),
      MonoidHom.map_zpowers] at hm
    have hbnd : ⁅V R v ⊓ Q R c, zpowers z⁆ ≤ Z R v := by
      apply (commutator_mono le_rfl (zpowers_le.mpr hz)).trans
      rw [commutator_comm, source_claim_three common hb ha hd w]
      exact le_normalizer_iff_commutator_le_right.mp (hZS.trans (Z_normalized R v))
    exact hbnd hm
  let := finite_stabilizer R v
  let := geometry.Z_normal v
  have hderived : ⁅H, H⁆ ≤ N := by
    intro y hy
    have hm := mem_map_of_mem S.subtype hy
    rw [map_commutator, map_subgroupOf_eq_of_le hHS] at hm
    exact radius_derived_le_Z source geometry (by omega) (moduleFacts common)
      v w.predecessor_color hm
  have hidx : K.relIndex H = (Q R c).relIndex (V R v) := by
    rw [← relIndex_map_map_of_injective K H S.subtype_injective,
      map_subgroupOf_eq_of_le (inf_le_left.trans hHS), map_subgroupOf_eq_of_le hHS,
      inf_relIndex_left]
  have hdisp := quotient_commutator_relIndex_le_mul_of_restriction
    H K N N (comap_mono inf_le_left) (fun _ hy => Z_le_VBall R v 2 hy)
    (fun _ hy => Z_le_VBall R v 2 hy) inferInstance hderived
    x (by rw [normalizer_eq_top]; trivial) hKN
  rw [relIndex_self, mul_one, hidx] at hdisp
  have hdisp' : N.relIndex ⁅H, zpowers x⁆ ≤ 2 := by
    rw [relIndex_sup_right] at hdisp
    exact hdisp.trans hsmall
  have hi := relIndex_map_map_of_injective N ⁅H, zpowers x⁆ S.subtype_injective
  rw [map_subgroupOf_eq_of_le (Z_le_stabilizer R v), map_commutator,
    map_subgroupOf_eq_of_le hHS, MonoidHom.map_zpowers] at hi
  exact ⟨x, hzQ, htwo, hi.trans_le hdisp'⟩


/-- The original all-rho hypothesis turns the constructed small involution
into a complete natural section at the predecessor. -/
theorem predecessor_section_of_small_image
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (hall : ∀ rho, (cosetGraph R).dist c rho = 2 →
      ⁅Z R rho, Q R c⁆ ≤ B R c (geometry.Z_normal c))
    (hsmall : (Q R c).relIndex (V R w.predecessor) ≤ 2) :
    Nonempty (Escape.NaturalSectionAt w.predecessor
      (V R w.predecessor) (Z R w.predecessor)) := by
  obtain ⟨x, hx, htwo, hi⟩ := small_radius_involution_of_small_image common hb ha hd w hsmall
  exact radius_section_of_small_displacement common (by omega) w.predecessor_color
    (radius_triple_le_Z_at_any_center (by omega) w.path.start_color hall w.predecessor_color)
    x hx htwo hi

omit [Finite M] in
/-- Conjugation transports the actual involution and its full V/Z displacement. -/
theorem small_radius_involution_at_any_center {v c : Vertex R}
    (hv : color R v = false) (hc : color R c = false)
    (hs : HasSmallRadiusInvolution v) : HasSmallRadiusInvolution c := by
  obtain ⟨g, hg⟩ := exists_mVertex_of_color R hv
  obtain ⟨h, hh⟩ := exists_mVertex_of_color R hc
  let k := g⁻¹ * h
  have he : act R k v = c := by
    simp only [k, hg, hh, act_mVertex, mul_inv_cancel_left]
  obtain ⟨x, hx, htwo, hi⟩ := hs
  let f := (MulAut.conj k⁻¹).toMonoidHom
  have hxf : f x ∈ stabilizer R c := by
    rw [← he, stabilizer_act]
    exact mem_map_of_mem f x.property
  let y : stabilizer R c := ⟨f x, hxf⟩
  refine ⟨y, ?_, ?_, ?_⟩
  · intro hy
    have hmem : f x ∈ (Q R v).map f := by
      simpa only [← he, Q_act] using hy
    obtain ⟨u, hu, heu⟩ := hmem
    exact hx ((MulAut.conj k⁻¹).injective heu ▸ hu)
  · apply Subtype.ext
    change (f x) ^ 2 = 1
    rw [← map_pow, show (x : FreeAmalgam R) ^ 2 = 1 from congrArg Subtype.val htwo, map_one]
  · change (Z R c).relIndex ⁅V R c, zpowers (f x)⁆ ≤ 2
    rw [← he, Z_act, V_act, ← MonoidHom.map_zpowers, ← map_commutator,
      relIndex_map_map_of_injective _ _ (MulAut.conj k⁻¹).injective]
    exact hi

/-- The first image bound, conditional on excluding a small involution on
V/Z. The original local-span obstruction is a separate module argument. -/
theorem predecessor_image_gt_two_of_no_small_involution
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (hnat : ¬ HasSmallRadiusInvolution c) :
    2 < (Q R c).relIndex (V R w.predecessor) := by
  by_contra h
  exact hnat (small_radius_involution_at_any_center w.predecessor_color w.path.start_color
    (small_radius_involution_of_small_image common hb ha hd w (by omega)))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.EscapeSelection.ImageBounds
