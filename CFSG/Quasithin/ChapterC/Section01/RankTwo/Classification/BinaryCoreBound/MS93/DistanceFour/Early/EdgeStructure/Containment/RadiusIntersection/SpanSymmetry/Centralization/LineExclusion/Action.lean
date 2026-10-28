module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.RadiusIntersection.SpanSymmetry.Centralization.Reduction

/-!
# The self-dual quotient obstruction for the midpoint span

The initial radius centrality makes Q_a act trivially on W/Z(W), where
W = ⟨Z_e^{G_a}⟩. Thus conjugation descends through the actual local
SL₃(2) quotient. Simplicity makes this action faithful whenever W is
nonabelian: a trivial action would put every conjugate of its abelian
seed in the seed times Z(W).

When W' is a central subgroup of order two, its commutator pairing gives
self-duality. The critical endpoint Z_r has nontrivial elementary image
in G_a/Q_a. The crossing commutator bound shows that W intersect Q_e is
fixed modulo Z(W). Consequently an image of W in G_e/Q_e of order at
most two gives an offender, contrary to the checked self-dual binary
SL₃(2) obstruction.

The local action and index proofs adapt the corresponding arguments in
AbelianSpans/Offender/SpanAction/Basic.lean and FFBound.lean. Here kernel
descent only needs [W,Q_a] to centralize W, as supplied by InitialFacts;
it does not assume the stronger centrality in G_a of that commutator.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.4), printed p.902. The quotient is the literal W/Z(W), with
its actual conjugation action and local quotient projection.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanSymmetry.LineExclusion
open SpanOffender
variable {G : Type*} [Group G]

private theorem derived_le_center (W S : Subgroup G) (hWS : W ≤ S)
    (hc : ⁅W,W⁆ ≤ centralizer (S : Set G)) :
    _root_.commutator W ≤ center W := by
  intro x hx
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact hc (W.map_subtype_commutator ▸ mem_map_of_mem W.subtype hx) y (hWS y.property)

private theorem elementary_central_quotient (W : Subgroup G)
    (hc : _root_.commutator W ≤ center W) (hΩ : omegaOneAmbient W = W) :
    IsElementaryAbelian 2 (W ⧸ center W) := by
  let : IsMulCommutative (W ⧸ center W) :=
    Normal.quotient_commutative_iff_commutator_le.mpr hc
  refine ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
  intro v
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center W) v
  apply MonoidHom.square_eq_one_on_omega₁
  have hx : (x : G) ∈ omegaOneAmbient W := by rw [hΩ]; exact x.property
  obtain ⟨y,hy,he⟩ := hx
  have : y = x := Subtype.ext he
  rwa [← this]

private noncomputable def centralConjugation (S W : Subgroup G)
    (hn : S ≤ normalizer (W : Set G)) : S →* MulAut (W ⧸ center W) :=
  (Subgroup.quotientAut (center W)).comp (Offenders.conjugation S W hn)

private theorem centralConjugation_apply (S W : Subgroup G)
    (hn : S ≤ normalizer (W : Set G)) (g : S) (x : W) :
    centralConjugation S W hn g (QuotientGroup.mk' (center W) x) =
      QuotientGroup.mk' (center W) (Offenders.conjugation S W hn g x) := by
  exact Subgroup.quotientAut_apply_mk _ _ _

private theorem centralConjugation_kills (S N W : Subgroup G)
    (_hW : W ≤ S) (hn : S ≤ normalizer (W : Set G))
    (hc : ⁅W,N⁆ ≤ centralizer (W : Set G)) :
    N.subgroupOf S ≤ (centralConjugation S W hn).ker := by
  intro g hg
  apply MulEquiv.ext
  intro v
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center W) v
  rw [centralConjugation_apply]
  apply QuotientGroup.eq_iff_div_mem.mpr
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  have hd : ⁅(g : G), (x : G)⁆ ∈ ⁅W,N⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator hg x.property
  have hh := hc hd y y.property
  change (y : G) * ((g : G) * (x : G) * (g : G)⁻¹ / (x : G)) =
    ((g : G) * (x : G) * (g : G)⁻¹ / (x : G)) * (y : G)
  simpa only [commutatorElement_def, div_eq_mul_inv] using hh

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem commutative_sup_center {H : Type*} [Group H]
    (A : Subgroup H) [IsMulCommutative A] : IsMulCommutative (A ⊔ center H : Subgroup H) := by
  apply le_centralizer_iff_isMulCommutative.mp
  have hA : A ⊔ center H ≤ centralizer (A : Set H) :=
    sup_le A.le_centralizer (center_le_centralizer _)
  exact sup_le (le_centralizer_iff.mp hA) (center_le_centralizer _)

omit [Finite M] in
private theorem centralConjugation_nontrivial (a d : Vertex R)
    (hseed : IsMulCommutative (Z R d))
    (hnon : ¬ IsMulCommutative (neighborSpan a d)) :
    centralConjugation (stabilizer R a) (neighborSpan a d) (neighborSpan_normalized a d) ≠ 1 := by
  let W := neighborSpan a d
  let S := stabilizer R a
  let A := (Z R d).subgroupOf W
  let K := A ⊔ center W
  let q := QuotientGroup.mk' (center W)
  let := hseed
  let : IsMulCommutative A := subgroupOf_isMulCommutative W (Z R d)
  let : IsMulCommutative K := commutative_sup_center A
  intro he
  have hle : W ≤ K.map W.subtype := by
    apply iSup_le
    intro g
    rintro _ ⟨z,hz,rfl⟩
    let x : W := ⟨z,Z_le_neighborSpan a d hz⟩
    let y : W := Offenders.conjugation S W (neighborSpan_normalized a d) g x
    have hq : q y = q x := by
      have hh := DFunLike.congr_fun
        (DFunLike.congr_fun he g) (q x)
      rw [centralConjugation_apply] at hh
      exact hh
    have hd : y / x ∈ center W := QuotientGroup.eq_iff_div_mem.mp hq
    have hxK : x ∈ K := (show A ≤ K from le_sup_left) hz
    have hyK : y ∈ K := by
      have hh := K.mul_mem ((show center W ≤ K from le_sup_right) hd) hxK
      simpa only [div_mul_cancel] using hh
    exact ⟨y,hyK,rfl⟩
  have heq : K.map W.subtype = W := le_antisymm (map_subtype_le _) hle
  apply hnon
  change IsMulCommutative W
  rw [← heq]
  exact map_isMulCommutative K W.subtype

include source in
/-- A nonabelian span carries the actual faithful action of its local SL₃(2) quotient. -/
private theorem spanCentralAction_of_radius_nonempty (a d : Vertex R) (ha : color R a = false)
    (hWQ : neighborSpan a d ≤ Q R a)
    (hc : ⁅neighborSpan a d, Q R a⁆ ≤
      centralizer (neighborSpan a d : Set (FreeAmalgam R)))
    (hseed : IsMulCommutative (Z R d))
    (hnon : ¬ IsMulCommutative (neighborSpan a d)) :
    Nonempty (SpanCentralAction a (neighborSpan a d)) := by
  let W := neighborSpan a d
  let S := stabilizer R a
  have hWS : W ≤ S := hWQ.trans (fun _ hx => hx.1)
  let : Finite S := finite_stabilizer R a
  have hfin : Finite W := Finite.of_injective (inclusion hWS) (inclusion_injective hWS)
  let F := centralConjugation S W (neighborSpan_normalized a d)
  obtain ⟨π,hπ,hker⟩ := span_local_projection (source := source) a ha
  have hkill : π.ker ≤ F.ker := by
    rw [hker]
    exact centralConjugation_kills S (Q R a) W hWS (neighborSpan_normalized a d) hc
  let ρ := π.liftOfSurjective hπ ⟨F,hkill⟩
  have hρ (g : S) : ρ (π g) = F g :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hfaith : Function.Injective ρ := by
    let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
    rcases (inferInstance : ρ.ker.Normal).eq_bot_or_eq_top with ht | ht
    · exact ρ.ker_eq_bot_iff.mp ht
    · exfalso
      apply centralConjugation_nontrivial a d hseed hnon
      have htriv := MonoidHom.ker_eq_top_iff.mp ht
      apply MonoidHom.ext
      intro g
      rw [← hρ, htriv]
      rfl
  refine ⟨{
    finite := hfin
    normalized := neighborSpan_normalized a d
    elementary := elementary_central_quotient W
      (derived_le_center W W le_rfl ((commutator_mono le_rfl hWQ).trans hc))
      (neighborSpan_omegaOne a d)
    projection := π
    projection_surjective := hπ
    projection_kernel := hker
    action := ρ
    faithful := hfaith
    conjugation := ?_ }⟩
  intro g x y hy
  rw [hρ, centralConjugation_apply]
  congr 1
  exact Subtype.ext hy.symm



namespace OffenderBound
variable {H Y : Type*} [Group H] [Group Y]
private def fixed (f : H →* MulAut Y) (A : Subgroup H) : Subgroup Y :=
  letI := MulDistribMulAction.compHom Y (f.comp A.subtype)
  FixedPoints.subgroup A Y

private theorem linearize_isOffender [Finite Y] [IsElementaryAbelian 2 Y]
    (f : H →* MulAut Y) (A : Subgroup H) [Finite A] [IsElementaryAbelian 2 A]
    (hne : A ≠ ⊥) (hb : (fixed f A).index ≤ Nat.card A) :
    Representation.BinaryOffender.IsOffender (Offenders.linearize f) A := by
  let e : Representation.BinaryOffender.fixedSpace (Offenders.linearize f) A ≃ fixed f A := {
    toFun := fun v => ⟨v.val.toMul, fun a => congrArg Additive.toMul (v.property a)⟩
    invFun := fun y => ⟨Additive.ofMul y.val, fun a => congrArg Additive.ofMul (y.property a)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hcard : Nat.card Y ≤ Nat.card (fixed f A) * Nat.card A := by
    rw [← (fixed f A).card_mul_index]
    exact Nat.mul_le_mul_left _ hb
  rw [← Nat.card_congr e] at hcard
  have hVcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Y)
  have hFcard := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Representation.BinaryOffender.fixedSpace (Offenders.linearize f) A)
  rw [Nat.card_zmod] at hVcard hFcard
  have hAcard : Nat.card A = 2 ^ Representation.BinaryOffender.rank A := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    unfold Representation.BinaryOffender.rank
    rw [hn, Nat.log_pow (by decide : 1 < 2)]
  change Nat.card (Additive Y) ≤ _ at hcard
  rw [hVcard, hFcard, hAcard, ← pow_add] at hcard
  have hd := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard
  have hr := Representation.BinaryOffender.fixedCodim_add_finrank (Offenders.linearize f) A
  exact ⟨⟨hne, inferInstance⟩, by omega⟩

omit [Finite M] in
private theorem fixed_index_le (a : Vertex R) (W E N : Subgroup (FreeAmalgam R))
    (c : SpanCentralAction a W)
    (hc : ⁅W ⊓ N,E⁆ ≤ centralizer (W : Set (FreeAmalgam R))) :
    (fixed c.action ((E.subgroupOf (stabilizer R a)).map c.projection)).index ≤
      N.relIndex W := by
  let := c.finite
  let q := QuotientGroup.mk' (center W)
  have hfix : (N.subgroupOf W).map q ≤
      fixed c.action ((E.subgroupOf (stabilizer R a)).map c.projection) := by
    rintro _ ⟨x,hx,rfl⟩ g
    obtain ⟨s,hs,he⟩ := g.property
    change c.action (g : SL) (q x) = q x
    rw [← he]
    let y := Offenders.conjugation (stabilizer R a) W c.normalized s x
    rw [c.conjugation s x y rfl]
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply mem_center_iff.mpr
    intro z
    apply Subtype.ext
    have hd : ⁅(s : FreeAmalgam R),(x : FreeAmalgam R)⁆ ∈ ⁅W ⊓ N,E⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator hs ⟨x.property,hx⟩
    have hh := hc hd z z.property
    change (z : FreeAmalgam R) * ((s : FreeAmalgam R) * (x : FreeAmalgam R) *
      (s : FreeAmalgam R)⁻¹ / (x : FreeAmalgam R)) =
      ((s : FreeAmalgam R) * (x : FreeAmalgam R) *
      (s : FreeAmalgam R)⁻¹ / (x : FreeAmalgam R)) * (z : FreeAmalgam R)
    simpa only [commutatorElement_def, div_eq_mul_inv] using hh
  refine (index_antitone hfix).trans ?_
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (N.subgroupOf W).index_ne_zero_of_finite)
    ((N.subgroupOf W).index_map_dvd (QuotientGroup.mk'_surjective (center W)))


end OffenderBound

/-- A central derived line excludes a midpoint-span image of order at most two. -/
theorem midpoint_span_not_small_of_derived_line
    (common : CommonFacts R source geometry) (initial : InitialFacts R geometry)
    (a b d : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (p : PairedSpans geometry a b d ha)
    (hcard : Nat.card (⁅neighborSpan a p.e,neighborSpan a p.e⁆ : Subgroup (FreeAmalgam R)) = 2)
    (hcentral : ⁅neighborSpan a p.e,neighborSpan a p.e⁆ ≤
      centralizer (stabilizer R a : Set (FreeAmalgam R))) :
    ¬ (Q R p.e).relIndex (neighborSpan a p.e) ≤ 2 := by
  intro hsmall
  let W := neighborSpan a p.e
  have hWV : W ≤ V R a := neighborSpan_le_radius a p.e (by
    rw [SimpleGraph.dist_comm]; exact p.near.le)
  have hWQ : W ≤ Q R a := hWV.trans (radius_le_Q common a ha)
  have hWS : W ≤ stabilizer R a := hWQ.trans (fun _ hx => hx.1)
  have hc : ⁅W,Q R a⁆ ≤ centralizer (W : Set (FreeAmalgam R)) := by
    rintro x hx w hw
    obtain ⟨z,hz,rfl⟩ := initial.commutator_central a ha (commutator_mono hWV le_rfl hx)
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨w,hWV hw⟩)
  have hnon : ¬ IsMulCommutative W := by
    intro hh
    have hz := commutator_self_eq_bot_iff.mpr hh
    change Nat.card (⁅W,W⁆ : Subgroup (FreeAmalgam R)) = 2 at hcard
    rw [hz, Nat.card_eq_fintype_card] at hcard
    simp at hcard
  let := geometry.Z_elementary (lt_trans (by decide : 0 < 2) common.large_distance) p.e p.he
  obtain ⟨c⟩ := spanCentralAction_of_radius_nonempty (source := source) a p.e ha hWQ hc
    inferInstance hnon
  let := c.finite
  let := c.elementary
  let : Module.Finite (ZMod 2) (Additive (W ⧸ center W)) := Module.Finite.of_finite
  have hdual := c.selfDual hWS hcard hcentral
  let A := ((Z R p.r).subgroupOf (stabilizer R a)).map c.projection
  have hAS : Z R p.r ≤ stabilizer R a := p.seed_edge.trans
    (fun _ hx => hx.2 a (adjacent_symm R hab))
  have hesc := (common.critical_reverse a ha p.r p.hr p.critical).2
  have hne : A ≠ ⊥ := by
    intro hh
    have hk := (Subgroup.map_eq_bot_iff _).mp hh
    rw [c.projection_kernel] at hk
    exact hesc (fun x hx => hk (show
      (⟨x,hAS hx⟩ : stabilizer R a) ∈ (Z R p.r).subgroupOf (stabilizer R a) from hx))
  let := geometry.Z_elementary (lt_trans (by decide : 0 < 2) common.large_distance) p.r p.hr
  let : IsElementaryAbelian 2 ((Z R p.r).subgroupOf (stabilizer R a)) :=
    IsElementaryAbelian.subgroupOf hAS
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map c.projection
  have hcross : ⁅W ⊓ Q R p.e,Z R p.r⁆ ≤ centralizer (W : Set (FreeAmalgam R)) := by
    have hZa : Z R a ≤ centralizer (W : Set (FreeAmalgam R)) :=
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha)).trans
        (centralizer_le hWQ)
    rw [commutator_comm]
    exact (commutator_mono le_rfl inf_le_right).trans ((p.layer_right.trans inf_le_left).trans hZa)
  have hidx : (OffenderBound.fixed c.action A).index ≤ Nat.card A := by
    have hh := (OffenderBound.fixed_index_le a W (Z R p.r) (Q R p.e) c hcross).trans hsmall
    have hge := (one_lt_card_iff_ne_bot A).mpr hne
    exact hh.trans (by omega)
  exact not_isFFModule_of_faithful_selfDual (Offenders.linearize c.action)
    (Offenders.linearize_injective c.action c.faithful) hdual
    ⟨A,OffenderBound.linearize_isOffender c.action A hne hidx⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanSymmetry.LineExclusion
