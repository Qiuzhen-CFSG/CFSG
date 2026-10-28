module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Escape.Contradiction.Geometry

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Escape.Contradiction.Fixed.Linear

/-!
# Full first-actor fixation from the moving-neighbor bound

A moving neighbor has noncentral displacement, so its radius kernel has
index four in V_alpha and V_alpha Q_mu = Q_beta. Enlarging the actor by
Q_mu changes its commutators only inside B_mu. Neighbor transitivity then
transports the index bound to [V_alpha,Q_beta] modulo B_alpha, using the
original conjugation maps. The starred intersection with B_alpha is exactly
Z_alpha, so every actual starred layer module has edge displacement rank
at most two.

The literal fixed preimage Y is fixed by the first intrinsic core. The two
genuine natural sections show that a marked cubic has fixed space contained
in Y and moves at least four dimensions. The radius splits into its central
part, fixed modulo Z_alpha, and its actual starred part. Consequently the
same cubic moves at least four dimensions in the starred module. The finite
parabolic displacement theorem now promotes core fixation to full-actor
fixation there, and the central splitting transfers this to the supplied
radius module. The full actor remains distinct from its ordered residual.

The final source-facing theorem retains the contained seed, orbit span,
marked dual quotient and nonzero-neighbor premises. Once the neighbor bound
is explicit, the fixation argument itself needs only that bound and the two
natural sections; the other premises remain for the parent source assembly.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), notation on printed p.905 and (4.6.12)(1)--(4), pp.910--911.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
/-- A neighbor outside B_alpha has displacement outside the local center. -/
theorem moving_neighbor_noncentral (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (μ : Vertex R)
    (hν : nu R geometry (alpha R) μ) :
    ¬ ⁅Z R μ, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype := by
  intro hc
  have hZV : Z R μ ≤ V R (alpha R) :=
    le_iSup_of_le μ (le_iSup_of_le hν.1.le le_rfl)
  have hzero : ⁅Z R μ, V R (alpha R)⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← Sections.U_inf_localCenter_eq_bot common]
    exact le_inf ((commutator_mono hZV le_rfl).trans_eq
      (radius.radius_derived (alpha R) rfl)) hc
  apply hν.2
  rw [radius.B_eq_center (alpha R) rfl]
  intro z hz
  refine ⟨⟨z, hZV hz⟩, mem_center_iff.mpr ?_, rfl⟩
  intro v
  exact Subtype.ext (commutator_eq_bot_iff_le_centralizer.mp hzero hz v v.property)

/-- The moving-neighbor kernel supplements the original radius to the full edge core. -/
theorem moving_neighbor_radius_supplement (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (μ : Vertex R) (hν : nu R geometry (alpha R) μ)
    (hμ : Adjacent R (beta R) μ) :
    V R (alpha R) ⊔ Q R μ = Q R (beta R) := by
  obtain ⟨k⟩ := Sections.exists_frame common radius hb
  have hd : (cosetGraph R).dist (alpha R) μ = 2 :=
    (cosetGraph R).dist_comm.trans hν.1
  have hi := (Flags.RankOne.displacement_cardinalities source geometry common hb
    radius.toEarlyFacts k.flagControl μ hd hμ
    (moving_neighbor_noncentral common radius μ hν)).2.2.2
  exact Flags.RankOne.radius_sup_midpoint_kernel geometry common.large_distance
    radius.toEarlyFacts μ (distance_two_color rfl hd) hμ hi


private theorem relIndex_join_right {G : Type*} [Group G]
    (D B E : Subgroup G) (hDE : D ≤ E) (hBE : B ≤ E)
    (hn : E ≤ normalizer B) : B.relIndex (D ⊔ B) = B.relIndex D := by
  let : (B.subgroupOf E).Normal := normal_subgroupOf_of_le_normalizer hn
  have h := relIndex_sup_right (D.subgroupOf E) (B.subgroupOf E)
  rw [← subgroupOf_sup hDE hBE, relIndex_subgroupOf (sup_le hDE hBE),
    relIndex_subgroupOf hDE] at h
  exact h

/-- Enlarging the actor by Q_mu costs no displacement modulo B_mu. -/
theorem moving_neighbor_edge_bound (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (μ : Vertex R) (hν : nu R geometry (alpha R) μ)
    (hμ : Adjacent R (beta R) μ)
    (hdisp : (B R μ (geometry.Z_normal μ)).relIndex ⁅V R (alpha R), V R μ⁆ ≤ 4) :
    (B R μ (geometry.Z_normal μ)).relIndex ⁅Q R (beta R), V R μ⁆ ≤ 4 := by
  have hc : color R μ = false := distance_two_color rfl
    ((cosetGraph R).dist_comm.trans hν.1)
  have hQE : Q R μ ≤ Q R (beta R) := Q_le_adjacent_h R rfl (adjacent_symm R hμ)
  have hAE : V R (alpha R) ≤ Q R (beta R) :=
    (Flags.V_le_Q geometry common.large_distance _ rfl).trans
      (Q_le_adjacent_h R rfl (base_adjacent R))
  have hVE : V R μ ≤ Q R (beta R) :=
    (Flags.V_le_Q geometry common.large_distance _ hc).trans hQE
  have hEl : Q R (beta R) ≤ stabilizer R μ := fun _ hx => hx.2 μ hμ
  have hVN : Q R (beta R) ≤ normalizer (V R μ) :=
    hEl.trans (DistanceEight.V_normalized R μ)
  have hBN : Q R (beta R) ≤ normalizer (B R μ (geometry.Z_normal μ)) := by
    rw [radius.B_eq_center μ hc]
    exact hVN.trans (normalizer_le_normalizer_characteristic_image _ _)
  have hBE : B R μ (geometry.Z_normal μ) ≤ Q R (beta R) := by
    rw [radius.B_eq_center μ hc]
    exact (map_subtype_le _).trans hVE
  have hZB : Z R μ ≤ B R μ (geometry.Z_normal μ) :=
    Flags.Z_le_B geometry μ (geometry.V_local μ hc (by
      rw [geometry.distance_constant μ hc]; exact common.large_distance))
  have hDE : ⁅V R (alpha R), V R μ⁆ ≤ Q R (beta R) :=
    ((commutator_mono hAE le_rfl).trans
      (le_normalizer_iff_commutator_le_right.mp hVN)).trans hVE
  have hn : Q R (beta R) ≤ normalizer (Q R μ) := hEl.trans (Q_normalized R μ)
  let : ((Q R μ).subgroupOf (Q R (beta R))).Normal :=
    normal_subgroupOf_of_le_normalizer hn
  have hproduct (x : FreeAmalgam R) (hx : x ∈ Q R (beta R)) :
      ∃ a ∈ V R (alpha R), ∃ q ∈ Q R μ, a * q = x := by
    have hx' : (⟨x, hx⟩ : Q R (beta R)) ∈
        (V R (alpha R)).subgroupOf (Q R (beta R)) ⊔
          (Q R μ).subgroupOf (Q R (beta R)) := by
      rw [← subgroupOf_sup hAE hQE,
        moving_neighbor_radius_supplement common radius hb μ hν hμ, subgroupOf_self]
      trivial
    obtain ⟨a, ha, q, hq, he⟩ := mem_sup_of_normal_right.mp hx'
    exact ⟨a, ha, q, hq, congrArg Subtype.val he⟩
  have hcomm : ⁅Q R (beta R), V R μ⁆ ≤
      ⁅V R (alpha R), V R μ⁆ ⊔ B R μ (geometry.Z_normal μ) := by
    apply commutator_le.mpr
    intro x hx v hv
    obtain ⟨a, ha, q, hq, rfl⟩ := hproduct x hx
    rw [commutatorElement_mul_left_eq_conj_mul]
    apply mul_mem
    · apply mem_sup_right
      apply (mem_normalizer_iff.mp (hBN (hAE ha)) _).mp
      apply hZB
      have hc' := radius.commutator_le_Z μ hc
      rw [commutator_comm] at hc'
      exact hc' (commutator_mem_commutator hq hv)
    · exact mem_sup_left (commutator_mem_commutator ha hv)
  let : Finite (stabilizer R μ) := finite_stabilizer R μ
  let : Finite (Q R (beta R)) := Finite.of_injective
    (inclusion hEl) (inclusion_injective _)
  let : Finite (⁅V R (alpha R), V R μ⁆ ⊔ B R μ (geometry.Z_normal μ) :
    Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion (sup_le hDE hBE)) (inclusion_injective _)
  have hi := relIndex_le_of_le_right hcomm (H := B R μ (geometry.Z_normal μ))
    (show (B R μ (geometry.Z_normal μ)).relIndex
      (⁅V R (alpha R), V R μ⁆ ⊔ B R μ (geometry.Z_normal μ)) ≠ 0 from
        Subgroup.index_ne_zero_of_finite)
  rw [relIndex_join_right _ _ _ hDE hBE hBN] at hi
  exact hi.trans hdisp

private theorem map_center_image {G : Type*} [Group G] (P : Subgroup G)
    (e : G ≃* G) :
    ((center P).map P.subtype).map e.toMonoidHom =
      (center (P.map e.toMonoidHom)).map (P.map e.toMonoidHom).subtype := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨⟨e x, mem_map_of_mem _ x.property⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    rintro ⟨_, y, hy, rfl⟩
    apply Subtype.ext
    simpa only [coe_mul, map_mul, MulEquiv.coe_toMonoidHom] using
      congrArg e (congrArg Subtype.val ((mem_center_iff.mp hx) ⟨y, hy⟩))
  · rintro _ ⟨⟨_, x, hx, rfl⟩, hz, rfl⟩
    refine ⟨x, ⟨⟨x, hx⟩, ?_, rfl⟩, rfl⟩
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply e.injective
    simpa only [coe_mul, map_mul, MulEquiv.coe_toMonoidHom] using
      congrArg Subtype.val ((mem_center_iff.mp hz) ⟨e y, mem_map_of_mem _ y.property⟩)

/-- Transfer the actual neighbor quotient bound to the original edge-core action. -/
theorem edge_bound_of_neighbor_bound (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (μ : Vertex R) (hν : nu R geometry (alpha R) μ)
    (hμ : Adjacent R (beta R) μ)
    (hdisp : (B R μ (geometry.Z_normal μ)).relIndex ⁅V R (alpha R), V R μ⁆ ≤ 4) :
    (B R (alpha R) (geometry.Z_normal (alpha R))).relIndex
      ⁅V R (alpha R), Q R (beta R)⁆ ≤ 4 := by
  have hi := moving_neighbor_edge_bound common radius hb μ hν hμ hdisp
  have hc : color R μ = false := distance_two_color rfl
    ((cosetGraph R).dist_comm.trans hν.1)
  obtain ⟨g, hg, hga⟩ := stabilizer_transitive_neighbors R (beta R) hμ
    (adjacent_symm R (base_adjacent R))
  change act R g μ = alpha R at hga
  have hgβ : act R g (beta R) = beta R := hg
  have hB : B R (alpha R) (geometry.Z_normal (alpha R)) =
      (B R μ (geometry.Z_normal μ)).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [radius.B_eq_center _ rfl, radius.B_eq_center _ hc,
      map_center_image, ← V_act, hga]
  have hV : V R (alpha R) = (V R μ).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← V_act, hga]
  have hQ : Q R (beta R) = (Q R (beta R)).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← Q_act, hgβ]
  rw [hB, hV, hQ, ← map_commutator,
    relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective, commutator_comm]
  exact hi


/-- The literal denominator Y is fixed by the first intrinsic core. -/
theorem fixedPreimage_le_first_core_fixed (common : CommonFacts R source geometry)
    (s : CriticalSegment geometry) (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (hf : Seed.Compatible f s) :
    d.subspace (Sections.fixedPreimage s.middle) ≤
      Representation.BinaryOffender.fixedSpace d.representation
        ((f.core false).map source.projection) := by
  have hcore : f.core false = R := by
    apply map_injective (embedM_injective R)
    exact hf.first_core.trans (Q_beta R)
  rw [hcore, Sections.fixedPreimage_subspace common d]
  exact inf_le_right

/-- The large-intersection hypothesis makes the second natural section nonzero. -/
theorem intersection_not_le_fixedPreimage (common : CommonFacts R source geometry)
    (s : CriticalSegment geometry) (hs : ¬ s.SmallIntersection)
    (hbc : Adjacent R (beta R) s.middle) :
    ¬ Sections.intersection s.middle ≤ Sections.fixedPreimage s.middle := by
  intro h
  have hKN : Sections.intersection s.middle ≤ normalizer (Z R (alpha R)) :=
    inf_le_left.trans ((geometry.V_local (alpha R) rfl common.large_distance).trans
      (Z_normalized R _))
  have hcomm := commutator_commutatorPreimage_le (Sections.intersection s.middle)
    (Q R (beta R)) (Z R (alpha R)) hKN
  apply hs
  exact (commutator_mono h ((Flags.V_le_Q geometry common.large_distance _ s.middle_color).trans
    (Q_le_adjacent_h R rfl (adjacent_symm R hbc)))).trans hcomm

/-- The second section is nonzero in every supplied literal radius module. -/
theorem intersection_subspace_not_le_fixedPreimage (common : CommonFacts R source geometry)
    (s : CriticalSegment geometry) (hs : ¬ s.SmallIntersection)
    (hbc : Adjacent R (beta R) s.middle) (d : LayerModule source (V R (alpha R))) :
    ¬ d.subspace (Sections.intersection s.middle) ≤
      d.subspace (Sections.fixedPreimage s.middle) := by
  intro h
  apply intersection_not_le_fixedPreimage common s hs hbc
  intro x hx
  let v : V R (alpha R) := ⟨x, hx.1⟩
  exact (d.projection_mem_subspace_iff _
    (Sections.Z_le_fixedPreimage common s.first_distance) v).mp
      (h ((d.mem_subspace_iff _ _).mpr ⟨v, hx, rfl⟩))


/-- The actual starred quotient has edge-core displacement of binary rank at most two. -/
theorem star_edge_movedSpace_finrank_le_two
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (μ : Vertex R) (hν : nu R geometry (alpha R) μ)
    (hμ : Adjacent R (beta R) μ)
    (hdisp : (B R μ (geometry.Z_normal μ)).relIndex ⁅V R (alpha R), V R μ⁆ ≤ 4)
    (d : LayerModule source (VStar R geometry (alpha R) (beta R))) :
    Module.finrank (ZMod 2) (Seed.movedSpace d.representation (R.map source.projection) ⊤) ≤ 2 := by
  let S := VStar R geometry (alpha R) (beta R)
  let D := ⁅S, Q R (beta R)⁆
  have hE : Q R (beta R) ≤ stabilizer R (alpha R) :=
    fun _ hx => hx.2 _ (adjacent_symm R (base_adjacent R))
  have hN : Q R (beta R) ≤ normalizer S :=
    hE.trans (Flags.star_normalized geometry _ _)
  have hDS : D ≤ S := le_normalizer_iff_commutator_le_left.mp hN
  have hDF : D ≤ ⁅V R (alpha R), Q R (beta R)⁆ :=
    commutator_mono (Flags.star_le_radius geometry _ _) le_rfl
  have hFV : ⁅V R (alpha R), Q R (beta R)⁆ ≤ V R (alpha R) :=
    le_normalizer_iff_commutator_le_left.mp
      (hE.trans (DistanceEight.V_normalized R (alpha R)))
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite (⁅V R (alpha R), Q R (beta R)⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion (hFV.trans
      (geometry.V_local (alpha R) rfl common.large_distance))) (inclusion_injective _)
  have hi := (relIndex_le_of_le_right hDF
    (show (B R (alpha R) (geometry.Z_normal (alpha R))).relIndex
      ⁅V R (alpha R), Q R (beta R)⁆ ≠ 0 from Subgroup.index_ne_zero_of_finite)).trans
        (edge_bound_of_neighbor_bound common radius hb μ hν hμ hdisp)
  have hDB : D ⊓ B R (alpha R) (geometry.Z_normal (alpha R)) = D ⊓ Z R (alpha R) := by
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1, (radius.star_intersection (alpha R) (beta R) rfl (base_adjacent R)).le
        ⟨hDS hx.1, hx.2⟩⟩
    · exact inf_le_inf_left _ (Flags.Z_le_B geometry (alpha R)
        (geometry.V_local (alpha R) rfl common.large_distance))
  have hindex : (Z R (alpha R)).relIndex D ≤ 4 := by
    rw [← inf_relIndex_left D, ← hDB, inf_relIndex_left]
    exact hi
  have hpre : d.preimage ⊤ = S := by
    apply le_antisymm (d.preimage_le _)
    intro x hx
    exact (d.mem_preimage_iff _ _).mpr ⟨hx, Submodule.mem_top⟩
  have hm := d.subspace_commutator_preimage ⊤ R (by rwa [← Q_beta R])
  rw [hpre, ← Q_beta R] at hm
  have hp := d.subspace_relIndex D hDS
  rw [hp, hm] at hindex
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hindex

open Representation Representation.BinaryOffender

private theorem cubic_fixed_zero {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) BinarySL2Residual.C W)
    (hρ : ρ.invariants = ⊥) (c : BinarySL2Residual.C) (hc : c ≠ 1)
    (w : W) (hw : ρ c w = w) : w = 0 := by
  have hg : ∀ x : BinarySL2Residual.C, x ∈ zpowers c :=
    fun _ => mem_zpowers_of_prime_card Sections.sl2_twoResidual_card hc
  have h := (Representation.mem_invariants_iff_of_forall_mem_zpowers ρ c hg w).mpr hw
  rwa [hρ, Submodule.mem_bot] at h

private theorem quotient_Y_finrank_ge_four
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry) (hs : ¬ s.SmallIntersection)
    (hbc : Adjacent R (beta R) s.middle) (d : LayerModule source (V R (alpha R)))
    (k : Sections.Frame source) :
    4 ≤ Module.finrank (ZMod 2) (d.Space ⧸ d.subspace (Sections.fixedPreimage s.middle)) := by
  let K := d.subspace (Sections.intersection s.middle)
  let Y := d.subspace (Sections.fixedPreimage s.middle)
  have hYK : Y ≤ K := d.subspace_mono (commutatorPreimage_le _ _ _)
  obtain ⟨e, he⟩ := Sections.exists_first_natural common radius k hb s hbc d
  have h1 : Module.finrank (ZMod 2) (d.Space ⧸ K) = 2 := by
    simpa using e.finrank_eq
  obtain ⟨n, e₂, φ, honto, hker, hcoords, hact⟩ :=
    Sections.exists_second_natural common radius k hb s hbc d
  have hn : n ≠ 0 := by
    intro hn
    subst n
    apply intersection_subspace_not_le_fixedPreimage common s hs hbc d
    intro v hv
    have hz : (Y.comap K.subtype).mkQ ⟨v, hv⟩ = 0 := by
      apply e₂.injective
      exact Subsingleton.elim _ _
    exact (Submodule.Quotient.mk_eq_zero (Y.comap K.subtype)).mp hz
  have h2 : Module.finrank (ZMod 2) (K ⧸ Y.comap K.subtype) = n * 2 := by
    simpa [Module.finrank_pi_fintype] using e₂.finrank_eq
  have h3 := K.finrank_quotient_add_finrank
  have h4 := (Y.comap K.subtype).finrank_quotient_add_finrank
  have h5 := Y.finrank_quotient_add_finrank
  have h6 := (Submodule.comapSubtypeEquivOfLe hYK).finrank_eq
  change 4 ≤ Module.finrank (ZMod 2) (d.Space ⧸ Y)
  omega

/-- The two genuine natural sections supply the same cubic with its
displacement, fixed-kernel containment, and source codimension bound. -/
theorem exists_first_cubic_displacement_and_fixed_kernel
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry) (hs : ¬ s.SmallIntersection)
    (hbc : Adjacent R (beta R) s.middle) (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (hf : Seed.Compatible f s) :
    ∃ c ∈ (f.parabolic false).map source.projection, orderOf c = 3 ∧
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (d.representation c - LinearMap.id)) ∧
      LinearMap.ker (d.representation c - LinearMap.id) ≤
        d.subspace (Sections.fixedPreimage s.middle) ∧
      4 ≤ Module.finrank (ZMod 2)
        (d.Space ⧸ d.subspace (Sections.fixedPreimage s.middle)) := by
  classical
  obtain ⟨k⟩ := Sections.exists_frame common radius hb
  obtain ⟨T, hT, hTmap⟩ := Sections.exists_marked_cubic source k
  have hCcard : Nat.card BinarySL2Residual.C = 3 := Sections.sl2_twoResidual_card
  let : Nontrivial BinarySL2Residual.C := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨c₀, hc₀⟩ := exists_ne (1 : BinarySL2Residual.C)
  obtain ⟨g, hgT, hgc⟩ := show c₀ ∈ T.map (Sections.markedResidualProjection source k) by
    rw [hTmap]; trivial
  let m := (Sections.residualEquiv source k.orientation).symm g
  let c := source.projection m
  have hpowg : g ^ 3 = 1 := by
    have hpow := pow_card_eq_one' (x := (⟨g, hgT⟩ : T))
    rw [hT] at hpow
    exact congrArg Subtype.val hpow
  have hpow : c ^ 3 = 1 := by
    change (source.projection ((Sections.residualEquiv source k.orientation).symm g)) ^ 3 = 1
    have hm : m ^ 3 = 1 := by
      dsimp [m]; rw [← map_pow, hpowg, map_one]
    exact (map_pow source.projection (m : M) 3).symm.trans
      (congrArg source.projection (congrArg Subtype.val hm) |>.trans (map_one _))
  have hker : LinearMap.ker (d.representation c - LinearMap.id) ≤
      d.subspace (Sections.fixedPreimage s.middle) := by
    intro v hv
    have hvfix : d.representation c v = v := sub_eq_zero.mp hv
    let K := d.subspace (Sections.intersection s.middle)
    let Y := d.subspace (Sections.fixedPreimage s.middle)
    have hfirst : Sections.firstCRepresentation common radius k hb s hbc d c₀ (K.mkQ v) =
        K.mkQ v := by
      rw [← hgc, Sections.firstCRepresentation_apply]
      change K.mkQ (d.representation c v) = K.mkQ v
      rw [hvfix]
    have hvK : v ∈ K := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      exact cubic_fixed_zero _
        (Sections.firstCRepresentation_invariants_eq_bot common radius k hb s hbc d)
        c₀ hc₀ _ hfirst
    have hsecond : Sections.secondCRepresentation common radius k hb s hbc d c₀
        ((Y.comap K.subtype).mkQ ⟨v, hvK⟩) = (Y.comap K.subtype).mkQ ⟨v, hvK⟩ := by
      rw [← hgc, Sections.secondCRepresentation_apply]
      change (Y.comap K.subtype).mkQ ⟨d.representation c v, _⟩ =
        (Y.comap K.subtype).mkQ ⟨v, hvK⟩
      congr 1
      exact Subtype.ext hvfix
    exact (Submodule.Quotient.mk_eq_zero (Y.comap K.subtype)).mp (cubic_fixed_zero _
      (Sections.secondCRepresentation_invariants_eq_bot common radius k hb s hbc d)
      c₀ hc₀ _ hsecond)
  have hrank : 4 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (d.representation c - LinearMap.id)) := by
    have h1 := Submodule.finrank_mono hker
    have h2 := (d.representation c - LinearMap.id).finrank_range_add_finrank_ker
    have h3 := (d.subspace (Sections.fixedPreimage s.middle)).finrank_quotient_add_finrank
    have h4 := quotient_Y_finrank_ge_four common radius hb s hs hbc d k
    omega
  refine ⟨c, ?_, ?_, hrank, hker,
    quotient_Y_finrank_ge_four common radius hb s hs hbc d k⟩
  · apply mem_map_of_mem
    rw [f.first_parabolic_eq_flag s hf k.orientation k.edge_kernel]
    exact map_subtype_le _ m.property
  · rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp (orderOf_dvd_of_pow_eq_one hpow) with h | h
    · have hc : c = 1 := orderOf_eq_one_iff.mp h
      rw [hc, map_one] at hrank
      have hz : (1 : Module.End (ZMod 2) d.Space) - LinearMap.id = 0 := sub_self _
      rw [hz, LinearMap.range_zero, finrank_bot] at hrank
      omega
    · exact h

/-- The two genuine natural sections supply a cubic moving at least four dimensions. -/
theorem exists_first_cubic_displacement
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry) (hs : ¬ s.SmallIntersection)
    (hbc : Adjacent R (beta R) s.middle) (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (hf : Seed.Compatible f s) :
    ∃ c ∈ (f.parabolic false).map source.projection, orderOf c = 3 ∧
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (d.representation c - LinearMap.id)) := by
  obtain ⟨c, hc, ho, hrank, _, _⟩ :=
    exists_first_cubic_displacement_and_fixed_kernel common radius hb s hs hbc d f hf
  exact ⟨c, hc, ho, hrank⟩

/-- The literal starred subspace with the restriction of the original action. -/
private noncomputable def fixStarRepresentation (d : LayerModule source (V R (alpha R))) :
    Subrepresentation d.representation where
  toSubmodule := d.subspace (VStar R geometry (alpha R) (beta R))
  apply_mem_toSubmodule g v hv := d.subspace_invariant _
    (DistanceEight.V_normalized R _) (Flags.star_normalized geometry _ _) g v hv

/-- Restrict the supplied quotient map, retaining its exact relative kernel. -/
private noncomputable def fixStarLayer (d : LayerModule source (V R (alpha R))) :
    LayerModule source (VStar R geometry (alpha R) (beta R)) where
  Space := d.subspace (VStar R geometry (alpha R) (beta R))
  representation := (fixStarRepresentation (geometry := geometry) d).toRepresentation
  projection := {
    toFun := fun x => Multiplicative.ofAdd ⟨(d.projection
      ⟨x, Flags.star_le_radius geometry _ _ x.property⟩).toAdd,
        (d.mem_subspace_iff _ _).mpr ⟨_, x.property, rfl⟩⟩
    map_one' := by
      apply Subtype.ext
      exact d.projection.map_one
    map_mul' := by
      intro x y
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd (d.projection.map_mul
        ⟨x, Flags.star_le_radius geometry _ _ x.property⟩
        ⟨y, Flags.star_le_radius geometry _ _ y.property⟩) }
  onto := by
    intro v
    obtain ⟨x, hx, he⟩ := (d.mem_subspace_iff _ _).mp v.toAdd.property
    refine ⟨⟨x, hx⟩, ?_⟩
    exact Subtype.ext he
  kernel := by
    ext x
    change (⟨(d.projection
      ⟨x, Flags.star_le_radius geometry _ _ x.property⟩).toAdd, _⟩ :
        d.subspace (VStar R geometry (alpha R) (beta R))) = 0 ↔ _
    rw [Subtype.ext_iff]
    change (⟨x, Flags.star_le_radius geometry _ _ x.property⟩ : V R (alpha R)) ∈
      d.projection.ker ↔ _
    rw [d.kernel]
    rfl
  action := by
    intro m x y hy
    apply Subtype.ext
    exact d.action m ⟨x, Flags.star_le_radius geometry _ _ x.property⟩
      ⟨y, Flags.star_le_radius geometry _ _ y.property⟩ hy

private theorem B_fixed_by_stabilizer (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) :
    ⁅B R (alpha R) (geometry.Z_normal (alpha R)), stabilizer R (alpha R)⁆ ≤
      Z R (alpha R) := by
  let C := commutatorPreimage (stabilizer R (alpha R))
    (B R (alpha R) (geometry.Z_normal (alpha R))) (Z R (alpha R))
  have hL : Ltilde R (alpha R) ≤ C := by
    apply le_commutatorPreimage (map_subtype_le _)
    rw [commutator_comm]
    exact Flags.B_commutator_le_Z geometry _
      (geometry.V_local (alpha R) rfl common.large_distance)
  have hQ : Q R (alpha R) ≤ C := by
    apply le_commutatorPreimage (show Q R (alpha R) ≤ stabilizer R (alpha R) from fun _ hx => hx.1)
    rw [commutator_comm]
    exact (commutator_mono (Early.B_le_radius common _ rfl) le_rfl).trans
      (radius.commutator_le_Z _ rfl)
  have hS : stabilizer R (alpha R) ≤ C := by
    rw [← source.local_generation (alpha R) rfl]
    exact sup_le hL hQ
  rw [commutator_comm]
  exact (commutator_mono hS le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (Z_normalized R _))

/-- The radius-center image in V_alpha/Z_alpha is fixed by the actual full quotient action. -/
theorem radius_B_fixed (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (d : LayerModule source (V R (alpha R)))
    (b : d.Space) (hb : b ∈ d.subspace (B R (alpha R) (geometry.Z_normal _)))
    (g : SL) : d.representation g b = b := by
  obtain ⟨x, hx, rfl⟩ := (d.mem_subspace_iff _ _).mp hb
  obtain ⟨m, rfl⟩ := source.projection_surjective g
  have hm : embedM R m ∈ stabilizer R (alpha R) := by
    rw [alpha, stabilizer_m_base]; exact ⟨m, rfl⟩
  apply (d.fixed_iff_commutator_mem m (DistanceEight.V_normalized R _ hm) x).mpr
  have h := B_fixed_by_stabilizer common radius
  rw [commutator_comm] at h
  exact h (commutator_mem_commutator hm hx)

/-- Every vector of the literal radius quotient is a sum of a fixed center
vector and a vector in its starred submodule. -/
theorem radius_split (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (d : LayerModule source (V R (alpha R)))
    (v : d.Space) :
    ∃ b ∈ d.subspace (B R (alpha R) (geometry.Z_normal _)),
      ∃ w ∈ d.subspace (VStar R geometry (alpha R) (beta R)), b + w = v := by
  let B₀ := B R (alpha R) (geometry.Z_normal _)
  let S := VStar R geometry (alpha R) (beta R)
  let D := d.subspace B₀ ⊔ d.subspace S
  have hB : B₀ ≤ d.preimage D := by
    intro x hx
    exact (d.mem_preimage_iff D x).mpr ⟨Early.B_le_radius common _ rfl hx,
      Submodule.mem_sup_left ((d.mem_subspace_iff B₀ _).mpr ⟨_, hx, rfl⟩)⟩
  have hS : S ≤ d.preimage D := by
    intro x hx
    exact (d.mem_preimage_iff D x).mpr ⟨Flags.star_le_radius geometry _ _ hx,
      Submodule.mem_sup_right ((d.mem_subspace_iff S _).mpr ⟨_, hx, rfl⟩)⟩
  have hV : V R (alpha R) ≤ d.preimage D := by
    exact (Flags.radius_eq_B_sup_star geometry radius.toEarlyFacts common.large_distance
      (alpha R) (beta R) rfl (base_adjacent R)).le.trans (sup_le hB hS)
  obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd v)
  have hmem := ((d.mem_preimage_iff D x).mp (hV x.property)).2
  rw [hx] at hmem
  exact Submodule.mem_sup.mp hmem

private theorem cubic_rank_le_star_rank (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (d : LayerModule source (V R (alpha R))) (c : SL) :
    Module.finrank (ZMod 2) (LinearMap.range (d.representation c - LinearMap.id)) ≤
      Module.finrank (ZMod 2) (LinearMap.range
        ((fixStarLayer (geometry := geometry) d).representation c - LinearMap.id)) := by
  let S := d.subspace (VStar R geometry (alpha R) (beta R))
  let σ : Representation (ZMod 2) SL S :=
    (fixStarLayer (geometry := geometry) d).representation
  have hD : LinearMap.range (d.representation c - LinearMap.id) ≤
      (LinearMap.range (σ c - LinearMap.id)).map S.subtype := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨b, hb, w, hw, hv⟩ := radius_split common radius d v
    refine ⟨(σ c - LinearMap.id : Module.End (ZMod 2) S) ⟨w, hw⟩,
      ⟨⟨w, hw⟩, rfl⟩, ?_⟩
    change d.representation c w - w = d.representation c v - v
    rw [← hv, map_add, radius_B_fixed common radius d b hb c]
    abel
  exact (Submodule.finrank_mono hD).trans (Submodule.finrank_map_le _ _)


/-- The neighbor budget and the two natural sections promote core fixation
on the literal radius quotient to fixation by the full first actor. -/
theorem first_core_fixed_le_first_actor_fixed_of_neighbor_bound
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry) (hs : ¬ s.SmallIntersection)
    (hbc : Adjacent R (beta R) s.middle) (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (hf : Seed.Compatible f s)
    (μ : Vertex R) (hν : nu R geometry (alpha R) μ)
    (hμ : Adjacent R (beta R) μ)
    (hdisp : (B R μ (geometry.Z_normal μ)).relIndex ⁅V R (alpha R), V R μ⁆ ≤ 4) :
    fixedSpace d.representation ((f.core false).map source.projection) ≤
      fixedSpace d.representation ((f.actor false).map source.projection) := by
  let e := fixStarLayer (geometry := geometry) d
  have hR : f.core false = R := by
    apply map_injective (embedM_injective R)
    exact hf.first_core.trans (Q_beta R)
  obtain ⟨c, hc, ho, hrank⟩ :=
    exists_first_cubic_displacement common radius hb s hs hbc d f hf
  have hcore : Module.finrank (ZMod 2)
      (Seed.movedSpace e.representation ((f.core false).map source.projection) ⊤) ≤ 2 := by
    rw [hR]
    exact star_edge_movedSpace_finrank_le_two common radius hb μ hν hμ hdisp e
  have hstar := ParabolicLinear.frame_fixedSpace_core_le_parabolic e.representation
    f false c hc ho hcore (hrank.trans (cubic_rank_le_star_rank common radius d c))
  rw [f.actor_eq false]
  intro v hv
  obtain ⟨b, hb, w, hw, hvw⟩ := radius_split common radius d v
  have hwcore : (⟨w, hw⟩ : e.Space) ∈
      fixedSpace e.representation ((f.core false).map source.projection) := by
    intro a
    apply Subtype.ext
    change d.representation a w = w
    have hh : d.representation a v = v := hv a
    rw [← hvw, map_add, radius_B_fixed common radius d b hb a] at hh
    exact add_left_cancel hh
  intro a
  have hwfix : d.representation a w = w := congrArg Subtype.val ((hstar hwcore) a)
  change d.representation a v = v
  rw [← hvw, map_add, radius_B_fixed common radius d b hb a, hwfix]

set_option linter.unusedVariables false in
/-- The fixation line in MS93 (4.6.12)(4), p.911, with the moving neighbor
and its displacement bound left explicit for the parent source assembly. -/
theorem fixedPreimage_le_first_actor_fixed_of_neighbor_bound
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry) (hs : ¬ s.SmallIntersection)
    (hbc : Adjacent R (beta R) s.middle) (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (hf : Seed.Compatible f s)
    (hcontained : d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle)
    (hspan : orbitSpan s.middle ≤ Q R s.middle)
    (hquot : Nonempty (SpanQuotient source common s.middle))
    (hmoved : Seed.movedSpace d.representation ((f.residual true).map source.projection)
      (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ d.subspace (orbitSpan s.middle))
    (μ : Vertex R) (hν : nu R geometry (alpha R) μ)
    (hμ : Adjacent R (beta R) μ) (hnonzero : ⁅Z R μ, orbitSpan s.middle⁆ ≠ ⊥)
    (hdisp : (B R μ (geometry.Z_normal μ)).relIndex ⁅V R (alpha R), V R μ⁆ ≤ 4) :
    d.subspace (Sections.fixedPreimage s.middle) ≤
      fixedSpace d.representation ((f.actor false).map source.projection) := by
  exact (fixedPreimage_le_first_core_fixed common s d f hf).trans
    (first_core_fixed_le_first_actor_fixed_of_neighbor_bound
      common radius hb s hs hbc d f hf μ hν hμ hdisp)


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape
