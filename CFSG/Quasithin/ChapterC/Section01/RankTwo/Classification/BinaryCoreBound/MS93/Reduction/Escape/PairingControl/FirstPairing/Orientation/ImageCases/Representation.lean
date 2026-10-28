module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.ImageCases.Estimates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.ImageCases.Representation.Kernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.ImageCases.Representation.Selection

/-!
# The representation argument in the order-two image branch

The commutator-kernel dichotomy is transported inside each finite vertex
stabilizer. Faithfulness of the actual natural action shows that
R₀ = [V_a,Z_a'] is outside B_a. Since R₀ centralizes V_c ∩ Q_a when b ≥ 6,
the dichotomy forces the entire V_a to centralize this intersection modulo
D_a. At c, a nonzero commutator row preserves the intersection quotient's
index, giving the required image lower bound four.

The selection argument at the end of printed p.883 supplies a moving neighbor
d with [Z_d,V_c] not contained in D_c. The final theorem combines this witness
with the representation argument, proving both small-image estimates from
the earlier source inputs without an additional nonzero-row premise.
No later escape conclusion or ambient normality in the amalgam is used.
Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(2), pp.883--884.
-/

public section

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.ImageCases
open QuotientApplication.NaturalGeneration

open Stellmacher.PushingUp.AmalgamGraph
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : MS93.Geometry R}

private theorem local_generation_eq_top (source : LocalSource L R)
    {a : Vertex R} (ha : color R a = false) :
    pResidual 2 (stabilizer R a) ⊔ (Q R a).subgroupOf (stabilizer R a) = ⊤ := by
  apply Subgroup.map_injective (f := (stabilizer R a).subtype)
    (stabilizer R a).subtype_injective
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le
    (show Q R a ≤ stabilizer R a from fun _ hx => hx.1)]
  change Ltilde R a ⊔ Q R a = (⊤ : Subgroup (stabilizer R a)).map _
  rw [source.local_generation a ha, ← MonoidHom.range_eq_map, range_subtype]

omit [Finite M] in
private theorem local_fixed_preimage (a : Vertex R) :
    letI := geometry.Z_normal a
    (B R a (geometry.Z_normal a)).subgroupOf (stabilizer R a) =
      centralizerModulo ((V R a).subgroupOf (stabilizer R a))
        (pResidual 2 (stabilizer R a)) ((Z R a).subgroupOf (stabilizer R a)) := by
  let := geometry.Z_normal a
  change Subgroup.comap (stabilizer R a).subtype
    (Subgroup.map (stabilizer R a).subtype _) = _
  exact comap_map_eq_self_of_injective (stabilizer R a).subtype_injective _

omit [Finite M] in
private theorem local_fixed_normal (a : Vertex R) :
    ((fixedCore R a).subgroupOf (stabilizer R a)).Normal :=
  normal_subgroupOf_of_le_normalizer (fixedCore_normalized a)

/-- The full natural coordinates are on V/B, with B the literal source preimage. -/
noncomputable def natural_coordinates_at (source : LocalSource L R)
    (hb : 2 < geometry.b R) {a : Vertex R} (ha : color R a = false)
    (s : NaturalSectionAt a (V R a) (Z R a)) :
    RankOnePairing.NaturalFactor s.projection ⊤
      ((V R a).subgroupOf (stabilizer R a))
      ((B R a (geometry.Z_normal a)).subgroupOf (stabilizer R a)) := by
  let := finite_stabilizer R a
  have hH : IsPGroup 2 ((V R a).subgroupOf (stabilizer R a)) :=
    (source.V_isPGroup geometry hb a ha).comap_subtype
  rw [local_fixed_preimage (geometry := geometry) a]
  exact sectionCoordinates s.module_section (isPPerfect_pResidual 2) hH
      (local_generation_eq_top source ha)

private theorem local_triple_bound (hb : 2 < geometry.b R)
    {a : Vertex R} (ha : color R a = false) (bounds : BoundsAt geometry a) :
    ⁅(V R a).subgroupOf (stabilizer R a),
      ⁅(Q R a).subgroupOf (stabilizer R a), pResidual 2 (stabilizer R a)⁆⁆ ≤
        (fixedCore R a).subgroupOf (stabilizer R a) := by
  let := geometry.Z_normal a
  apply (map_le_iff_le_comap).mp
  rw [map_commutator, map_commutator,
    map_subgroupOf_eq_of_le ((geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)),
    map_subgroupOf_eq_of_le (show Q R a ≤ stabilizer R a from fun _ hx => hx.1)]
  exact bounds.triple

omit [Finite M] in
private theorem local_fixed_bound {a : Vertex R} (bounds : BoundsAt geometry a) :
    letI := geometry.Z_normal a
    ⁅centralizerModulo ((V R a).subgroupOf (stabilizer R a))
        (pResidual 2 (stabilizer R a)) ((Z R a).subgroupOf (stabilizer R a)),
      (Q R a).subgroupOf (stabilizer R a)⁆ ≤
        (fixedCore R a).subgroupOf (stabilizer R a) := by
  let := geometry.Z_normal a
  apply (map_le_iff_le_comap).mp
  rw [map_commutator,
    map_subgroupOf_eq_of_le (show Q R a ≤ stabilizer R a from fun _ hx => hx.1)]
  exact bounds.fixed

/-- A nonzero row at a vertex gives the required index comparison for every
literal subgroup of V, with no extra index or normalization premise. -/
theorem commutator_image_index_at (source : LocalSource L R)
    (hb : 4 < geometry.b R) {a : Vertex R} (ha : color R a = false)
    (s : NaturalSectionAt a (V R a) (Z R a)) (bounds : BoundsAt geometry a)
    (S W : Subgroup (FreeAmalgam R)) (hS : S ≤ Q R a) (hW : W ≤ V R a)
    (hne : ¬ ⁅S, V R a⁆ ≤ fixedCore R a) :
    (B R a (geometry.Z_normal a)).relIndex W ≤
      (fixedCore R a).relIndex ⁅S, W⁆ := by
  let G := stabilizer R a
  let := finite_stabilizer R a
  have hQG : Q R a ≤ G := fun _ hx => hx.1
  have hVG : V R a ≤ G := (geometry.V_le_Q (by omega) a ha).trans hQG
  have hSG : S ≤ G := hS.trans hQG
  have hWG : W ≤ G := hW.trans hVG
  let := local_fixed_normal (R := R) a
  let : IsMulCommutative (V R a) := le_centralizer_iff_isMulCommutative.mp
    (Geometry.V_centralizes_V_of_distance ha ha (by simpa only [SimpleGraph.dist_self, zero_add] using hb))
  have hne' : ¬ ⁅S.subgroupOf G, (V R a).subgroupOf G⁆ ≤
      (fixedCore R a).subgroupOf G := by
    intro hc
    apply hne
    have hh := map_mono (f := G.subtype) hc
    rw [map_commutator, map_subgroupOf_eq_of_le hSG, map_subgroupOf_eq_of_le hVG] at hh
    exact hh.trans (by rw [subgroupOf_map_subtype]; exact inf_le_left)
  have h := natural_commutator_image_index s.module_section (isPPerfect_pResidual 2)
    (source.V_isPGroup geometry (by omega) a ha).comap_subtype
    (local_generation_eq_top source ha) (local_triple_bound (by omega) ha bounds)
    (local_fixed_bound bounds) (S.subgroupOf G) (W.subgroupOf G)
    (fun _ hx => hS hx) (fun _ hx => hW hx) hne'
  rw [← local_fixed_preimage (geometry := geometry)] at h
  have hB := relIndex_map_map_of_injective
    ((B R a (geometry.Z_normal a)).subgroupOf G) (W.subgroupOf G) G.subtype_injective
  have hD := relIndex_map_map_of_injective
    ((fixedCore R a).subgroupOf G) ⁅S.subgroupOf G, W.subgroupOf G⁆ G.subtype_injective
  have hBG : B R a (geometry.Z_normal a) ≤ G := map_subtype_le _
  have hDG : fixedCore R a ≤ G := inf_le_left.trans hQG
  rw [map_subgroupOf_eq_of_le hBG, map_subgroupOf_eq_of_le hWG] at hB
  rw [map_subgroupOf_eq_of_le hDG, map_commutator,
    map_subgroupOf_eq_of_le hSG, map_subgroupOf_eq_of_le hWG] at hD
  exact hB ▸ hD ▸ h

/-- The critical endpoint acts nontrivially on V/B: otherwise faithfulness
of the actual natural coordinates would put Z at that endpoint in Q. -/
theorem radius_not_le_fixed_preimage (source : LocalSource L R)
    (hb : 2 < geometry.b R) (p : Counterexample geometry) (ip : InitialFacts p) :
    ¬ radiusCommutator p.a p.a' ≤ B R p.a (geometry.Z_normal p.a) := by
  intro h
  let G := stabilizer R p.a
  let n := natural_coordinates_at source hb p.color_a ip.natural_section
  have hV : V R p.a ≤ G := (geometry.V_le_Q hb p.a p.color_a).trans (fun _ hx => hx.1)
  have hc : ⁅(Z R p.a').subgroupOf G, (V R p.a).subgroupOf G⁆ ≤
      (B R p.a (geometry.Z_normal p.a)).subgroupOf G := by
    apply (map_le_iff_le_comap).mp
    rw [map_commutator, map_subgroupOf_eq_of_le p.end_Z_le_start_stabilizer,
      map_subgroupOf_eq_of_le hV, commutator_comm]
    exact h
  have hk := natural_actor_le_kernel n ((Z R p.a').subgroupOf G) hc
  rw [ip.natural_section.module_section.projection_kernel] at hk
  apply (source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical).2
  intro x hx
  exact hk (show (⟨x, p.end_Z_le_start_stabilizer hx⟩ : G) ∈ (Z R p.a').subgroupOf G from hx)

/-- The whole starting V centralizes the literal intersection modulo D_a.
The nonfixed witness is R₀, whose centralization follows from b ≥ 6. -/
theorem small_intersection_commutator_le_fixed (source : LocalSource L R)
    (hb : 2 < geometry.b R) (p : Counterexample geometry) (ip : InitialFacts p)
    (bounds : BoundsAt geometry p.a) :
    ⁅V R p.a, V R p.c ⊓ Q R p.a⁆ ≤ fixedCore R p.a := by
  let G := stabilizer R p.a
  let W := V R p.c ⊓ Q R p.a
  let E := radiusCommutator p.a p.a'
  let := finite_stabilizer R p.a
  let := local_fixed_normal (R := R) p.a
  let := geometry.Z_normal p.a
  have hQG : Q R p.a ≤ G := fun _ hx => hx.1
  have hVG : V R p.a ≤ G := (geometry.V_le_Q hb p.a p.color_a).trans hQG
  have hWG : W ≤ G := inf_le_right.trans hQG
  have hEG : E ≤ G := p.radius_le_start.trans hVG
  have hne : ¬ E.subgroupOf G ≤
      centralizerModulo ((V R p.a).subgroupOf G) (pResidual 2 G)
        ((Z R p.a).subgroupOf G) := by
    rw [← local_fixed_preimage (geometry := geometry)]
    intro he
    apply radius_not_le_fixed_preimage source hb p ip
    intro x hx
    exact he (show (⟨x, hEG hx⟩ : G) ∈ E.subgroupOf G from hx)
  have hcomm : ⁅E.subgroupOf G, W.subgroupOf G⁆ ≤ (fixedCore R p.a).subgroupOf G := by
    apply (map_le_iff_le_comap).mp
    rw [map_commutator, map_subgroupOf_eq_of_le hEG, map_subgroupOf_eq_of_le hWG]
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      (radius_centralizes_intersection p ip)).le.trans bot_le
  have hc := natural_commutator_le_of_nonfixed ip.natural_section.module_section
    (isPPerfect_pResidual 2) (source.V_isPGroup geometry hb p.a p.color_a).comap_subtype
    (local_generation_eq_top source p.color_a) (local_triple_bound hb p.color_a bounds)
    (local_fixed_bound bounds) (W.subgroupOf G) (E.subgroupOf G)
    (fun _ hx => hx.2) (fun _ hx => p.radius_le_start hx) hne hcomm
  have hh := map_mono (f := G.subtype) hc
  rw [map_commutator, map_subgroupOf_eq_of_le hVG, map_subgroupOf_eq_of_le hWG] at hh
  exact hh.trans (by rw [subgroupOf_map_subtype]; exact inf_le_left)

/-- The representation step in the small-image branch. The remaining witness
is only a moving Z-layer with a nonzero commutator on V_c modulo D_c; all
quotient-index growth and the whole-V containment are proved here. -/
theorem small_image_estimate_of_nonzero_row (source : LocalSource L R)
    (hb : 2 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (bounds : ∀ a, color R a = false → BoundsAt geometry a)
    (hi : (Q R p.a).relIndex (V R p.c) = 2)
    {d : Vertex R} (hd : d ∈ movingNeighbors geometry p.a)
    (hne : ¬ ⁅Z R d, V R p.c⁆ ≤ fixedCore R p.c) :
    Nonempty (SmallImageEstimate p) := by
  obtain ⟨ip⟩ := initial p
  obtain ⟨q, hqa, _⟩ := contrary_at p bad p.c p.before_color
  obtain ⟨iq⟩ := initial q
  have hs : NaturalSectionAt p.c (V R p.c) (Z R p.c) := by
    simpa only [hqa] using iq.natural_section
  have hindex := commutator_image_index_at source (by have := ip.six_le; omega)
    p.before_color hs (bounds p.c p.before_color) (Z R d) (V R p.c ⊓ Q R p.a)
    ((moving_Z_le_V hd).trans p.trapped) inf_le_left hne
  have hlower := small_intersection_quotient_ge_four source hb initial p bad hi
  have heq : (V R p.c ⊓ B R p.c (geometry.Z_normal p.c)).relIndex (V R p.c ⊓ Q R p.a) =
      (B R p.c (geometry.Z_normal p.c)).relIndex (V R p.c ⊓ Q R p.a) := by
    rw [← inf_relIndex_right (V R p.c ⊓ B R p.c (geometry.Z_normal p.c)),
      ← inf_relIndex_right (B R p.c (geometry.Z_normal p.c))]
    congr 1
    ext x
    simp only [mem_inf]
    tauto
  rw [heq] at hlower
  exact ⟨⟨d, hd, hlower.trans hindex,
    small_intersection_commutator_le_fixed source hb p ip (bounds p.a p.color_a)⟩⟩

/-- The two small-image estimates of MS93 (4.3.2)(2), printed p.884, from the
earlier source inputs. The moving witness is selected using the p.883 argument;
the natural commutator map then transfers the intersection quotient's lower
bound to its literal commutator image. -/
theorem small_image_estimate (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (bounds : ∀ a, color R a = false → BoundsAt geometry a)
    (hi : (Q R p.a).relIndex (V R p.c) = 2) :
    Nonempty (SmallImageEstimate p) := by
  obtain ⟨d, hd, hne⟩ :=
    exists_moving_commutator_not_le_predecessor_fixed source hb modules transfer initial p bad
  exact small_image_estimate_of_nonzero_row source hb initial p bad bounds hi hd hne

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.ImageCases
