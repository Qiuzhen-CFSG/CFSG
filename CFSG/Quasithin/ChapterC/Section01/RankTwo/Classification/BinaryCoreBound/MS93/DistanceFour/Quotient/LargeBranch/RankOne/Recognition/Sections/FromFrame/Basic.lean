module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections.Actions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Displacement.Cardinalities
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.EdgeComparison

/-!
# The marked residual and its first literal section

For a supplied `Sections.Frame`, both literal linear sections carry the
conjugation action of the same embedded source residual. The original local
residual is identified with that embedded subgroup through the given amalgam
map; the actor has not yet been replaced by a matrix quotient.

Commutation by any `x ∈ Z_c \ Z_beta` is a surjective homomorphism from
`V_alpha` to `[Z_c,V_alpha]`, with exact relative kernel `V_alpha ∩ Q_c`.
The frame and the radius-center identity make conjugation change `x` only
by an element of `Z_beta`, which centralizes the radius subgroup. This proves
the actual residual equivariance of the commutator map. The accepted
index-four calculation and edge comparison identify its image with the
natural edge plane. That plane has no nonidentity residual-fixed element,
so the first linear quotient has order four, zero invariant space, and
trivial action by the actual intersection with `Q_beta`.

The marked identification of `H/(H ∩ Q_beta)` with `SL₂(2)'`, and the
supplement and fixed-space argument for the second section, remain separate
proof obligations. No existence of a frame or complete version of (4.6.12)
is asserted here. Finiteness is used inside the local stabilizers only.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.12)(1)--(2), printed p.910, using (4.6.9), printed p.908,
and the marked flag on p.905. The index-two commutator-column construction
extends the private proof in `Consequences.Displacement.Cardinalities.Reduction`.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Sections
open Flags.RankOne
/-- An index-two centralizing subgroup makes one commutator column the whole image. -/
private theorem central_index_two_map {G : Type*} [Group G]
    (V A C : Subgroup G) (hcentral : C ≤ centralizer (V : Set G))
    (hindex : C.relIndex A = 2) (hcommV : ⁅V, A⁆ ≤ V)
    (hcomm : ⁅V, A⁆ ≤ centralizer (V : Set G))
    (x : G) (hx : x ∈ A) (hxC : x ∉ C) :
    ∃ φ : V →* (⁅A, V⁆ : Subgroup G), Function.Surjective φ ∧
      φ.ker = (centralizer (A : Set G)).subgroupOf V ∧
      ∀ v, (φ v : G) = ⁅(v : G), x⁆ := by
  have hvalue (v : G) (hv : v ∈ V) : ⁅v, x⁆ ∈ ⁅V, A⁆ :=
    commutator_mem_commutator hv hx
  let φ : V →* (⁅A, V⁆ : Subgroup G) := {
    toFun v := ⟨⁅(v : G), x⁆, by rw [commutator_comm]; exact hvalue v v.property⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' v w := by
      apply Subtype.ext
      change ⁅(v : G) * (w : G), x⁆ = ⁅(v : G), x⁆ * ⁅(w : G), x⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hvw : (v : G) * ⁅(w : G), x⁆ = ⁅(w : G), x⁆ * v :=
        hcomm (hvalue w w.property) v v.property
      have hcc : ⁅(w : G), x⁆ * ⁅(v : G), x⁆ =
          ⁅(v : G), x⁆ * ⁅(w : G), x⁆ :=
        hcomm (hvalue v v.property) _ (hcommV (hvalue w w.property))
      rw [hvw, mul_inv_cancel_right, hcc] }
  have hsame (v : G) (hv : v ∈ V) (a : G) (ha : a ∈ A) (haC : a ∉ C) :
      ⁅v, a⁆ = ⁅v, x⁆ := by
    have hfactor : x⁻¹ * a ∈ C :=
      (C.subgroupOf A).mul_mem_iff_of_index_two hindex
        (a := ⟨x⁻¹, A.inv_mem hx⟩) (b := ⟨a, ha⟩) |>.mpr (by
          simp only [mem_subgroupOf, inv_mem_iff, hxC, haC])
    have hzero : ⁅v, x⁻¹ * a⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hcentral hfactor v hv)
    have hh := commutatorElement_mul_right_eq_mul_conj v x (x⁻¹ * a)
    simpa only [mul_inv_cancel_left, hzero, mul_one, mul_inv_cancel_right,
      mul_inv_cancel, mul_one] using hh
  refine ⟨φ, ?_, ?_, fun _ => rfl⟩
  · have hrange : ((⁅A, V⁆).subtype.comp φ).range = ⁅V, A⁆ := by
      apply le_antisymm
      · rintro _ ⟨v, rfl⟩
        exact hvalue v v.property
      · apply commutator_le.mpr
        intro v hv a ha
        by_cases haC : a ∈ C
        · have hone : ⁅v, a⁆ = 1 :=
            commutatorElement_eq_one_iff_mul_comm.mpr (hcentral haC v hv)
          rw [hone]
          exact (((⁅A, V⁆).subtype.comp φ).range).one_mem
        exact ⟨⟨v, hv⟩, (hsame v hv a ha haC).symm⟩
    intro y
    have hy : (y : G) ∈ ((⁅A, V⁆).subtype.comp φ).range := by
      rw [hrange, commutator_comm]
      exact y.property
    obtain ⟨v, hv⟩ := hy
    exact ⟨v, Subtype.ext hv⟩
  · ext v
    change φ v = 1 ↔ (v : G) ∈ centralizer (A : Set G)
    rw [Subtype.ext_iff]
    change ⁅(v : G), x⁆ = 1 ↔ (v : G) ∈ centralizer (A : Set G)
    constructor
    · intro hv a ha
      apply Eq.symm
      apply commutatorElement_eq_one_iff_mul_comm.mp
      by_cases haC : a ∈ C
      · exact commutatorElement_eq_one_iff_mul_comm.mpr (hcentral haC v v.property)
      · exact (hsame v v.property a ha haC).trans hv
    · intro hv
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hv x hx).symm

variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The frame supplies exactly the earlier flag hypotheses, with the same orientation. -/
theorem Frame.flagControl (f : Frame source) : FlagControl source :=
  ⟨f.orientation, f.edge_kernel, f.triple⟩

/-- Identify the original local residual with its image under the fixed amalgam embedding. -/
noncomputable def residualEquiv (source : LocalSource L R) (i : Bool) :
    rankOne (parabolic source.projection source.flag i) ≃* flagResidual source i :=
  Subgroup.equivMapOfInjective _ (embedM R) (embedM_injective R)

/-- The inverse actor comparison retains the actual ambient element. -/
theorem residualEquiv_symm_apply (source : LocalSource L R) (i : Bool)
    (g : flagResidual source i) :
    embedM R ((residualEquiv source i).symm g) = (g : FreeAmalgam R) := by
  change ((residualEquiv source i) ((residualEquiv source i).symm g) : FreeAmalgam R) = _
  rw [MulEquiv.apply_symm_apply]

variable [Finite M] (common : CommonFacts R source geometry)
  (radius : RadiusFacts R geometry) (f : Frame source)
  (hb : geometry.b R = 4) (s : CriticalSegment geometry)
  (hbc : Adjacent R (beta R) s.middle)

omit [Finite M] in
/-- Both section actions use the very same original local residual. -/
private theorem local_residual_normalizes_radius :
    (rankOne (parabolic source.projection source.flag f.orientation)).map (embedM R) ≤
      normalizer (V R (alpha R)) :=
  (flagResidual_le source f.orientation).trans
    ((flagParabolic_le source f.orientation).trans (DistanceEight.V_normalized R _))

/-- The literal first linear quotient carries ambient conjugation by H. -/
noncomputable def firstRepresentation (d : LayerModule source (V R (alpha R))) :
    Representation (ZMod 2) (flagResidual source f.orientation)
      (d.Space ⧸ d.subspace (intersection s.middle)) :=
  (d.quotientRepresentation (rankOne (parabolic source.projection source.flag f.orientation))
    (intersection s.middle) (by exact local_residual_normalizes_radius f)
    (residual_normalizes_intersection common radius f s.first_distance hbc)).comp
      (residualEquiv source f.orientation).symm.toMonoidHom

/-- The literal second linear quotient carries ambient conjugation by the same H. -/
noncomputable def secondRepresentation (d : LayerModule source (V R (alpha R))) :
    Representation (ZMod 2) (flagResidual source f.orientation)
      ((d.subspace (intersection s.middle)) ⧸
        (d.subspace (fixedPreimage s.middle)).comap (d.subspace (intersection s.middle)).subtype) :=
  (d.sectionRepresentation (rankOne (parabolic source.projection source.flag f.orientation))
    (intersection s.middle) (fixedPreimage s.middle) (by exact local_residual_normalizes_radius f)
    (residual_normalizes_intersection common radius f s.first_distance hbc)
    (residual_normalizes_fixedPreimage common radius f s.first_distance hbc)).comp
      (residualEquiv source f.orientation).symm.toMonoidHom

/-- The first quotient representation satisfies the original ambient conjugation formula. -/
theorem firstRepresentation_action (d : LayerModule source (V R (alpha R)))
    (g : flagResidual source f.orientation) (v w : V R (alpha R))
    (hw : (w : FreeAmalgam R) = g * (v : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹) :
    (d.quotientMap (intersection s.middle) w).toAdd =
      firstRepresentation common radius f s hbc d g (d.quotientMap (intersection s.middle) v).toAdd := by
  apply d.quotientMap_action
  change (w : FreeAmalgam R) = embedM R ((residualEquiv source f.orientation).symm g) *
    (v : FreeAmalgam R) * (embedM R ((residualEquiv source f.orientation).symm g))⁻¹
  rw [residualEquiv_symm_apply]
  exact hw

/-- The second quotient representation satisfies that same ambient conjugation formula. -/
theorem secondRepresentation_action (d : LayerModule source (V R (alpha R)))
    (g : flagResidual source f.orientation) (v w : intersection s.middle)
    (hw : (w : FreeAmalgam R) = g * (v : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹) :
    (d.sectionMap (intersection s.middle) (fixedPreimage s.middle) inf_le_left w).toAdd =
      secondRepresentation common radius f s hbc d g
        (d.sectionMap (intersection s.middle) (fixedPreimage s.middle) inf_le_left v).toAdd := by
  apply d.sectionMap_action
  change (w : FreeAmalgam R) = embedM R ((residualEquiv source f.orientation).symm g) *
    (v : FreeAmalgam R) * (embedM R ((residualEquiv source f.orientation).symm g))⁻¹
  rw [residualEquiv_symm_apply]
  exact hw

include common radius f hb hbc in
/-- The first literal quotient has index four in the radius subgroup. -/
theorem intersection_index_four :
    (intersection s.middle).relIndex (V R (alpha R)) = 4 := by
  have h := (displacement_cardinalities source geometry common hb radius.toEarlyFacts
    f.flagControl s.middle s.first_distance hbc
    (midpoint_displacement_noncentral common radius hb s)).2.2.2
  change ((V R (alpha R) ⊓ Q R s.middle).subgroupOf (V R (alpha R))).index = 4
  rw [inf_subgroupOf_left]
  exact h

include common radius f hb hbc in
/-- The critical midpoint displacement is the original marked natural edge plane. -/
theorem midpoint_displacement_eq_edge :
    ⁅Z R s.middle, V R (alpha R)⁆ = ⁅Z R (alpha R), Q R (beta R)⁆ := by
  have hcard := (displacement_cardinalities source geometry common hb radius.toEarlyFacts
    f.flagControl s.middle s.first_distance hbc
    (midpoint_displacement_noncentral common radius hb s)).1
  have hedge := edgeGeneratorComparison source geometry common hb radius.toEarlyFacts
    f.flagControl (Bzero_eq_B common radius) s.middle (midpoint_nu common radius hb s) hbc
  have hle := (displacement_le_edge geometry common.large_distance s.middle).trans_eq hedge
  have hfour := radius.toEarlyFacts.edge_commutator_card (alpha R) (beta R) rfl (base_adjacent R)
  let : Finite (⁅Z R (alpha R), Q R (beta R)⁆ : Subgroup (FreeAmalgam R)) :=
    Nat.finite_of_card_ne_zero (by rw [hfour]; decide)
  exact eq_of_le_of_card_ge hle (by rw [hcard, hfour])

include common radius f hb hbc in
/-- The midpoint displacement has no nonidentity fixed point for this very residual. -/
theorem midpoint_displacement_fixed_eq_bot :
    ⁅Z R s.middle, V R (alpha R)⁆ ⊓
      centralizer (flagResidual source f.orientation : Set (FreeAmalgam R)) = ⊥ := by
  rw [midpoint_displacement_eq_edge common radius f hb s hbc,
    edge_natural_fixed_plane source geometry common radius.toEarlyFacts
      f.orientation f.edge_kernel]
  apply le_bot_iff.mp
  rw [← U_inf_localCenter_eq_bot common]
  exact le_inf (inf_le_left.trans inf_le_left)
    ((inf_le_inf_right _ inf_le_right).trans
      (edgeFixedLayerAction source geometry common radius.toEarlyFacts
        f.orientation f.edge_kernel).2)

include common radius f hb hbc in
/-- The actual first linear quotient has four elements, for any supplied radius realization. -/
theorem first_quotient_card (d : LayerModule source (V R (alpha R))) :
    Nat.card (d.Space ⧸ d.subspace (intersection s.middle)) = 4 := by
  have h := intersection_index_four common radius f hb s hbc
  rw [d.quotient_relIndex _ (Z_le_intersection common s.first_distance)] at h
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  exact h

include common radius f hbc in
/-- The residual changes a midpoint central generator only by an edge-central element. -/
theorem residual_commutator_le_edge_Z :
    ⁅Z R s.middle, flagResidual source f.orientation⁆ ≤ Z R (beta R) := by
  have hZ : Z R s.middle ≤ V R (beta R) := by
    rw [V_eq_neighborSpan (alpha R) (beta R) rfl (base_adjacent R)]
    exact le_iSup_of_le s.middle (le_iSup_of_le hbc le_rfl)
  exact (commutator_mono hZ le_rfl).trans
    (flag_commutator_le_edge_Z_of_Bzero source geometry common.large_distance
      radius.toEarlyFacts f.orientation f.edge_kernel f.triple (Bzero_eq_B common radius))

include common radius f hbc in
/-- Commutation by any generator outside Z_beta gives an onto map with the literal kernel K. -/
theorem exists_midpoint_commutator_map (x : FreeAmalgam R)
    (hx : x ∈ Z R s.middle) (hxout : x ∉ Z R (beta R)) :
    ∃ φ : V R (alpha R) →* (⁅Z R s.middle, V R (alpha R)⁆ : Subgroup (FreeAmalgam R)),
      Function.Surjective φ ∧ φ.ker = (intersection s.middle).subgroupOf (V R (alpha R)) ∧
      (∀ v, (φ v : FreeAmalgam R) = ⁅(v : FreeAmalgam R), x⁆) ∧
      (∀ (g : flagResidual source f.orientation) (v w : V R (alpha R)),
        (w : FreeAmalgam R) = g * (v : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹ →
        (φ w : FreeAmalgam R) = g * (φ v : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹) := by
  have hVQ := Flags.V_le_Q geometry common.large_distance (alpha R) rfl
  have hZcV : Z R s.middle ≤ V R (alpha R) :=
    le_iSup_of_le s.middle (le_iSup_of_le
      (by rw [SimpleGraph.dist_comm, s.first_distance]) le_rfl)
  have hcentral : Z R (beta R) ≤ centralizer (V R (alpha R) : Set (FreeAmalgam R)) :=
    ((Flags.edge_Z_le (alpha R) (beta R) rfl (base_adjacent R)).trans
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes _ rfl))).trans
      (centralizer_le hVQ)
  have hcomm : ⁅V R (alpha R), Z R s.middle⁆ ≤
      (center (V R (alpha R))).map (V R (alpha R)).subtype :=
    (commutator_mono le_rfl (hZcV.trans hVQ)).trans
      (radius.toEarlyFacts.commutator_central _ rfl)
  have hCV : (center (V R (alpha R))).map (V R (alpha R)).subtype ≤
      centralizer (V R (alpha R) : Set (FreeAmalgam R)) := by
    rintro z ⟨z, hz, rfl⟩ v hv
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨v, hv⟩)
  obtain ⟨φ, honto, hker, hφ⟩ := central_index_two_map (V R (alpha R)) (Z R s.middle)
    (Z R (beta R)) hcentral
    (radius.toEarlyFacts.edge_Z_index s.middle (beta R)
      (distance_two_color rfl s.first_distance) (adjacent_symm R hbc))
    (hcomm.trans (map_subtype_le _)) (hcomm.trans hCV) x hx hxout
  refine ⟨φ, honto, ?_, hφ, ?_⟩
  · rw [hker]
    have he := radius_inf_kernel common rfl s.first_distance
    ext v
    change (v : FreeAmalgam R) ∈ centralizer (Z R s.middle : Set (FreeAmalgam R)) ↔
      (v : FreeAmalgam R) ∈ intersection s.middle
    rw [intersection, he]
    exact (and_iff_right v.property).symm
  · intro g v w hw
    rw [hφ, hφ]
    have hgx : ⁅(g : FreeAmalgam R), x⁆ ∈ Z R (beta R) := by
      apply residual_commutator_le_edge_Z common radius f s hbc
      rw [commutator_comm]
      exact commutator_mem_commutator g.property hx
    have hcw : ⁅(w : FreeAmalgam R), ⁅(g : FreeAmalgam R), x⁆⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hcentral hgx w w.property)
    have hcwV : ⁅(w : FreeAmalgam R), x⁆ ∈ V R (alpha R) :=
      (hcomm.trans (map_subtype_le _)) (commutator_mem_commutator w.property hx)
    have hc : ⁅(g : FreeAmalgam R), x⁆ * ⁅(w : FreeAmalgam R), x⁆ =
        ⁅(w : FreeAmalgam R), x⁆ * ⁅(g : FreeAmalgam R), x⁆ :=
      (hcentral hgx _ hcwV).symm
    have he := map_commutatorElement (MulAut.conj (g : FreeAmalgam R)).toMonoidHom
      (v : FreeAmalgam R) x
    change (g : FreeAmalgam R) * ⁅(v : FreeAmalgam R), x⁆ * (g : FreeAmalgam R)⁻¹ =
      ⁅(g : FreeAmalgam R) * (v : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹,
        (g : FreeAmalgam R) * x * (g : FreeAmalgam R)⁻¹⁆ at he
    rw [← hw, show (g : FreeAmalgam R) * x * (g : FreeAmalgam R)⁻¹ =
      ⁅(g : FreeAmalgam R), x⁆ * x by simp [commutatorElement_def, mul_assoc],
      commutatorElement_mul_right_eq_mul_conj, hcw, one_mul, hc, mul_inv_cancel_right] at he
    exact he.symm

include hb in
/-- The actual edge kernel acts trivially on the first quotient. -/
theorem firstRepresentation_kernel_contains_edge (d : LayerModule source (V R (alpha R))) :
    (Q R (beta R)).subgroupOf (flagResidual source f.orientation) ≤
      (firstRepresentation common radius f s hbc d).ker := by
  obtain ⟨x, hx, hxout⟩ : ∃ x ∈ Z R s.middle, x ∉ Z R (beta R) := by
    by_contra! hle
    have hindex := radius.toEarlyFacts.edge_Z_index s.middle (beta R)
      (distance_two_color rfl s.first_distance) (adjacent_symm R hbc)
    have hone := relIndex_eq_one.mpr hle
    omega
  obtain ⟨φ, _, hker, _, hequiv⟩ :=
    exists_midpoint_commutator_map common radius f s hbc x hx hxout
  have hD : ⁅Z R s.middle, V R (alpha R)⁆ ≤
      centralizer (Q R (beta R) : Set (FreeAmalgam R)) := by
    rw [midpoint_displacement_eq_edge common radius f hb s hbc,
      edge_natural_fixed_plane source geometry common radius.toEarlyFacts
        f.orientation f.edge_kernel,
      Early.edge_Z_eq_fixed common (alpha R) (beta R) rfl (base_adjacent R)]
    exact inf_le_right.trans inf_le_right
  have hqker := d.quotientMap_kernel (intersection s.middle)
    (Z_le_intersection common s.first_distance)
  intro g hg
  apply LinearMap.ext
  intro z
  obtain ⟨v, hv⟩ := d.quotientMap_surjective (intersection s.middle) (Multiplicative.ofAdd z)
  have hn : (g : FreeAmalgam R) ∈ normalizer (V R (alpha R)) :=
    local_residual_normalizes_radius f g.property
  let w : V R (alpha R) := ⟨g * (v : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹,
    (mem_normalizer_iff.mp hn v).mp v.property⟩
  have hφeq : φ w = φ v := by
    apply Subtype.ext
    rw [hequiv g v w rfl, hD (φ v).property g hg, mul_inv_cancel_right]
  have hmem : w * v⁻¹ ∈ (d.quotientMap (intersection s.middle)).ker := by
    rw [hqker, ← hker]
    change φ (w * v⁻¹) = 1
    rw [map_mul, map_inv, hφeq, mul_inv_cancel]
  have hqw : d.quotientMap (intersection s.middle) w = d.quotientMap (intersection s.middle) v := by
    change d.quotientMap (intersection s.middle) (w * v⁻¹) = 1 at hmem
    rwa [map_mul, map_inv, mul_inv_eq_one] at hmem
  have ha := firstRepresentation_action common radius f s hbc d g v w rfl
  rw [hqw, hv] at ha
  exact ha.symm

include hb in
/-- The first quotient has zero invariants for the actual embedded residual,
before replacing that actor by its marked order-three image. -/
theorem firstRepresentation_invariants_eq_bot (d : LayerModule source (V R (alpha R))) :
    Representation.invariants (firstRepresentation common radius f s hbc d) = ⊥ := by
  obtain ⟨x, hx, hxout⟩ : ∃ x ∈ Z R s.middle, x ∉ Z R (beta R) := by
    by_contra! hle
    have hindex := radius.toEarlyFacts.edge_Z_index s.middle (beta R)
      (distance_two_color rfl s.first_distance) (adjacent_symm R hbc)
    have hone := relIndex_eq_one.mpr hle
    omega
  obtain ⟨φ, honto, hker, hφ, hequiv⟩ :=
    exists_midpoint_commutator_map common radius f s hbc x hx hxout
  rw [Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨v, hv⟩ := d.quotientMap_surjective (intersection s.middle) (Multiplicative.ofAdd z)
  have hqker := d.quotientMap_kernel (intersection s.middle)
    (Z_le_intersection common s.first_distance)
  have hfix : (φ v : FreeAmalgam R) ∈
      centralizer (flagResidual source f.orientation : Set (FreeAmalgam R)) := by
    intro g hg
    have hn : g ∈ normalizer (V R (alpha R)) :=
      local_residual_normalizes_radius f hg
    let w : V R (alpha R) := ⟨g * (v : FreeAmalgam R) * g⁻¹,
      (mem_normalizer_iff.mp hn v).mp v.property⟩
    have hqw : d.quotientMap (intersection s.middle) w = d.quotientMap (intersection s.middle) v := by
      apply Multiplicative.toAdd.injective
      rw [firstRepresentation_action common radius f s hbc d ⟨g, hg⟩ v w rfl, hv]
      exact hz ⟨g, hg⟩
    have hquot : w * v⁻¹ ∈ (d.quotientMap (intersection s.middle)).ker := by
      change d.quotientMap (intersection s.middle) (w * v⁻¹) = 1
      rw [map_mul, map_inv, hqw, mul_inv_cancel]
    have hφeq : φ w = φ v := by
      have hmem : w * v⁻¹ ∈ φ.ker := by rwa [hker, ← hqker]
      change φ (w * v⁻¹) = 1 at hmem
      rwa [map_mul, map_inv, mul_inv_eq_one] at hmem
    have he := hequiv ⟨g, hg⟩ v w rfl
    rw [hφeq] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm)
  have hone : (φ v : FreeAmalgam R) = 1 := by
    have hm : (φ v : FreeAmalgam R) ∈
        ⁅Z R s.middle, V R (alpha R)⁆ ⊓
          centralizer (flagResidual source f.orientation : Set (FreeAmalgam R)) :=
      ⟨(φ v).property, hfix⟩
    rwa [midpoint_displacement_fixed_eq_bot common radius f hb s hbc, mem_bot] at hm
  have hmem : v ∈ (d.quotientMap (intersection s.middle)).ker := by
    rw [hqker, ← hker]
    exact show φ v = 1 from Subtype.ext hone
  have hzero : d.quotientMap (intersection s.middle) v = 1 := hmem
  rw [hv] at hzero
  exact congrArg Multiplicative.toAdd hzero

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Sections
