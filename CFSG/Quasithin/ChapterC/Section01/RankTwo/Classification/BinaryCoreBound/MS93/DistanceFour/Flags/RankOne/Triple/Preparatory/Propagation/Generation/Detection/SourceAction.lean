module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Generation.Geometry

/-!
# The source action in commutator detection

Pull the actual midpoint span V₀ and Z_alpha back through embedM to the
finite local group M. Their normality, denominator containment and elementary
quotient are proved here. The source projection kernel acts trivially on this
quotient, while the critical triple rules out a trivial action of all of M.

If a transported escaping layer has its commutator with V₀ ∩ Q_t contained
in Z_alpha, an actual element of that layer pulls back to an involution of M
with nonidentity image under the source projection. Its fixed preimage on
V₀/Z_alpha has relative index at most two. This uses the supplied actor index
and the original subgroup embeddings; it does not require Z_t ≤ V₀.

These are the geometric inputs to the remaining representation recognition:
a nontrivial binary SL₃(2) action with such an involution must have a split
natural moving section. No recognition or SingleSection assertion is made here.

Source: Meierfrankenfeld--Stellmacher (1993), notation on p.881 and
(4.6.8), claim (2), printed p.906.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation.Detection
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

/-- The literal pullback of V₀ to the original local group. -/
noncomputable def sourceSpan (p : FlagCriticalData source geometry i) : Subgroup M :=
  (midpointSpan p).comap (embedM R)

/-- The literal pullback of Z_alpha through the same embedding. -/
noncomputable def sourceDenominator (R : Subgroup M) : Subgroup M :=
  (Z R (alpha R)).comap (embedM R)

/-- The midpoint span is normal in M, not in the free amalgam. -/
theorem sourceSpan_normal (p : FlagCriticalData source geometry i) :
    (sourceSpan p).Normal := by
  constructor
  intro x hx m
  change embedM R (m * x * m⁻¹) ∈ midpointSpan p
  rw [map_mul, map_mul, map_inv]
  apply (mem_normalizer_iff.mp (span_normalized p ?_) _).mp hx
  simpa only [alpha, stabilizer_m_base, Mbar] using
    (show embedM R m ∈ (embedM R).range from ⟨m, rfl⟩)

/-- The denominator is normal in the same finite local group. -/
theorem sourceDenominator_normal (R : Subgroup M) : (sourceDenominator R).Normal := by
  constructor
  intro x hx m
  change embedM R (m * x * m⁻¹) ∈ Z R (alpha R)
  rw [map_mul, map_mul, map_inv]
  apply (mem_normalizer_iff.mp (Z_normalized R (alpha R) ?_) _).mp hx
  simpa only [alpha, stabilizer_m_base, Mbar] using
    (show embedM R m ∈ (embedM R).range from ⟨m, rfl⟩)

/-- The original denominator is contained in the original numerator. -/
theorem sourceDenominator_le_sourceSpan [Finite M]
    (p : FlagCriticalData source geometry i) : sourceDenominator R ≤ sourceSpan p :=
  comap_mono (Z_le_span p)

/-- Mapping back recovers V₀ exactly. -/
theorem sourceSpan_map (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i) :
    (sourceSpan p).map (embedM R) = midpointSpan p := by
  apply map_comap_eq_self
  simpa only [alpha, stabilizer_m_base, Mbar] using
    (span_le_radius p).trans (geometry.V_local _ rfl common.large_distance)

/-- Mapping back recovers Z_alpha exactly. -/
theorem sourceDenominator_map (R : Subgroup M) :
    (sourceDenominator R).map (embedM R) = Z R (alpha R) := by
  apply map_comap_eq_self
  simpa only [alpha, stabilizer_m_base, Mbar] using Z_le_stabilizer R (alpha R)

/-- The marked projection kernel acts trivially on V₀/Z_alpha. -/
theorem sourceSpan_kernel_commutator_le [Finite M] (early : EarlyFacts R geometry)
    (p : FlagCriticalData source geometry i) :
    ⁅sourceSpan p, source.projection.ker⁆ ≤ sourceDenominator R := by
  apply commutator_le.mpr
  intro x hx m hm
  change embedM R ⁅x, m⁆ ∈ Z R (alpha R)
  rw [map_commutatorElement]
  apply span_commutator_le_Z early p
  apply commutator_mem_commutator (show embedM R x ∈ midpointSpan p from hx)
  rw [Q_alpha R source.two_group source.core_le]
  exact mem_map_of_mem _ (source.projection_kernel ▸ hm)

private theorem elementary_of_squares {A : Type*} [Group A]
    (h : ∀ a : A, a ^ 2 = 1) : IsElementaryAbelian 2 A := by
  have hi (a : A) : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h a)
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr h }
  intro a b
  simpa only [hi] using mul_inv_rev a b

private theorem quotient_elementary_of_squares {A : Type*} [Group A]
    (N : Subgroup A) [N.Normal] (h : ∀ a : A, a ^ 2 ∈ N) :
    IsElementaryAbelian 2 (A ⧸ N) := by
  apply elementary_of_squares
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact h y

/-- Normality inside the numerator gives the intrinsic quotient. -/
theorem sourceSpan_denominator_normal (p : FlagCriticalData source geometry i) :
    ((sourceDenominator R).subgroupOf (sourceSpan p)).Normal := by
  let := sourceDenominator_normal R
  infer_instance

/-- The pullback quotient is elementary abelian, using the early square bound. -/
theorem sourceSpan_quotient_elementary (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (p : FlagCriticalData source geometry i) :
    letI := sourceSpan_denominator_normal p
    IsElementaryAbelian 2
      (sourceSpan p ⧸ (sourceDenominator R).subgroupOf (sourceSpan p)) := by
  let := sourceSpan_denominator_normal p
  apply quotient_elementary_of_squares ((sourceDenominator R).subgroupOf (sourceSpan p))
  intro y
  simp only [mem_subgroupOf, sourceDenominator, mem_comap, coe_pow, map_pow]
  exact radius_square_mem_Z common early ⟨embedM R y, span_le_radius p y.property⟩

/-- A trivial quotient action would annihilate the chosen noncentral triple. -/
theorem sourceSpan_action_nontrivial (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i) :
    ¬ ⁅sourceSpan p, (⊤ : Subgroup M)⁆ ≤ sourceDenominator R := by
  intro h
  have hmap := map_mono (f := embedM R) h
  rw [map_commutator, sourceSpan_map common p, sourceDenominator_map,
    ← MonoidHom.range_eq_map] at hmap
  have hSG : ⁅midpointSpan p, stabilizer R (alpha R)⁆ ≤ Z R (alpha R) := by
    simpa only [alpha, stabilizer_m_base, Mbar] using hmap
  have hmiddle : ⁅Z R p.middle, flagResidual source i⁆ ≤ Z R (alpha R) :=
    (commutator_mono (middle_le_span p)
      ((flagResidual_le source i).trans (flagParabolic_le source i))).trans hSG
  apply p.middle_triple
  have hzero := (commutator_mono hmiddle
    (V_le_Q geometry common.large_distance _ rfl)).trans (geometry.centralizes _ rfl).le
  exact hzero.trans bot_le

/-- The transported layer lies in G_alpha by the critical distance bound. -/
theorem transported_layer_le_stabilizer (hb : geometry.b R = 4)
    (p : FlagCriticalData source geometry i) (t : Vertex R)
    (ht : nu R geometry (alpha R) t) (g : FreeAmalgam R)
    (hg : act R g (alpha R) = t) :
    Z R (act R g p.middle) ≤ stabilizer R (alpha R) := by
  have hc : color R (act R g p.middle) = false := by
    rw [action_preserves_color]
    exact p.middle_color
  apply Z_le_stabilizer_of_dist_le _ (geometry.exists_critical _ hc)
  rw [geometry.distance_constant _ hc]
  change (cosetGraph R).dist (act R g p.middle) (alpha R) ≤ geometry.b R
  have hh := (cosetGraph_connected R).dist_triangle
    (u := act R g p.middle) (v := t) (w := alpha R)
  rw [transported_distance p g t hg, ht.1] at hh
  rw [hb]
  omega

/-- Failure of crossing supplies a genuine nonidentity involution of the
marked quotient with a fixed preimage of index at most two. -/
theorem exists_small_fixed_actor_of_non_crossing [Finite M]
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (p : FlagCriticalData source geometry i)
    (t : Vertex R) (ht : nu R geometry (alpha R) t)
    (g : FreeAmalgam R) (hg : act R g (alpha R) = t)
    (hescape : ¬ Z R (act R g p.middle) ≤ Q R (alpha R))
    (hindex : (Q R t).relIndex (midpointSpan p) ≤ 2)
    (hvanish : ⁅Z R (act R g p.middle), midpointSpan p ⊓ Q R t⁆ ≤ Z R (alpha R)) :
    let := sourceDenominator_normal R
    ∃ a : M, source.projection a ≠ 1 ∧ (source.projection a) ^ 2 = 1 ∧
      (centralizerModulo (sourceSpan p) (zpowers a) (sourceDenominator R)).relIndex
        (sourceSpan p) ≤ 2 := by
  let := sourceDenominator_normal R
  obtain ⟨z, hz, hzQ⟩ := SetLike.not_le_iff_exists.mp hescape
  have hzM : z ∈ (embedM R).range := by
    have := transported_layer_le_stabilizer hb p t ht g hg hz
    simpa only [alpha, stabilizer_m_base, Mbar] using this
  obtain ⟨a, rfl⟩ := hzM
  have ha : source.projection a ≠ 1 := by
    intro ha
    apply hzQ
    rw [Q_alpha R source.two_group source.core_le]
    exact mem_map_of_mem _ (source.projection_kernel ▸ ha)
  have hc : color R (act R g p.middle) = false := by
    rw [action_preserves_color]
    exact p.middle_color
  let := geometry.Z_elementary
    (lt_trans (by decide : 0 < 2) common.large_distance) _ hc
  have ha2 : a ^ 2 = 1 := by
    apply embedM_injective R
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (embedM R a) hz
  refine ⟨a, ha, by rw [← map_pow, ha2, map_one], ?_⟩
  let T := sourceSpan p ⊓ (Q R t).comap (embedM R)
  have hT : T ≤ centralizerModulo (sourceSpan p) (zpowers a) (sourceDenominator R) := by
    intro x hx
    apply mem_centralizerModulo_iff.mpr
    refine ⟨hx.1, ?_⟩
    intro b hb
    change embedM R ⁅b, x⁆ ∈ Z R (alpha R)
    rw [map_commutatorElement]
    have hbZ : embedM R b ∈ Z R (act R g p.middle) :=
      (zpowers_le.mpr (show a ∈ (Z R (act R g p.middle)).comap (embedM R) from hz)) hb
    exact hvanish (commutator_mem_commutator hbZ hx)
  have hTi : T.relIndex (sourceSpan p) = (Q R t).relIndex (midpointSpan p) := by
    rw [show T = sourceSpan p ⊓ (Q R t).comap (embedM R) from rfl,
      inf_relIndex_left, relIndex_comap, sourceSpan_map common p]
  exact (relIndex_le_of_le_left hT
    (T.subgroupOf (sourceSpan p)).index_ne_zero_of_finite).trans (hTi.trans_le hindex)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation.Detection
