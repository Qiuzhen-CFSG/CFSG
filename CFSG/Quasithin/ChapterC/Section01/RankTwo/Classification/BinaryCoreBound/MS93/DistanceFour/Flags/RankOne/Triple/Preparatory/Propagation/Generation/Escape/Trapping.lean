module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Generation.Escape.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Generation.Escape.RecognitionInputs

/-!
# A trapped midpoint span has a small nontrivial quotient actor

If t belongs to nu(alpha), V_alpha does not lie in Q_t: otherwise Z_t
would centralize V_alpha and belong to B_alpha. Choose an element outside
Q_t and pull it back through the transported M-embedding. It is nontrivial
under the original projection. If the transported span lies in Q_alpha,
its displacement by that element lies in [Q_alpha,V_alpha], hence Z_alpha.
Modulo Z_t this has order at most two by the common-edge index bound.

The original preimages are normal in M, their quotient is elementary by
the early square bound, and the critical midpoint gives nontrivial action.
Thus trapping supplies all SmallDisplacementData. The recognition of a
split natural section from these data is a separate remaining theorem.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), claim (2), p.906,
using the preceding local conclusions (4.6.1)--(4.6.7).
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

/-- The midpoint span inside the original finite M, through embedM. -/
noncomputable def spanPreimage (p : FlagCriticalData source geometry i) : Subgroup M :=
  (midpointSpan p).comap (embedM R)
/-- The actual Z_alpha denominator inside the original M. -/
noncomputable def denominatorPreimage (R : Subgroup M) : Subgroup M :=
  (Z R (alpha R)).comap (embedM R)

/-- The numerator maps onto the entire original midpoint span. -/
theorem spanPreimage_map (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i) :
    (spanPreimage p).map (embedM R) = midpointSpan p := by
  apply map_comap_eq_self
  change midpointSpan p ≤ Mbar R
  simpa only [alpha, stabilizer_m_base] using
    (span_le_radius p).trans (geometry.V_local _ rfl common.large_distance)

/-- The denominator maps onto the entire original Z-layer. -/
theorem denominatorPreimage_map (R : Subgroup M) :
    (denominatorPreimage R).map (embedM R) = Z R (alpha R) := by
  apply map_comap_eq_self
  change Z R (alpha R) ≤ Mbar R
  simpa only [alpha, stabilizer_m_base] using Z_le_stabilizer R (alpha R)

/-- Relative local normality becomes normality in M under the faithful embedding. -/
theorem spanPreimage_normal (p : FlagCriticalData source geometry i) :
    (spanPreimage p).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  intro m _
  apply le_normalizer_comap (embedM R)
  exact span_normalized p (by
    rw [alpha, stabilizer_m_base]
    change embedM R m ∈ Mbar R
    exact ⟨m, rfl⟩)

/-- The denominator is normal in M, without ambient amalgam normality. -/
theorem denominatorPreimage_normal (R : Subgroup M) :
    (denominatorPreimage R).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  intro m _
  apply le_normalizer_comap (embedM R)
  exact Z_normalized R (alpha R) (by
    rw [alpha, stabilizer_m_base]
    change embedM R m ∈ Mbar R
    exact ⟨m, rfl⟩)

/-- The original Z-layer is contained in the numerator. -/
theorem denominatorPreimage_le [Finite M] (p : FlagCriticalData source geometry i) :
    denominatorPreimage R ≤ spanPreimage p := comap_mono (Z_le_span p)

/-- The given projection kernel acts trivially on the actual section. -/
theorem spanPreimage_kernel_action [Finite M] (early : EarlyFacts R geometry)
    (p : FlagCriticalData source geometry i) :
    ⁅spanPreimage p, source.projection.ker⁆ ≤ denominatorPreimage R := by
  apply map_le_iff_le_comap.mp
  rw [map_commutator]
  apply (commutator_mono (map_comap_le _ _) ?_).trans (span_commutator_le_Z early p)
  rw [source.projection_kernel, ← Q_alpha R source.two_group source.core_le]

private theorem elementary_quotient_of_square {A : Type*} [Group A]
    (N : Subgroup A) [N.Normal] (hp : ∀ x : A, x ^ 2 ∈ N) :
    IsElementaryAbelian 2 (A ⧸ N) := by
  have hq (x : A ⧸ N) : x ^ 2 = 1 := by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hp y
  exact { is_comm := ⟨fun x y =>
            (Commute.of_orderOf_dvd_two (fun z => orderOf_dvd_of_pow_eq_one (hq z)) x y).eq⟩
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hq }

/-- The square bound gives elementary abelianness of the literal preimage quotient. -/
theorem spanPreimage_elementary [Finite M] (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (p : FlagCriticalData source geometry i) :
    letI := denominatorPreimage_normal R
    IsElementaryAbelian 2 (spanPreimage p ⧸ (denominatorPreimage R).subgroupOf (spanPreimage p)) := by
  let := denominatorPreimage_normal R
  apply elementary_quotient_of_square ((denominatorPreimage R).subgroupOf (spanPreimage p))
  intro y
  rw [mem_subgroupOf, denominatorPreimage, mem_comap, coe_pow, map_pow]
  exact radius_square_mem_Z common early
    ⟨embedM R (y : M), span_le_radius p y.property⟩

open scoped commutatorElement in
/-- The critical midpoint makes the quotient action nontrivial. -/
theorem spanPreimage_nontrivial (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (p : FlagCriticalData source geometry i) :
    ¬ ⁅spanPreimage p, (⊤ : Subgroup M)⁆ ≤ denominatorPreimage R := by
  intro h
  have hh := map_mono (f := embedM R) h
  rw [map_commutator, spanPreimage_map common p, denominatorPreimage_map,
    ← MonoidHom.range_eq_map] at hh
  apply span_not_le_B early p
  intro x hx
  apply (mem_B_iff R (alpha R) (geometry.Z_normal _)
    (geometry.V_local _ rfl common.large_distance) x).mpr
  refine ⟨span_le_radius p hx, ?_⟩
  intro l hl
  rw [commutator_comm] at hh
  apply hh (commutator_mem_commutator ?_ hx)
  change l ∈ Mbar R
  simpa only [alpha, stabilizer_m_base] using
    (show l ∈ stabilizer R (alpha R) from map_subtype_le _ hl)


/-- The same original numerator maps onto the transported span. -/
theorem transportedSpanPreimage_map (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i) (g : FreeAmalgam R) :
    (spanPreimage p).map (transportedEmbedding g) = transportedSpan p g := by
  rw [transportedEmbedding, ← map_map, spanPreimage_map common p, transportedSpan]

/-- The same original denominator maps onto the transported Z-layer. -/
theorem transportedDenominatorPreimage_map (g : FreeAmalgam R) :
    (denominatorPreimage R).map (transportedEmbedding g) = Z R (act R g (alpha R)) := by
  rw [transportedEmbedding, ← map_map, denominatorPreimage_map, Z_act]

/-- The source marking kernel maps onto the actual transported neighborhood kernel. -/
theorem transportedKernel_map [Finite M] (g : FreeAmalgam R) :
    source.projection.ker.map (transportedEmbedding g) = Q R (act R g (alpha R)) := by
  rw [transportedEmbedding, ← map_map, source.projection_kernel,
    ← Q_alpha R source.two_group source.core_le, Q_act]

/-- A moving distance-two vertex detects a nontrivial radius actor at that vertex. -/
theorem radius_not_le_kernel (early : EarlyFacts R geometry)
    (t : Vertex R) (ht : nu R geometry (alpha R) t) :
    ¬ V R (alpha R) ≤ Q R t := by
  intro h
  apply ht.2
  rw [early.B_eq_center _ rfl]
  have hZV : Z R t ≤ V R (alpha R) := le_iSup_of_le t (le_iSup_of_le ht.1.le le_rfl)
  have hc := commutator_eq_bot_iff_le_centralizer.mp
    (geometry.centralizes t (color_of_distance_two (alpha R) t rfl ht.1))
  intro z hz
  refine ⟨⟨z, hZV hz⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro v
  exact Subtype.ext (hc hz v (h v.property))

/-- Trapping bounds displacement by Z_alpha modulo Z_t, of order at most two. -/
theorem trappedSpan_small_displacement [Finite M]
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (p : FlagCriticalData source geometry i) (g : FreeAmalgam R)
    (t : Vertex R) (hg : act R g (alpha R) = t)
    (ht : nu R geometry (alpha R) t) (htrap : transportedSpan p g ≤ Q R (alpha R)) :
    ∃ m : M, source.projection m ≠ 1 ∧
      (denominatorPreimage R).relIndex (⁅spanPreimage p, zpowers m⁆) ≤ 2 := by
  classical
  obtain ⟨x, hxV, hxQ⟩ := SetLike.not_le_iff_exists.mp (radius_not_le_kernel early t ht)
  have hVt : V R (alpha R) ≤ stabilizer R t :=
    (V_le_Q geometry common.large_distance _ rfl).trans
      (Q_le_stabilizer_of_dist_le_two (alpha R) t rfl
        (color_of_distance_two (alpha R) t rfl ht.1)
        (by rw [SimpleGraph.dist_comm]; exact ht.1.le))
  have hxrange : x ∈ (transportedEmbedding g).range := by
    rw [transportedEmbedding_range, hg]
    exact hVt hxV
  obtain ⟨m, hm⟩ := hxrange
  have hπ : source.projection m ≠ 1 := by
    intro he
    apply hxQ
    rw [← hg, ← transportedKernel_map (source := source)]
    exact ⟨m, he, hm⟩
  refine ⟨m, hπ, ?_⟩
  rw [← relIndex_map_map_of_injective _ _ (transportedEmbedding_injective g),
    transportedDenominatorPreimage_map, map_commutator, transportedSpanPreimage_map common p,
    MonoidHom.map_zpowers, hm, hg]
  have hle : ⁅transportedSpan p g, zpowers x⁆ ≤ Z R (alpha R) := by
    rw [commutator_comm]
    exact (commutator_mono (zpowers_le.mpr hxV) htrap).trans
      (early.commutator_le_Z _ rfl)
  let := finite_stabilizer R (alpha R)
  let : Finite (Z R (alpha R)) := Finite.of_injective
    (inclusion (Z_le_stabilizer R (alpha R))) (inclusion_injective _)
  exact (relIndex_le_of_le_right hle index_ne_zero_of_finite).trans
    (intersection_index_le_two early t (alpha R)
      (color_of_distance_two (alpha R) t rfl ht.1)
      (by rw [SimpleGraph.dist_comm]; exact ht.1))


/-- Trapping gives all the input to the small-displacement recognition theorem,
including the action through the original projection. -/
theorem smallDisplacementData_of_trappedSpan [Finite M]
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (p : FlagCriticalData source geometry i) (g : FreeAmalgam R)
    (t : Vertex R) (hg : act R g (alpha R) = t)
    (ht : nu R geometry (alpha R) t) (htrap : transportedSpan p g ≤ Q R (alpha R)) :
    SmallDisplacementData source.projection (spanPreimage p) (denominatorPreimage R) where
  projection_surjective := source.projection_surjective
  kernel_le := denominatorPreimage_le p
  normal_group := spanPreimage_normal p
  normal_kernel := denominatorPreimage_normal R
  elementary := spanPreimage_elementary common early p
  kernel_action := spanPreimage_kernel_action early p
  nontrivial_action := spanPreimage_nontrivial common early p
  small_actor := trappedSpan_small_displacement common early p g t hg ht htrap

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation
