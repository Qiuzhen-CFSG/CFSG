module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Setup
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates.Transport

/-!
# The two Y-span intersection estimates

Put K = V_alpha intersect Q_c and U = the full-second-actor span of Y.
The actual natural sections give |V_alpha/K| = 4 and |K/Y| = 4^n.
The radius center B lies in Y. Escape makes |Y/B| at least two; in the
crossing case the bound |V_alpha/B| ≤ 64 forces |K/Y| ≤ 4. Crossing and
escape give |U/Y| ≥ 4, hence |V_alpha/U| ≤ 4. Fixation of U by the second
core then gives the literal quotient-centralizer index.

In the contained case, normalization and the first quotient put [U,Q_delta1]
in Y. The first natural quotient extends this containment to V_alpha:
the quotient centralizer is invariant under the ordered first residual,
and a nonzero orbit of the actual cubic matrix spans that natural plane.
The large-intersection hypothesis makes |K/Y| at least four, so |Y/B| ≤ 4.
The source identity V_alpha-star intersect B = Z_alpha bounds the actual
starred Y-intersection, and therefore the first-core commutator image.

The radius bound and full-first-actor fixation of Y are explicit earlier
premises, produced independently by the endpoint/radius calculation. Final
unconditional Estimates assembly remains with the parent module. No
recognition, dimension-six, or chief-factor conclusion is assumed here.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), notation on printed p.905, (4.6.10), and the two intersection cases
in (4.6.12)(5), printed p.911. The sections (1)--(2) are on printed p.910.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
private theorem local_residual_normalizes_radius (k : Sections.Frame source) :
    Flags.RankOne.flagResidual source k.orientation ≤ normalizer (V R (alpha R)) :=
  (Flags.RankOne.flagResidual_le source k.orientation).trans
    ((Flags.RankOne.flagParabolic_le source k.orientation).trans
      (DistanceEight.V_normalized R _))

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

private theorem B_le_Y (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (s : CriticalSegment geometry) :
    B R (alpha R) (geometry.Z_normal (alpha R)) ≤ Sections.fixedPreimage s.middle := by
  have hBV := Early.B_le_radius common (alpha R) rfl
  have hBc : B R (alpha R) (geometry.Z_normal (alpha R)) ≤
      centralizer (V R (alpha R) : Set (FreeAmalgam R)) := by
    rw [radius.B_eq_center (alpha R) rfl]
    rintro _ ⟨z, hz, rfl⟩ y hy
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y, hy⟩)
  have hZc : Z R s.middle ≤ V R (alpha R) :=
    le_iSup_of_le s.middle (le_iSup_of_le
      (by rw [SimpleGraph.dist_comm, s.first_distance]) le_rfl)
  apply le_commutatorPreimage
  · change _ ≤ V R (alpha R) ⊓ Q R s.middle
    rw [radius_inf_kernel common rfl s.first_distance]
    exact le_inf hBV (hBc.trans (centralizer_le hZc))
  · exact (commutator_mono le_rfl
      (show Q R (beta R) ≤ stabilizer R (alpha R) from
        fun _ hx => hx.2 _ (adjacent_symm R (base_adjacent R)))).trans
      (B_fixed_by_stabilizer common radius)

private theorem Y_not_le_B (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (s : CriticalSegment geometry) (f : Seed.Frame source)
    (hescape : ¬ ySpan f s.middle ≤ Q R s.middle) :
    ¬ Sections.fixedPreimage s.middle ≤ B R (alpha R) (geometry.Z_normal (alpha R)) := by
  intro hYB
  have hUB : ySpan f s.middle ≤ B R (alpha R) (geometry.Z_normal (alpha R)) := by
    apply conjugateSpanBy_le hYB
    intro x hx
    have hxS : x ∈ stabilizer R (alpha R) := by
      rw [alpha, stabilizer_m_base]
      exact map_le_range (embedM R) _ hx
    rw [mem_normalizer_iff_map_conj_eq]
    exact Flags.B_map_conj geometry radius.toEarlyFacts (alpha R) rfl ⟨x, hxS⟩
  exact hescape (hUB.trans ((B_le_Y common radius s).trans
    ((commutatorPreimage_le _ _ _).trans inf_le_right)))

private theorem second_index_power_four (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) :
    ∃ n : ℕ, (Sections.fixedPreimage s.middle).relIndex (Sections.intersection s.middle) = 4 ^ n := by
  obtain ⟨k⟩ := Sections.exists_frame common radius hb
  obtain ⟨n, e, φ, honto, hker, hcoords, hact⟩ :=
    Sections.exists_second_natural common radius k hb s hbc d
  refine ⟨n, ?_⟩
  change ((Sections.fixedPreimage s.middle).subgroupOf (Sections.intersection s.middle)).index = _
  rw [← hker]
  change Nat.card (Sections.intersection s.middle ⧸ φ.ker) = _
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ honto).toEquiv]
  change Nat.card (Fin n → Fin 2 → ZMod 2) = _
  simp only [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  rfl

private theorem relIndex_ge_two_of_not_le {G : Type*} [Group G]
    (H K : Subgroup G) [Finite K] (h : ¬ K ≤ H) : 2 ≤ H.relIndex K := by
  have hzero : H.relIndex K ≠ 0 := index_ne_zero_of_finite
  have hone : H.relIndex K ≠ 1 := fun he => h (relIndex_eq_one.mp he)
  omega

private theorem second_index_ge_four (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hs : ¬ s.SmallIntersection)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) :
    4 ≤ (Sections.fixedPreimage s.middle).relIndex (Sections.intersection s.middle) := by
  obtain ⟨n, hn⟩ := second_index_power_four common radius hb s hbc d
  have hne : ¬ Sections.intersection s.middle ≤ Sections.fixedPreimage s.middle := by
    intro h
    apply hs
    have hVQ : V R s.middle ≤ Q R (beta R) :=
      (Flags.V_le_Q geometry common.large_distance s.middle s.middle_color).trans
        (Q_le_adjacent_h R rfl (adjacent_symm R hbc))
    exact (commutator_mono h hVQ).trans
      (commutator_commutatorPreimage_le _ _ _
        (inf_le_left.trans ((geometry.V_local (alpha R) rfl common.large_distance).trans
          (Z_normalized R _))))
  have hnpos : 1 ≤ n := by
    by_contra hn0
    have hz : n = 0 := by omega
    rw [hz, pow_zero, relIndex_eq_one] at hn
    exact hne hn
  rw [hn]
  exact Nat.pow_le_pow_right (by decide : 0 < 4) hnpos

/-- The literal starred quotient is bounded using (4.6.10), before any
recognition or chief-factor calculation. -/
theorem star_index_le_radius_index (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) :
    (Z R (alpha R)).relIndex (VStar R geometry (alpha R) (beta R)) ≤
      (B R (alpha R) (geometry.Z_normal (alpha R))).relIndex (V R (alpha R)) := by
  let : Finite (V R (alpha R)) := Early.finite_radius common (alpha R) rfl
  have h := radius.star_intersection (alpha R) (beta R) rfl (base_adjacent R)
  rw [← h, inf_comm, inf_relIndex_right]
  exact relIndex_le_of_le_right (Flags.star_le_radius geometry _ _) index_ne_zero_of_finite

/-- The large-intersection hypothesis makes K/Y nontrivial. Its natural
summands and the first natural plane leave at most four cosets of B in Y;
(4.6.10) transports that bound to the actual starred intersection. -/
theorem star_intersection_Y_index_le_four_of_radius
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry) (hs : ¬ s.SmallIntersection)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R)))
    (hrad : (B R (alpha R) (geometry.Z_normal (alpha R))).relIndex (V R (alpha R)) ≤ 64) :
    (Z R (alpha R)).relIndex
      (VStar R geometry (alpha R) (beta R) ⊓ Sections.fixedPreimage s.middle) ≤ 4 := by
  let B₀ := B R (alpha R) (geometry.Z_normal (alpha R))
  let Y := Sections.fixedPreimage s.middle
  let K := Sections.intersection s.middle
  let S := VStar R geometry (alpha R) (beta R)
  let A := V R (alpha R)
  let : Finite A := Early.finite_radius common (alpha R) rfl
  let : Finite Y := Finite.of_injective
    (inclusion ((commutatorPreimage_le _ _ _).trans inf_le_left)) (inclusion_injective _)
  have hBY : B₀ ≤ Y := B_le_Y common radius s
  have hYK : Y ≤ K := commutatorPreimage_le _ _ _
  have hKA : K ≤ A := inf_le_left
  obtain ⟨k⟩ := Sections.exists_frame common radius hb
  have hKAi : K.relIndex A = 4 := Sections.intersection_index_four common radius k hb s hbc
  have hKYi : 4 ≤ Y.relIndex K := second_index_ge_four common radius hb s hs hbc d
  have hprod := relIndex_mul_relIndex B₀ Y A hBY (hYK.trans hKA)
  have hprod' := relIndex_mul_relIndex Y K A hYK hKA
  rw [hKAi] at hprod'
  have hBYi : B₀.relIndex Y ≤ 4 := by
    change B₀.relIndex A ≤ 64 at hrad
    nlinarith
  have he : B₀ ⊓ (S ⊓ Y) = Z R (alpha R) := by
    rw [← inf_assoc, inf_comm B₀ S]
    change (VStar R geometry (alpha R) (beta R) ⊓
      B R (alpha R) (geometry.Z_normal (alpha R))) ⊓ Y = _
    rw [radius.star_intersection (alpha R) (beta R) rfl (base_adjacent R)]
    exact inf_eq_left.mpr (Sections.Z_le_fixedPreimage common s.first_distance)
  change (Z R (alpha R)).relIndex (S ⊓ Y) ≤ 4
  rw [← he, inf_relIndex_right]
  exact (relIndex_le_of_le_right inf_le_right
    (show B₀.relIndex Y ≠ 0 from index_ne_zero_of_finite)).trans hBYi

/-- Crossing and escape give at least four Y-cosets in the literal span.
The natural K/Y section and the radius bound therefore give the source's
intermediate bound |V_alpha/U| ≤ 4, before taking a quotient centralizer. -/
theorem crossing_span_index_le_four_of_radius
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hrad : (B R (alpha R) (geometry.Z_normal (alpha R))).relIndex (V R (alpha R)) ≤ 64)
    (hescape : ¬ ySpan f s.middle ≤ Q R s.middle)
    (hcross : ¬ ySpan f s.middle ⊓ Q R s.middle ≤ Sections.fixedPreimage s.middle) :
    (ySpan f s.middle).relIndex (V R (alpha R)) ≤ 4 := by
  let B₀ := B R (alpha R) (geometry.Z_normal (alpha R))
  let Y := Sections.fixedPreimage s.middle
  let K := Sections.intersection s.middle
  let U₀ := ySpan f s.middle
  let A := V R (alpha R)
  let : Finite A := Early.finite_radius common (alpha R) rfl
  let : Finite Y := Finite.of_injective
    (inclusion ((commutatorPreimage_le _ _ _).trans inf_le_left)) (inclusion_injective _)
  let : Finite U₀ := Finite.of_injective (inclusion (ySpan_le_radius f s.middle))
    (inclusion_injective _)
  let : Finite ↥(U₀ ⊓ Q R s.middle) := Finite.of_injective (inclusion inf_le_left)
    (inclusion_injective _)
  have hBY : B₀ ≤ Y := B_le_Y common radius s
  have hYK : Y ≤ K := commutatorPreimage_le _ _ _
  have hKA : K ≤ A := inf_le_left
  have hYU : Y ≤ U₀ := le_conjugateSpanBy _ _
  have hUA : U₀ ≤ A := ySpan_le_radius f s.middle
  obtain ⟨k⟩ := Sections.exists_frame common radius hb
  have hKAi : K.relIndex A = 4 := Sections.intersection_index_four common radius k hb s hbc
  have hBYi : 2 ≤ B₀.relIndex Y := relIndex_ge_two_of_not_le _ _
    (Y_not_le_B common radius s f hescape)
  obtain ⟨n, hn⟩ := second_index_power_four common radius hb s hbc d
  change Y.relIndex K = 4 ^ n at hn
  have hprod := relIndex_mul_relIndex B₀ Y A hBY (hYK.trans hKA)
  have hprod' := relIndex_mul_relIndex Y K A hYK hKA
  rw [hKAi] at hprod'
  have hKYle : Y.relIndex K ≤ 8 := by
    change B₀.relIndex A ≤ 64 at hrad
    nlinarith
  have hKY : Y.relIndex K ≤ 4 := by
    rw [hn] at hKYle ⊢
    have hnle : n ≤ 1 := by
      by_contra h
      have hp : 4 ^ 2 ≤ 4 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      norm_num at hp
      omega
    exact (Nat.pow_le_pow_right (by decide) hnle).trans (by decide)
  have hUI : 2 ≤ Y.relIndex (U₀ ⊓ Q R s.middle) :=
    relIndex_ge_two_of_not_le _ _ hcross
  have hUQ : 2 ≤ (Q R s.middle).relIndex U₀ := relIndex_ge_two_of_not_le _ _ hescape
  have hsplit := relIndex_inf_mul_relIndex Y (Q R s.middle) U₀
  rw [inf_comm (Q R s.middle) U₀, inf_eq_left.mpr (hYK.trans inf_le_right)] at hsplit
  have hYUge : 4 ≤ Y.relIndex U₀ := by nlinarith
  have hlast := relIndex_mul_relIndex Y U₀ A hYU hUA
  change U₀.relIndex A ≤ 4
  nlinarith

/-- The crossing case of (4.6.12)(5). The fixed Y-span lies in the quotient
centralizer of the second core, with the exact Z_alpha denominator. -/
theorem crossing_bound_of_radius_and_Y_fixed
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry) (_hs : ¬ s.SmallIntersection)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s)
    (hescape : ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle)
    (hrad : (B R (alpha R) (geometry.Z_normal (alpha R))).relIndex (V R (alpha R)) ≤ 64)
    (hY : ⁅Sections.fixedPreimage s.middle, (f.actor false).map (embedM R)⁆ ≤ Z R (alpha R))
    (hcross : ¬ ySpan f s.middle ⊓ Q R s.middle ≤ Sections.fixedPreimage s.middle) :
    (commutatorPreimage (V R (alpha R)) ((f.core true).map (embedM R))
      (Z R (alpha R))).relIndex (V R (alpha R)) ≤ 4 := by
  let : Finite (V R (alpha R)) := Early.finite_radius common (alpha R) rfl
  have hfixed := (first_actor_fixed_consequences common d f s.middle hY).2
  have hUC := le_commutatorPreimage (ySpan_le_radius f s.middle) hfixed
  exact (relIndex_le_of_le_left hUC (show (ySpan f s.middle).relIndex
    (V R (alpha R)) ≠ 0 from index_ne_zero_of_finite)).trans
    (crossing_span_index_le_four_of_radius common radius hb s hbc d f hrad
      (ySpan_escape common radius hb s hbc d f hf hescape) hcross)
private def planeCycle : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  ⟨!![0, 1; 1, 1], by decide⟩

private theorem planeCycle_mem : planeCycle ∈ commutator
    (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
  let a : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) := ⟨!![0, 1; 1, 0], by decide⟩
  let b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) := ⟨!![1, 1; 0, 1], by decide⟩
  have h : planeCycle = ⁅b, a⁆ := by decide
  rw [h]
  exact commutator_mem_commutator (mem_top _) (mem_top _)

private theorem planeCycle_spans : ∀ v : Fin 2 → ZMod 2, v ≠ 0 →
    ∀ w : Fin 2 → ZMod 2, w = 0 ∨ w = v ∨
      w = planeCycle.val.mulVec v ∨ w = v + planeCycle.val.mulVec v := by decide

private theorem radius_commutator_edge_le_intersection
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (k : Sections.Frame source) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle) :
    ⁅V R (alpha R), Q R (beta R)⁆ ≤ Sections.intersection s.middle := by
  have hVQ : V R (alpha R) ≤ Q R (beta R) :=
    (Flags.V_le_Q geometry common.large_distance _ rfl).trans
      (Q_le_adjacent_h R rfl (base_adjacent R))
  have hQV : Q R (beta R) ≤ normalizer (V R (alpha R)) :=
    (show Q R (beta R) ≤ stabilizer R (alpha R) from
      fun _ hx => hx.2 _ (adjacent_symm R (base_adjacent R))).trans
      (DistanceEight.V_normalized R _)
  have hmid : ⁅V R (alpha R), V R s.middle⁆ ≤ Sections.intersection s.middle := by
    apply le_inf
    · exact le_normalizer_iff_commutator_le_left.mp
        (((Flags.V_le_Q geometry common.large_distance _ s.middle_color).trans
          (Q_le_adjacent_h R rfl (adjacent_symm R hbc))).trans hQV)
    · apply le_trans _ (Flags.V_le_Q geometry common.large_distance _ s.middle_color)
      exact le_normalizer_iff_commutator_le_right.mp
        (hVQ.trans ((show Q R (beta R) ≤ stabilizer R s.middle from
          fun _ hx => hx.2 _ hbc).trans (DistanceEight.V_normalized R _)))
  have hpre : Q R (beta R) ≤ commutatorPreimage (Q R (beta R))
      (V R (alpha R)) (Sections.intersection s.middle) := by
    rw [← Sections.midpoint_radius_supplement common radius k hb s hbc]
    apply sup_le
    · apply le_commutatorPreimage le_sup_left
      rwa [commutator_comm]
    · apply le_commutatorPreimage le_sup_right
      rw [commutator_comm]
      exact (radius.commutator_le_Z (alpha R) rfl).trans
        (Sections.Z_le_intersection common s.first_distance)
  rw [commutator_comm]
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (Sections.edge_normalizes_intersection hbc))

/-- In the contained case the actual first-core displacement of U lies in Y.
This uses normalization by the opposite parabolic and the literal first
quotient, without identifying the first core with the ordered residual. -/
theorem ySpan_first_core_displacement_le_Y
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle) (f : Seed.Frame source)
    (hf : Seed.Compatible f s)
    (hcontained : ySpan f s.middle ⊓ Q R s.middle ≤ Sections.fixedPreimage s.middle) :
    ⁅ySpan f s.middle, (f.core false).map (embedM R)⁆ ≤ Sections.fixedPreimage s.middle := by
  obtain ⟨k⟩ := Sections.exists_frame common radius hb
  apply le_trans (le_inf ?_ ?_) hcontained
  · apply le_normalizer_iff_commutator_le_left.mp
    apply le_trans _ (ySpan_normalized f s.middle)
    rw [f.actor_eq]
    exact map_mono (f.core_le_parabolic false true)
  · rw [hf.first_core]
    exact ((commutator_mono (ySpan_le_radius f s.middle) le_rfl).trans
      (radius_commutator_edge_le_intersection common radius k hb s hbc)).trans inf_le_right

private theorem radius_eq_of_invariant_escaping_subgroup
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (k : Sections.Frame source) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R)))
    (T : Subgroup (FreeAmalgam R)) (hTV : T ≤ V R (alpha R))
    (hKT : Sections.intersection s.middle ≤ T)
    (hTn : Flags.RankOne.flagResidual source k.orientation ≤ normalizer T)
    (hescape : ¬ T ≤ Q R s.middle) : V R (alpha R) ≤ T := by
  classical
  obtain ⟨e, φ, honto, hker, hcoords, hact⟩ :=
    Sections.exists_first_natural_map common radius k hb s hbc d
  let E := (T.subgroupOf (V R (alpha R))).map φ
  obtain ⟨x, hxT, hxQ⟩ := SetLike.not_le_iff_exists.mp hescape
  let x' : V R (alpha R) := ⟨x, hTV hxT⟩
  let v : Fin 2 → ZMod 2 := (φ x').toAdd
  have hv : v ≠ 0 := by
    intro hv
    have hxker : x' ∈ φ.ker := by
      change φ x' = 1
      exact Multiplicative.toAdd.injective hv
    rw [hker] at hxker
    exact hxQ hxker.2
  have hvE : Multiplicative.ofAdd v ∈ E := mem_map_of_mem φ hxT
  let c : BinarySL2Residual.C := ⟨planeCycle, planeCycle_mem⟩
  obtain ⟨g, hg⟩ := Sections.markedResidualProjection_surjective source k c
  let y : V R (alpha R) := ⟨g * (x : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹,
    (mem_normalizer_iff.mp (local_residual_normalizes_radius k g.property) x).mp x'.property⟩
  have hyT : (y : FreeAmalgam R) ∈ T :=
    (mem_normalizer_iff.mp (hTn g.property) x).mp hxT
  have hyE : φ y ∈ E := mem_map_of_mem φ hyT
  have hy : (φ y).toAdd = planeCycle.val.mulVec v := by
    rw [hact g x' y rfl, hg]
  have hwE : Multiplicative.ofAdd (planeCycle.val.mulVec v) ∈ E := by
    have he : φ y = Multiplicative.ofAdd (planeCycle.val.mulVec v) :=
      Multiplicative.toAdd.injective hy
    rwa [he] at hyE
  have hE : E = ⊤ := by
    apply top_unique
    intro z _
    rcases planeCycle_spans v hv z.toAdd with hz | hz | hz | hz
    · have he : z = 1 := Multiplicative.toAdd.injective hz
      rw [he]
      exact E.one_mem
    · exact (show z = Multiplicative.ofAdd v from Multiplicative.toAdd.injective hz) ▸ hvE
    · exact (show z = Multiplicative.ofAdd (planeCycle.val.mulVec v) from
        Multiplicative.toAdd.injective hz) ▸ hwE
    · have he : z = Multiplicative.ofAdd v * Multiplicative.ofAdd (planeCycle.val.mulVec v) :=
        Multiplicative.toAdd.injective hz
      rw [he]
      exact E.mul_mem hvE hwE
  have hkerT : φ.ker ≤ T.subgroupOf (V R (alpha R)) := by
    rw [hker]
    exact fun x hx => hKT hx
  have htop : T.subgroupOf (V R (alpha R)) = ⊤ := by
    rw [← comap_map_eq_self hkerT]
    change E.comap φ = ⊤
    rw [hE, comap_top]
  intro z hz
  have hmem : (⟨z, hz⟩ : V R (alpha R)) ∈ T.subgroupOf (V R (alpha R)) := by
    rw [htop]
    exact mem_top _
  exact hmem

/-- The first natural quotient propagates the contained-case displacement
from the escaping U to the entire radius. The second section supplies the
displacement on K. All normalization uses the source-ordered residual. -/
theorem radius_first_core_displacement_le_Y_of_contained
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s)
    (hescape : ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle)
    (hcontained : ySpan f s.middle ⊓ Q R s.middle ≤ Sections.fixedPreimage s.middle) :
    ⁅V R (alpha R), (f.core false).map (embedM R)⁆ ≤ Sections.fixedPreimage s.middle := by
  obtain ⟨k⟩ := Sections.exists_frame common radius hb
  let Y := Sections.fixedPreimage s.middle
  let C := commutatorPreimage (V R (alpha R)) (Q R (beta R)) Y
  have hVQ : V R (alpha R) ≤ Q R (beta R) :=
    (Flags.V_le_Q geometry common.large_distance _ rfl).trans
      (Q_le_adjacent_h R rfl (base_adjacent R))
  have hVY : V R (alpha R) ≤ normalizer Y :=
    hVQ.trans (Sections.edge_normalizes_fixedPreimage common hbc)
  have hKC : Sections.intersection s.middle ≤ C :=
    le_commutatorPreimage inf_le_left
      (Sections.intersection_commutator_edge_le_fixedPreimage common radius k hb s hbc)
  have hUC : ySpan f s.middle ≤ C := by
    apply le_commutatorPreimage (ySpan_le_radius f s.middle)
    rw [← hf.first_core]
    exact ySpan_first_core_displacement_le_Y common radius hb s hbc f hf hcontained
  have hH := f.first_residual_eq_flag s hf k.orientation k.edge_kernel
  have hCn : (f.residual false).map (embedM R) ≤ normalizer C := by
    rw [hH]
    apply commutatorPreimage_normalized _ _ _ _ hVY
    · exact local_residual_normalizes_radius k
    · rw [← k.edge_kernel]
      exact (Flags.RankOne.flagResidual_le source k.orientation).trans
        (Flags.RankOne.flagKernel_normalized source k.orientation)
    · exact Sections.residual_normalizes_fixedPreimage common radius k s.first_distance hbc
  have hVC : V R (alpha R) ≤ C :=
    radius_eq_of_invariant_escaping_subgroup common radius k hb s hbc d C
      (commutatorPreimage_le _ _ _) hKC (by simpa only [hH] using hCn)
      (fun h => ySpan_escape common radius hb s hbc d f hf hescape (hUC.trans h))
  rw [hf.first_core]
  exact (commutator_mono hVC le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hVY)

/-- The contained case of MS93 (4.6.12)(5), with the literal first-core
commutator and Z_alpha denominator. The radius bound remains an explicit
earlier-source premise; no starred order or recognition is assumed. -/
theorem contained_bound_of_radius_and_Y_fixed
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry) (hs : ¬ s.SmallIntersection)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s)
    (hescape : ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle)
    (hrad : (B R (alpha R) (geometry.Z_normal (alpha R))).relIndex (V R (alpha R)) ≤ 64)
    (_hY : ⁅Sections.fixedPreimage s.middle, (f.actor false).map (embedM R)⁆ ≤ Z R (alpha R))
    (hcontained : ySpan f s.middle ⊓ Q R s.middle ≤ Sections.fixedPreimage s.middle) :
    (Z R (alpha R)).relIndex
      ⁅VStar R geometry (alpha R) (beta R), (f.core false).map (embedM R)⁆ ≤ 4 := by
  let : Finite (V R (alpha R)) := Early.finite_radius common (alpha R) rfl
  let : Finite ↥(VStar R geometry (alpha R) (beta R) ⊓ Sections.fixedPreimage s.middle) :=
    Finite.of_injective (inclusion (inf_le_left.trans (Flags.star_le_radius geometry _ _)))
      (inclusion_injective _)
  have hcomm : ⁅VStar R geometry (alpha R) (beta R), (f.core false).map (embedM R)⁆ ≤
      VStar R geometry (alpha R) (beta R) ⊓ Sections.fixedPreimage s.middle := by
    apply le_inf
    · apply le_normalizer_iff_commutator_le_left.mp
      exact (map_le_range (embedM R) _).trans (by
        change Mbar R ≤ _
        simpa only [alpha, stabilizer_m_base] using Flags.star_normalized geometry (alpha R) (beta R))
    · exact (commutator_mono (Flags.star_le_radius geometry _ _) le_rfl).trans
        (radius_first_core_displacement_le_Y_of_contained common radius hb s hbc d f hf hescape hcontained)
  exact (relIndex_le_of_le_right hcomm index_ne_zero_of_finite).trans
    (star_intersection_Y_index_le_four_of_radius common radius hb s hs hbc d hrad)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
