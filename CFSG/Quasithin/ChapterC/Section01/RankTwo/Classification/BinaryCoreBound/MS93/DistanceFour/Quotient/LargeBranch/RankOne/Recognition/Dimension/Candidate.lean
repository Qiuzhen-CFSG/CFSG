module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Setup

/-!
# The canonical midpoint seed and its full-actor generation

The candidate is the actual second-parabolic conjugate span of Z_c in the
supplied radius quotient. Its nonzero image follows from the large branch;
its preimage adds exactly Z_alpha. Parabolic transport reduces containment
in the second star to containment of the midpoint line.

For two genuine natural SL2(2) copies, a lifted order-three matrix has an
invertible displacement on every invariant subspace. This proves the seed's
full-actor commutator generation, retaining the literal quotient action.
The final constructor still takes the natural coordinates and the two
geometric containments explicitly; it does not assert the source calculation
which must produce them or the starred dimension-six conclusion.

Source: Meierfrankenfeld--Stellmacher (1993), final paragraph of
(4.6.12)(5), printed p.912, with the seed contract on pp.910--911.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- All generators of the canonical candidate lie in the domain of d. -/
theorem midpointSpan_le_radius (f : Seed.Frame source) (s : CriticalSegment geometry) :
    midpointSpan f s.middle ≤ V R (alpha R) :=
  conjugateSpanBy_le (Seed.midpoint_Z_le_radius s)
    ((f.ambient_le true).trans (DistanceEight.V_normalized R (alpha R)))

/-- The critical midpoint places the candidate in the full starred layer,
without assuming dimension six or the more restrictive second-star containment. -/
theorem midpointSpan_le_star [Finite M] (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (f : Seed.Frame source) (s : CriticalSegment geometry) :
    midpointSpan f s.middle ≤ VStar R geometry (alpha R) (beta R) :=
  (conjugateSpanBy_le (Z_le_orbitSpan s.middle)
    ((f.ambient_le true).trans (orbitSpan_normalized s.middle))).trans
    (orbitSpan_le_star geometry radius.toEarlyFacts _ _ (base_adjacent R)
      (midpoint_nu common radius hb s))

/-- The canonical quotient candidate is invariant under the actual second parabolic. -/
theorem midpointSpace_normalized (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (c : Vertex R) :
    ∀ m ∈ f.parabolic true, ∀ v ∈ midpointSpace d f c,
      d.representation (source.projection m) v ∈ midpointSpace d f c := by
  intro m hm v hv
  exact d.subspace_invariant_of_mem _ m
    (DistanceEight.V_normalized R (alpha R)
      (f.ambient_le true (mem_map_of_mem _ hm)))
    (le_normalizer_conjugateSpanBy _ _ (mem_map_of_mem _ hm)) v hv

/-- The large-intersection hypothesis makes the canonical candidate nonzero. -/
theorem midpointSpace_ne_bot (d : LayerModule source (V R (alpha R)))
    (radius : RadiusFacts R geometry) (f : Seed.Frame source)
    (s : CriticalSegment geometry) (hs : ¬ s.SmallIntersection) :
    midpointSpace d f s.middle ≠ ⊥ := by
  intro h
  apply Seed.midpoint_image_ne_bot d radius s hs
  apply le_bot_iff.mp
  rw [← h]
  exact d.subspace_mono (le_conjugateSpanBy _ _)

/-- Restoring the quotient kernel gives exactly Z_alpha times the actual conjugate span. -/
theorem midpointSpace_preimage (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (s : CriticalSegment geometry) :
    d.preimage (midpointSpace d f s.middle) = Z R (alpha R) ⊔ midpointSpan f s.middle := by
  rw [midpointSpace, Seed.LayerModule.preimage_subspace_eq d _ (midpointSpan_le_radius f s),
    inf_eq_left.mpr (show Z R (alpha R) ≤ V R (alpha R) from Z_le_VBall R _ 2)]

/-- Source distance-two containment discharges the restored Z_alpha kernel.
Thus the seed preimage lies in Q_c precisely when the actual conjugate span does. -/
theorem midpointSpace_preimage_le_iff (common : CommonFacts R source geometry)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (s : CriticalSegment geometry) :
    d.preimage (midpointSpace d f s.middle) ≤ Q R s.middle ↔
      midpointSpan f s.middle ≤ Q R s.middle := by
  rw [midpointSpace_preimage, sup_le_iff]
  have hZ : Z R (alpha R) ≤ Q R s.middle := by
    rw [← common.X_eq_Z (alpha R) rfl]
    apply common.X_bound (alpha R) rfl s.middle s.middle_color
    rw [s.first_distance, geometry.distance_constant (alpha R) rfl]
    exact common.large_distance
  exact and_iff_right hZ

private theorem firstStar_invariant (d : LayerModule source (V R (alpha R)))
    (m n : M) (v : d.Space) (hv : v ∈ Seed.firstTildeStar (geometry := geometry) d n) :
    d.representation (source.projection m) v ∈
      Seed.firstTildeStar (geometry := geometry) d (m * n) := by
  obtain ⟨x, hx, rfl⟩ := (d.mem_subspace_iff _ v).mp hv
  have hm : embedM R m ∈ stabilizer R (alpha R) := by
    rw [alpha, stabilizer_m_base]
    exact ⟨m, rfl⟩
  let y : V R (alpha R) := ⟨embedM R m * x * (embedM R m)⁻¹,
    le_normalizer_iff.mp (DistanceEight.V_normalized R (alpha R)) _ hm _ x.property⟩
  apply (d.mem_subspace_iff _ _).mpr
  refine ⟨y, ?_, d.action m x y rfl⟩
  rw [Seed.firstStar_mul]
  exact mem_map_of_mem _ hx

/-- The full second parabolic permutes adjacent first stars and preserves its
core-fixed space, hence normalizes the literal second starred layer. -/
theorem secondStar_normalized (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) :
    ∀ m ∈ f.parabolic true, ∀ v ∈ Seed.secondTildeStar (geometry := geometry) d f 1,
      d.representation (source.projection m) v ∈ Seed.secondTildeStar (geometry := geometry) d f 1 := by
  intro m hm
  have hc : Seed.secondCore f 1 = f.core true := by
    have he : (MulAut.conj (1 : M)).toMonoidHom = MonoidHom.id M := by
      ext x
      simp
    simp only [Seed.secondCore, he, Subgroup.map_id]
  have hn : source.projection m ∈ normalizer ((f.core true).map source.projection) :=
    (le_normalizer_map _) (mem_map_of_mem _ (f.core_normalized true hm))
  change Seed.secondTildeStar (geometry := geometry) d f 1 ≤
    (Seed.secondTildeStar (geometry := geometry) d f 1).comap
      (d.representation (source.projection m))
  apply iSup_le
  intro p v hv
  change d.representation (source.projection m) v ∈
    Seed.secondTildeStar (geometry := geometry) d f 1
  apply (le_iSup (fun p : f.parabolic true =>
    Seed.firstTildeStar (geometry := geometry) d (1 * p) ⊓
      fixedSpace d.representation ((Seed.secondCore f 1).map source.projection))
        (⟨m, hm⟩ * p))
  refine ⟨?_, ?_⟩
  · change d.representation (source.projection m) v ∈
      Seed.firstTildeStar (geometry := geometry) d (1 * (m * (p : M)))
    have hv' := firstStar_invariant (geometry := geometry) d m (1 * (p : M)) v hv.1
    simpa only [one_mul, Subgroup.coe_mul] using hv'
  · rw [hc] at *
    intro a
    have ha : (source.projection m)⁻¹ * (a : SL) * source.projection m ∈
        (f.core true).map source.projection := by
      simpa only [inv_inv] using
        (mem_normalizer_iff.mp ((normalizer _).inv_mem hn) a).mp a.property
    have he := congrArg (d.representation (source.projection m)) (hv.2 ⟨_, ha⟩)
    change d.representation (source.projection m)
      (d.representation ((source.projection m)⁻¹ * (a : SL) * source.projection m) v) =
        d.representation (source.projection m) v at he
    change d.representation (a : SL) (d.representation (source.projection m) v) = _
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left,
      mul_assoc, inv_mul_cancel, mul_one] using he

/-- Second-star containment of the whole candidate reduces to containment
of the actual midpoint line, using the proved full-parabolic invariance. -/
theorem midpointSpace_le_secondStar_iff (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (s : CriticalSegment geometry) :
    midpointSpace d f s.middle ≤ Seed.secondTildeStar (geometry := geometry) d f 1 ↔
      d.subspace (Z R s.middle) ≤ Seed.secondTildeStar (geometry := geometry) d f 1 := by
  constructor
  · exact fun h => (d.subspace_mono (le_conjugateSpanBy _ _)).trans h
  · intro h
    change d.subspace (conjugateSpanBy (Z R s.middle) ((f.parabolic true).map (embedM R))) ≤ _
    rw [d.subspace_conjugateSpan _ (Seed.midpoint_Z_le_radius s) _
      ((f.ambient_le true).trans (DistanceEight.V_normalized R (alpha R)))]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨m, hm, rfl⟩, v, hv, rfl⟩
    exact secondStar_normalized d f m hm v (h hv)

private def cubic : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  ⟨!![0, 1; 1, 1], by decide⟩

private theorem cubic_displacement (v : Fin 2 → ZMod 2) :
    cubic.val.mulVec (cubic.val.mulVec v) - cubic.val.mulVec v = v := by
  have h : ∀ v : Fin 2 → ZMod 2,
      cubic.val.mulVec (cubic.val.mulVec v) - cubic.val.mulVec v = v := by decide
  exact h v

/-- The specified two natural copies have total dimension four. -/
theorem NaturalCopies.finrank_eq_four
    {d : LayerModule source (V R (alpha R))} {f : Seed.Frame source}
    (n : NaturalCopies (geometry := geometry) d f) :
    Module.finrank (ZMod 2) (Seed.secondTildeStar (geometry := geometry) d f 1) = 4 := by
  calc
    _ = Module.finrank (ZMod 2) (Fin 2 → Fin 2 → ZMod 2) := n.coordinates.finrank_eq
    _ = 4 := by simp [Module.finrank_pi_fintype]

/-- Every invariant subspace of the specified natural copies is generated by
commutators with the full actor. A lifted cubic gives an explicit preimage
under its displacement map; no identification with SL2(2)' is made. -/
theorem NaturalCopies.moved_eq [Finite M]
    {d : LayerModule source (V R (alpha R))} {f : Seed.Frame source}
    (n : NaturalCopies (geometry := geometry) d f)
    (A : Submodule (ZMod 2) d.Space)
    (hA : A ≤ Seed.secondTildeStar (geometry := geometry) d f 1)
    (hn : ∀ m ∈ f.parabolic true, ∀ v ∈ A,
      d.representation (source.projection m) v ∈ A) :
    Seed.movedSpace d.representation ((f.actor true).map source.projection) A = A := by
  rw [f.actor_eq]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨m, hm, rfl⟩, v, hv, rfl⟩
    exact A.sub_mem (hn m hm v hv) hv
  · intro v hv
    obtain ⟨m, hm⟩ := n.onto cubic
    let v' : Seed.secondTildeStar (geometry := geometry) d f 1 := ⟨v, hA hv⟩
    let w : Seed.secondTildeStar (geometry := geometry) d f 1 :=
      ⟨d.representation (source.projection m) v, hA (hn m m.property v hv)⟩
    let z : Seed.secondTildeStar (geometry := geometry) d f 1 :=
      ⟨d.representation (source.projection m) w,
        hA (hn m m.property _ (hn m m.property v hv))⟩
    have he : z - w = v' := by
      apply n.coordinates.injective
      ext j i
      have h1 := n.action m v' w rfl j
      have h2 := n.action m w z rfl j
      rw [hm] at h1 h2
      have hh := congrFun (cubic_displacement (n.coordinates v' j)) i
      simpa only [map_sub, Pi.sub_apply, h2, h1] using hh
    have he' : d.representation (source.projection m)
        (d.representation (source.projection m) v) -
          d.representation (source.projection m) v = v := congrArg Subtype.val he
    exact Submodule.subset_span ⟨source.projection m, mem_map_of_mem _ m.property,
      d.representation (source.projection m) v, hn m m.property v hv, he'⟩

/-- Construct the actual p.912 seed from natural coordinates and the two
remaining geometric containments. Normalization, nonzero image, full-actor
commutator generation and the restored-kernel containment are proved here. -/
theorem canonical_input [Finite M] (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (n : NaturalCopies (geometry := geometry) d f)
    (hline : d.subspace (Z R s.middle) ≤ Seed.secondTildeStar (geometry := geometry) d f 1)
    (hspan : midpointSpan f s.middle ≤ Q R s.middle) :
    ∃ x : Seed.Input (geometry := geometry) d f s.middle,
      x.space = midpointSpace d f s.middle := by
  have hstar := (midpointSpace_le_secondStar_iff d f s).mpr hline
  exact ⟨{
    space := midpointSpace d f s.middle
    le_star := hstar
    normalized := midpointSpace_normalized d f s.middle
    nonzero := midpointSpace_ne_bot d radius f s hs
    moved := n.moved_eq _ hstar (midpointSpace_normalized d f s.middle)
    preimage_le := (midpointSpace_preimage_le_iff common d f s).mpr hspan }, rfl⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
