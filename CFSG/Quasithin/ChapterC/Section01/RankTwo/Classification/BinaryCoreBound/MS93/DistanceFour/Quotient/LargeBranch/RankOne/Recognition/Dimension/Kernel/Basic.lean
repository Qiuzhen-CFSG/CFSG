module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Setup
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Candidate

/-!
# The literal unstarred midpoint kernel

On printed p.912 the subgroup X₁ is U_delta2 intersect Q_c, where U_delta2
is the unstarred layer defined on p.905. Here its ambient realization is
exactly the preimage of Dimension.secondLayer under the supplied quotient.
It contains Z_alpha, and its quotient is the intersection with the literal
midpoint kernel. Full second-parabolic normalization of U_delta2 follows
by permuting the incident first layers and preserving the intrinsic core.

The early commutator theorem gives [X₁,V_c] ≤ Z_c. We transport that bound
through the same LayerModule to the actual midpoint actor. These statements
prepare the source's index-two and natural-module calculation; they do not
assert the still-needed commutator order bound or midpoint-orbit containment.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), notation on p.905 and the final paragraph of (4.6.12)(5), p.912.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The actual unstarred U_delta2, restoring the original Z_alpha kernel. -/
noncomputable def secondPreimage (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) : Subgroup (FreeAmalgam R) :=
  d.preimage (secondLayer d f 1)

/-- The subgroup X₁ on p.912 uses the unstarred U_delta2. -/
noncomputable def midpointKernel (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (c : Vertex R) : Subgroup (FreeAmalgam R) :=
  secondPreimage d f ⊓ Q R c

/-- The portion of X₁ in the two natural starred copies, using the original quotient. -/
noncomputable def starredMidpointKernel (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (c : Vertex R) :
    Submodule (ZMod 2) (Seed.secondTildeStar (geometry := geometry) d f 1) :=
  (d.subspace (midpointKernel d f c)).comap
    (Seed.secondTildeStar (geometry := geometry) d f 1).subtype

/-- The source Z_delta2 is the centralizer of Q_delta2 in Z_alpha. -/
noncomputable def secondCenter (f : Seed.Frame source) : Subgroup (FreeAmalgam R) :=
  Z R (alpha R) ⊓ centralizer ((f.core true).map (embedM R) : Set (FreeAmalgam R))

private theorem preimage_mono (d : LayerModule source (V R (alpha R)))
    {A B : Submodule (ZMod 2) d.Space} (h : A ≤ B) : d.preimage A ≤ d.preimage B := by
  intro x hx
  obtain ⟨hxV, hxA⟩ := (d.mem_preimage_iff A x).mp hx
  exact (d.mem_preimage_iff B x).mpr ⟨hxV, h hxA⟩

/-- The unstarred preimage stays in the original radius group. -/
theorem secondPreimage_le_radius (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) : secondPreimage d f ≤ V R (alpha R) :=
  d.preimage_le _

/-- Restoring the quotient always includes Z_alpha, even if the subspace is zero. -/
theorem Z_le_secondPreimage (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) : Z R (alpha R) ≤ secondPreimage d f := by
  exact (le_inf le_rfl (Z_le_VBall R _ 2)).trans (d.inf_Z_le_preimage _)

/-- The actual starred preimage is a subgroup of its unstarred counterpart. -/
theorem secondStar_preimage_le_secondPreimage
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source) :
    d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤
      secondPreimage d f :=
  preimage_mono d (secondStar_le_secondLayer d f 1)

private theorem firstLayer_mul (m n : M) :
    firstLayer (R := R) (m * n) =
      (firstLayer (R := R) n).map (MulAut.conj (embedM R m)).toMonoidHom := by
  unfold firstLayer
  rw [map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change embedM R (m * n) * x * (embedM R (m * n))⁻¹ =
    embedM R m * (embedM R n * x * (embedM R n)⁻¹) * (embedM R m)⁻¹
  simp only [map_mul, mul_inv_rev, mul_assoc]

private theorem firstLayer_invariant (d : LayerModule source (V R (alpha R)))
    (m n : M) (v : d.Space) (hv : v ∈ d.subspace (firstLayer (R := R) n)) :
    d.representation (source.projection m) v ∈
      d.subspace (firstLayer (R := R) (m * n)) := by
  obtain ⟨x, hx, rfl⟩ := (d.mem_subspace_iff _ v).mp hv
  have hm : embedM R m ∈ stabilizer R (alpha R) := by
    rw [alpha, stabilizer_m_base]
    exact ⟨m, rfl⟩
  let y : V R (alpha R) := ⟨embedM R m * x * (embedM R m)⁻¹,
    le_normalizer_iff.mp (DistanceEight.V_normalized R (alpha R)) _ hm _ x.property⟩
  apply (d.mem_subspace_iff _ _).mpr
  refine ⟨y, ?_, d.action m x y rfl⟩
  rw [firstLayer_mul]
  exact mem_map_of_mem _ hx

/-- The full second parabolic preserves the unstarred quotient layer. -/
theorem secondLayer_normalized (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) :
    ∀ m ∈ f.parabolic true, ∀ v ∈ secondLayer d f 1,
      d.representation (source.projection m) v ∈ secondLayer d f 1 := by
  intro m hm
  have hc : Seed.secondCore f 1 = f.core true := by
    have he : (MulAut.conj (1 : M)).toMonoidHom = MonoidHom.id M := by
      ext x
      simp
    simp only [Seed.secondCore, he, Subgroup.map_id]
  have hn : source.projection m ∈ normalizer ((f.core true).map source.projection) :=
    (le_normalizer_map _) (mem_map_of_mem _ (f.core_normalized true hm))
  change secondLayer d f 1 ≤
    (secondLayer d f 1).comap
      (d.representation (source.projection m))
  apply iSup_le
  intro p v hv
  change d.representation (source.projection m) v ∈
    secondLayer d f 1
  apply (le_iSup (fun p : f.parabolic true =>
    d.subspace (firstLayer (R := R) (1 * p)) ⊓
      fixedSpace d.representation ((Seed.secondCore f 1).map source.projection))
        (⟨m, hm⟩ * p))
  refine ⟨?_, ?_⟩
  · change d.representation (source.projection m) v ∈
      d.subspace (firstLayer (R := R) (1 * (m * (p : M))))
    have hv' := firstLayer_invariant d m (1 * (p : M)) v hv.1
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

/-- This normalization holds for the literal ambient U_delta2. -/
theorem secondPreimage_normalized (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) : f.ambient true ≤ normalizer (secondPreimage d f) :=
  d.preimage_normalized _ _
    ((f.ambient_le true).trans (DistanceEight.V_normalized R (alpha R)))
    (secondLayer_normalized d f)

/-- The unstarred layer is fixed by the actual second core modulo Z_alpha. -/
theorem secondLayer_le_fixed (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) :
    secondLayer d f 1 ≤ fixedSpace d.representation ((f.core true).map source.projection) := by
  have he : (MulAut.conj (1 : M)).toMonoidHom = MonoidHom.id M := by
    ext m
    simp
  have hc : Seed.secondCore f 1 = f.core true := by
    simp only [Seed.secondCore, he, Subgroup.map_id]
  unfold secondLayer
  rw [hc]
  exact iSup_le fun _ => inf_le_right

/-- Fixation in the quotient gives the source commutator bound for the actual preimage. -/
theorem secondPreimage_commutator_core_le_Z
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source) :
    ⁅secondPreimage d f, (f.core true).map (embedM R)⁆ ≤ Z R (alpha R) := by
  apply d.preimage_commutator_le_Z
  · apply le_trans (map_le_range (embedM R) _)
    change Mbar R ≤ _
    simpa only [alpha, stabilizer_m_base] using DistanceEight.V_normalized R (alpha R)
  · exact secondLayer_le_fixed d f

/-- Distance two places the restored quotient kernel in Q_c. -/
theorem Z_le_midpointKernel (common : CommonFacts R source geometry)
    (s : CriticalSegment geometry) (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) : Z R (alpha R) ≤ midpointKernel d f s.middle := by
  refine le_inf (Z_le_secondPreimage d f) ?_
  rw [← common.X_eq_Z (alpha R) rfl]
  apply common.X_bound (alpha R) rfl s.middle s.middle_color
  rw [s.first_distance, geometry.distance_constant (alpha R) rfl]
  exact common.large_distance

/-- X₁ is the centralizer of Z_c inside the actual unstarred layer. -/
theorem midpointKernel_eq_centralizer [Finite M]
    (common : CommonFacts R source geometry) (s : CriticalSegment geometry)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source) :
    midpointKernel d f s.middle =
      secondPreimage d f ⊓ centralizer (Z R s.middle : Set (FreeAmalgam R)) := by
  have h := congrArg (fun T => secondPreimage d f ⊓ T)
    (radius_inf_kernel common rfl s.first_distance)
  simpa only [midpointKernel, ← inf_assoc, inf_eq_left.mpr (secondPreimage_le_radius d f)] using h

/-- No abstract replacement of the quotient kernel is needed. -/
theorem midpointKernel_preimage (common : CommonFacts R source geometry)
    (s : CriticalSegment geometry) (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) :
    d.preimage (d.subspace (midpointKernel d f s.middle)) = midpointKernel d f s.middle := by
  rw [Seed.LayerModule.preimage_subspace_eq d (midpointKernel d f s.middle)
      (inf_le_left.trans (secondPreimage_le_radius d f)),
    inf_eq_left.mpr (show Z R (alpha R) ≤ V R (alpha R) from Z_le_VBall R _ 2),
    sup_eq_right.mpr (Z_le_midpointKernel common s d f)]

/-- The early midpoint commutator theorem applies to X₁ with its literal kernel. -/
theorem midpointKernel_commutator_le_midpoint
    (radius : RadiusFacts R geometry) (s : CriticalSegment geometry)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source) :
    ⁅midpointKernel d f s.middle, V R s.middle⁆ ≤ Z R s.middle := by
  rw [commutator_comm]
  exact (commutator_mono le_rfl inf_le_right).trans
    (radius.commutator_le_Z s.middle s.middle_color)

/-- Transport [X₁,V_c] ≤ Z_c to the actual projected midpoint actor. -/
theorem midpointKernel_moved_le_line [Finite M]
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source) :
    Seed.movedSpace d.representation (Seed.midpointActor (source := source) s.middle)
      (d.subspace (midpointKernel d f s.middle)) ≤ d.subspace (Z R s.middle) := by
  have hm : ((V R s.middle).comap (embedM R)).map (embedM R) = V R s.middle := by
    rw [map_comap_eq]
    exact inf_eq_right.mpr (Seed.midpoint_radius_le_Mbar common s hbc)
  have hn : ((V R s.middle).comap (embedM R)).map (embedM R) ≤
      normalizer (V R (alpha R)) := by
    rw [hm]
    exact (Seed.midpoint_radius_le_Mbar common s hbc).trans (by
      simpa only [alpha, stabilizer_m_base] using DistanceEight.V_normalized R (alpha R))
  have he := d.subspace_commutator_preimage (d.subspace (midpointKernel d f s.middle))
    ((V R s.middle).comap (embedM R)) hn
  rw [midpointKernel_preimage common s d f, hm] at he
  rw [Seed.midpointActor, ← he]
  exact d.subspace_mono (midpointKernel_commutator_le_midpoint radius s d f)

/-- Relative normality of X₁ uses V_alpha' = U_alpha ≤ Z_alpha ≤ X₁. -/
theorem midpointKernel_normal (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (s : CriticalSegment geometry)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source) :
    ((midpointKernel d f s.middle).subgroupOf (secondPreimage d f)).Normal := by
  apply Normal.of_commutator_le
  intro x hx
  have hm := mem_map_of_mem (secondPreimage d f).subtype hx
  rw [map_subtype_commutator] at hm
  have hV := commutator_mono (secondPreimage_le_radius d f) (secondPreimage_le_radius d f)
  rw [radius.radius_derived (alpha R) rfl] at hV
  exact Z_le_midpointKernel common s d f (DistanceEight.U_le_Z R _ (hV hm))

/-- The quotient by X₁ retains the literal relative denominator on the unstarred layer. -/
theorem midpointKernel_relIndex_eq_pow_finrank
    (common : CommonFacts R source geometry) (s : CriticalSegment geometry)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source) :
    (midpointKernel d f s.middle).relIndex (secondPreimage d f) =
      2 ^ Module.finrank (ZMod 2) ((d.subspace (secondPreimage d f)) ⧸
        (d.subspace (midpointKernel d f s.middle)).comap
          (d.subspace (secondPreimage d f)).subtype) := by
  change ((midpointKernel d f s.middle).subgroupOf (secondPreimage d f)).index = _
  rw [← d.sectionMap_kernel _ _ (secondPreimage_le_radius d f)
      (Z_le_midpointKernel common s d f), index_ker,
    MonoidHom.range_eq_top.mpr (d.sectionMap_surjective _ _ (secondPreimage_le_radius d f)),
    Nat.card_congr (topEquiv).toEquiv]
  change Nat.card ((d.subspace (secondPreimage d f)) ⧸
    (d.subspace (midpointKernel d f s.middle)).comap
      (d.subspace (secondPreimage d f)).subtype) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
