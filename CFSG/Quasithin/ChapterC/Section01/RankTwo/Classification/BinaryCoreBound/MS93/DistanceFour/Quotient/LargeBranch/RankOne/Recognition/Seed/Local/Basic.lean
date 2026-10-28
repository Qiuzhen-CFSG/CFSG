module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Consequences

/-!
# The midpoint line and literal quotient transport for the local seed

The common edge layer Z_beta lies in Z_alpha and has index two in the
midpoint layer Z_c. The large-intersection hypothesis makes the image of
Z_c in V_alpha/Z_alpha nonzero, so this image is a binary line.

The quotient map sends ambient commutators to linear displacements and
conjugate spans to linear orbit spans, with exactly the supplied projection
and the original ambient embedding. The actual midpoint actor is a subgroup
of the first intrinsic core image. The seed is fixed by the second intrinsic
core, and its midpoint displacements lie in the line just constructed.

These are inputs to the local rank-one calculation in the first paragraph
after MS93 (4.6.12)(3), printed p.910. The plane dimension, nonzero midpoint
displacement, and fixation by the first full actor still require proof;
this module does not construct LocalConsequences.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), notation on p.905 and (4.6.12)(3), pp.910--911.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

namespace LayerModule
variable {S : Subgroup (FreeAmalgam R)} (d : LayerModule source S)

/-- The image--preimage adjunction on subgroups of the actual quotient domain. -/
theorem subspace_le_iff_le_preimage (T : Subgroup (FreeAmalgam R))
    (hT : T ≤ S) (A : Submodule (ZMod 2) d.Space) :
    d.subspace T ≤ A ↔ T ≤ d.preimage A := by
  constructor
  · intro h t ht
    exact (d.mem_preimage_iff A t).mpr ⟨hT ht,
      h ((d.mem_subspace_iff T _).mpr ⟨⟨t, hT ht⟩, ht, rfl⟩)⟩
  · intro h v hv
    obtain ⟨t, ht, rfl⟩ := (d.mem_subspace_iff T v).mp hv
    exact ((d.mem_preimage_iff A t).mp (h ht)).2

/-- The literal quotient image of an ambient commutator is the linear moved space. -/
theorem subspace_commutator_preimage (A : Submodule (ZMod 2) d.Space)
    (H : Subgroup M) (hS : H.map (embedM R) ≤ normalizer S) :
    d.subspace ⁅d.preimage A, H.map (embedM R)⁆ =
      Seed.movedSpace d.representation (H.map source.projection) A := by
  have hc : ⁅H.map (embedM R), d.preimage A⁆ ≤ S :=
    (commutator_mono le_rfl (d.preimage_le A)).trans
      (le_normalizer_iff_commutator_le_right.mp hS)
  rw [commutator_comm]
  apply le_antisymm
  · apply (d.subspace_le_iff_le_preimage _ hc _).mpr
    apply commutator_le.mpr
    rintro _ ⟨m, hm, rfl⟩ t ht
    obtain ⟨htS, htA⟩ := (d.mem_preimage_iff A t).mp ht
    let y : S := ⟨embedM R m * t * (embedM R m)⁻¹,
      le_normalizer_iff.mp hS _ (mem_map_of_mem _ hm) _ htS⟩
    let t' : S := ⟨t, htS⟩
    apply (d.mem_preimage_iff _ _).mpr
    refine ⟨(y * t'⁻¹).property, ?_⟩
    change (d.projection (y * t'⁻¹)).toAdd ∈
      Seed.movedSpace d.representation (H.map source.projection) A
    rw [map_mul, map_inv]
    change (d.projection y).toAdd + -(d.projection t').toAdd ∈
      Seed.movedSpace d.representation (H.map source.projection) A
    rw [← sub_eq_add_neg]
    rw [d.action m t' y rfl]
    exact Submodule.subset_span ⟨source.projection m, mem_map_of_mem _ hm,
      (d.projection t').toAdd, htA, rfl⟩
  · apply Submodule.span_le.mpr
    rintro w ⟨_, ⟨m, hm, rfl⟩, v, hv, rfl⟩
    obtain ⟨t, ht⟩ := d.onto (Multiplicative.ofAdd v)
    have htA : (t : FreeAmalgam R) ∈ d.preimage A := by
      apply (d.mem_preimage_iff A t).mpr
      exact ⟨t.property, by rw [ht]; exact hv⟩
    let y : S := ⟨embedM R m * t * (embedM R m)⁻¹,
      le_normalizer_iff.mp hS _ (mem_map_of_mem _ hm) _ t.property⟩
    apply (d.mem_subspace_iff _ _).mpr
    refine ⟨y * t⁻¹, commutator_mem_commutator (mem_map_of_mem _ hm) htA, ?_⟩
    rw [map_mul, map_inv]
    change (d.projection y).toAdd + -(d.projection t).toAdd =
      d.representation (source.projection m) v - v
    rw [← sub_eq_add_neg]
    rw [d.action m t y rfl, ht]
    rfl

end LayerModule

namespace Seed

/-- The span of all translates of a subspace under the specified matrix actor. -/
noncomputable def orbitSpace {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) SL W) (H : Subgroup SL)
    (A : Submodule (ZMod 2) W) : Submodule (ZMod 2) W :=
  Submodule.span (ZMod 2) {w | ∃ h ∈ H, ∃ v ∈ A, ρ h v = w}

end Seed

namespace LayerModule
variable {S : Subgroup (FreeAmalgam R)} (d : LayerModule source S)

/-- Conjugation through embedM descends to the given linear action on the orbit span. -/
theorem subspace_conjugateSpan (T : Subgroup (FreeAmalgam R)) (hT : T ≤ S)
    (H : Subgroup M) (hS : H.map (embedM R) ≤ normalizer S) :
    d.subspace (conjugateSpanBy T (H.map (embedM R))) =
      Seed.orbitSpace d.representation (H.map source.projection) (d.subspace T) := by
  have hspan : conjugateSpanBy T (H.map (embedM R)) ≤ S := conjugateSpanBy_le hT hS
  apply le_antisymm
  · apply (d.subspace_le_iff_le_preimage _ hspan _).mpr
    apply (closure_le _).mpr
    rintro _ ⟨_, ⟨m, hm, rfl⟩, t, ht, rfl⟩
    let t' : S := ⟨t, hT ht⟩
    let y : S := ⟨embedM R m * t * (embedM R m)⁻¹,
      le_normalizer_iff.mp hS _ (mem_map_of_mem _ hm) _ t'.property⟩
    apply (d.mem_preimage_iff _ _).mpr
    refine ⟨y.property, ?_⟩
    change (d.projection y).toAdd ∈
      Seed.orbitSpace d.representation (H.map source.projection) (d.subspace T)
    rw [d.action m t' y rfl]
    exact Submodule.subset_span ⟨source.projection m, mem_map_of_mem _ hm,
      (d.projection t').toAdd, (d.mem_subspace_iff _ _).mpr ⟨t', ht, rfl⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨m, hm, rfl⟩, v, hv, rfl⟩
    obtain ⟨t, ht, rfl⟩ := (d.mem_subspace_iff T v).mp hv
    let y : S := ⟨embedM R m * t * (embedM R m)⁻¹,
      le_normalizer_iff.mp hS _ (mem_map_of_mem _ hm) _ t.property⟩
    exact (d.mem_subspace_iff _ _).mpr ⟨y,
      subset_closure ⟨embedM R m, mem_map_of_mem _ hm, t, ht, rfl⟩,
      d.action m t y rfl⟩

end LayerModule

namespace Seed

/-- The image of the actual midpoint radius subgroup under the original projection. -/
noncomputable def midpointActor (c : Vertex R) : Subgroup SL :=
  ((V R c).comap (embedM R)).map source.projection

/-- The midpoint radius group lies in the original finite vertex stabilizer. -/
theorem midpoint_radius_le_Mbar [Finite M] (common : CommonFacts R source geometry)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle) :
    V R s.middle ≤ Mbar R := by
  have hcQ := Flags.V_le_Q geometry common.large_distance s.middle s.middle_color
  have hQb : Q R s.middle ≤ Q R (beta R) :=
    Q_le_adjacent_h R (show color R (beta R) = true from rfl) (adjacent_symm R hbc)
  intro v hv
  have hh := (hQb (hcQ hv)).2 (alpha R) (adjacent_symm R (base_adjacent R))
  simpa only [alpha, stabilizer_m_base] using hh

/-- Frame compatibility places the midpoint actor inside the first intrinsic core image. -/
theorem midpointActor_le_first_core [Finite M] (common : CommonFacts R source geometry)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (f : Frame source) (hf : Compatible f s) :
    midpointActor (source := source) s.middle ≤ (f.core false).map source.projection := by
  rintro _ ⟨m, hm, rfl⟩
  have hmQ : embedM R m ∈ Q R (beta R) :=
    Q_le_adjacent_h R (show color R (beta R) = true from rfl) (adjacent_symm R hbc)
      (Flags.V_le_Q geometry common.large_distance s.middle s.middle_color hm)
  rw [← hf.first_core] at hmQ
  obtain ⟨k, hk, he⟩ := hmQ
  have hkm := embedM_injective R he
  subst k
  exact mem_map_of_mem _ hk

/-- The distance-two midpoint layer belongs to V_alpha, the domain of the quotient. -/
theorem midpoint_Z_le_radius (s : CriticalSegment geometry) :
    Z R s.middle ≤ V R (alpha R) :=
  (Z_le_orbitSpan s.middle).trans
    (orbitSpan_le_radius s.middle ((cosetGraph R).dist_comm.trans s.first_distance).le)

/-- The edge index and the large-intersection branch identify the actual midpoint image as a line. -/
theorem midpoint_line_dimension (d : LayerModule source (V R (alpha R)))
    (radius : RadiusFacts R geometry) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) (hbc : Adjacent R (beta R) s.middle) :
    Module.finrank (ZMod 2) (d.subspace (Z R s.middle)) = 1 := by
  have hi := radius.edge_Z_index s.middle (beta R) s.middle_color (adjacent_symm R hbc)
  have hle := relIndex_le_of_le_left
    (Flags.edge_Z_le (alpha R) (beta R) rfl (base_adjacent R))
    (show (Z R (beta R)).relIndex (Z R s.middle) ≠ 0 by rw [hi]; decide)
  rw [hi, d.subspace_relIndex _ (midpoint_Z_le_radius s)] at hle
  have hn : Module.finrank (ZMod 2) (d.subspace (Z R s.middle)) ≠ 0 := by
    intro h
    exact midpoint_image_ne_bot d radius s hs ((Submodule.finrank_eq_zero).mp h)
  have hlt : Module.finrank (ZMod 2) (d.subspace (Z R s.middle)) < 2 := by
    by_contra h
    have hh := Nat.pow_le_pow_right (show 0 < (2 : ℕ) by decide) (show 2 ≤
      Module.finrank (ZMod 2) (d.subspace (Z R s.middle)) by omega)
    omega
  omega

/-- The starred seed is fixed by the second intrinsic core, without replacing the full actor by its residual. -/
theorem Input.le_second_core_fixed {d : LayerModule source (V R (alpha R))}
    {f : Frame source} {c : Vertex R} (x : Input (geometry := geometry) d f c) :
    x.space ≤ fixedSpace d.representation ((f.core true).map source.projection) := by
  have h := x.le_star.trans (secondTildeStar_le_fixed d f 1)
  have he : (MulAut.conj (1 : M)).toMonoidHom = MonoidHom.id M := by
    ext m
    simp
  simpa only [secondCore, he, Subgroup.map_id] using h

/-- The seed commutator uses the literal midpoint group, not merely an isomorphic actor. -/
theorem Input.midpoint_commutator_image [Finite M] {d : LayerModule source (V R (alpha R))}
    {f : Frame source} (common : CommonFacts R source geometry)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (x : Input (geometry := geometry) d f s.middle) :
    d.subspace ⁅d.preimage x.space, V R s.middle⁆ =
      movedSpace d.representation (midpointActor (source := source) s.middle) x.space := by
  have hm : ((V R s.middle).comap (embedM R)).map (embedM R) = V R s.middle := by
    rw [map_comap_eq]
    exact inf_eq_right.mpr (midpoint_radius_le_Mbar common s hbc)
  have hn : ((V R s.middle).comap (embedM R)).map (embedM R) ≤
      normalizer (V R (alpha R)) := by
    rw [hm]
    exact (midpoint_radius_le_Mbar common s hbc).trans (by
      simpa only [alpha, stabilizer_m_base] using DistanceEight.V_normalized R (alpha R))
  simpa only [hm, midpointActor] using d.subspace_commutator_preimage x.space
    ((V R s.middle).comap (embedM R)) hn

/-- The source opening commutator bound becomes a displacement bound into the midpoint line. -/
theorem Input.midpoint_moved_le_line [Finite M] {d : LayerModule source (V R (alpha R))}
    {f : Frame source} (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle) (x : Input (geometry := geometry) d f s.middle) :
    movedSpace d.representation (midpointActor (source := source) s.middle) x.space ≤
      d.subspace (Z R s.middle) := by
  rw [← x.midpoint_commutator_image common s hbc]
  exact d.subspace_mono (x.commutator_le_midpoint_Z radius s.middle_color)

end Seed
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
