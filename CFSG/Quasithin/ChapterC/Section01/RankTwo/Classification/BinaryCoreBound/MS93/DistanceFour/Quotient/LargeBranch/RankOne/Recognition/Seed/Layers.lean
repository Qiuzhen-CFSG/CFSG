module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Frame

/-!
# Starred-layer transport and ambient preimages

The first-color layers are independent of their coset representative whenever
the selected parabolic normalizes the actual edge star. Every such layer lies
in V_alpha-star. The second-color layer is fixed by its intrinsic parabolic
two-core. Normalization and fixation in the literal quotient lift respectively
to normalization and a commutator contained in Z_alpha in the ambient amalgam.

These are transport facts for the seed used in MS93 (4.6.12)(3), pp.910--911;
they do not recognize the seed or assert containment of the full orbit span.
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

/-- Quotient images preserve inclusions of ambient subgroups. -/
theorem subspace_mono {A B : Subgroup (FreeAmalgam R)} (h : A ≤ B) :
    d.subspace A ≤ d.subspace B := by
  intro v hv
  obtain ⟨x, hx, rfl⟩ := (d.mem_subspace_iff A v).mp hv
  exact (d.mem_subspace_iff B _).mpr ⟨x, h hx, rfl⟩

/-- Stability for the specified quotient images lifts to actual normalization. -/
theorem preimage_normalized (A : Submodule (ZMod 2) d.Space) (H : Subgroup M)
    (hS : H.map (embedM R) ≤ normalizer S)
    (hA : ∀ m ∈ H, ∀ v ∈ A, d.representation (source.projection m) v ∈ A) :
    H.map (embedM R) ≤ normalizer (d.preimage A) := by
  apply le_normalizer_iff.mpr
  rintro _ ⟨m, hm, rfl⟩ x hx
  obtain ⟨hxS, hxA⟩ := (d.mem_preimage_iff A x).mp hx
  let y : S := ⟨embedM R m * x * (embedM R m)⁻¹,
    le_normalizer_iff.mp hS _ (mem_map_of_mem _ hm) _ hxS⟩
  apply (d.mem_preimage_iff A _).mpr
  refine ⟨y.property, ?_⟩
  change (d.projection y).toAdd ∈ A
  rw [d.action m ⟨x, hxS⟩ y rfl]
  exact hA m hm _ hxA

/-- Fixation modulo the exact kernel is an ambient Z_alpha commutator bound. -/
theorem preimage_commutator_le_Z (A : Submodule (ZMod 2) d.Space) (H : Subgroup M)
    (hS : H.map (embedM R) ≤ normalizer S)
    (hA : A ≤ fixedSpace d.representation (H.map source.projection)) :
    ⁅d.preimage A, H.map (embedM R)⁆ ≤ Z R (alpha R) := by
  rw [commutator_comm]
  apply commutator_le.mpr
  rintro _ ⟨m, hm, rfl⟩ x hx
  obtain ⟨hxS, hxA⟩ := (d.mem_preimage_iff A x).mp hx
  let x' : S := ⟨x, hxS⟩
  let y : S := ⟨embedM R m * x * (embedM R m)⁻¹,
    le_normalizer_iff.mp hS _ (mem_map_of_mem _ hm) _ hxS⟩
  have hy : d.projection y = d.projection x' := by
    apply Multiplicative.toAdd.injective
    rw [d.action m x' y rfl]
    exact hA hxA ⟨source.projection m, mem_map_of_mem _ hm⟩
  have hk : y * x'⁻¹ ∈ d.projection.ker := by
    change d.projection (y * x'⁻¹) = 1
    rw [map_mul, map_inv, hy, mul_inv_cancel]
  rw [d.kernel] at hk
  exact hk

/-- A subgroup of the layer has zero quotient image exactly when it lies
in the literal Z_alpha kernel. -/
theorem subspace_eq_bot_iff (T : Subgroup (FreeAmalgam R)) (hT : T ≤ S) :
    d.subspace T = ⊥ ↔ T ≤ Z R (alpha R) := by
  constructor
  · intro h x hx
    have hv : (d.projection ⟨x, hT hx⟩).toAdd ∈ d.subspace T :=
      (d.mem_subspace_iff T _).mpr ⟨⟨x, hT hx⟩, hx, rfl⟩
    rw [h] at hv
    have hk : (⟨x, hT hx⟩ : S) ∈ d.projection.ker := hv
    rw [d.kernel] at hk
    exact hk
  · intro h
    apply le_bot_iff.mp
    intro v hv
    obtain ⟨x, hx, rfl⟩ := (d.mem_subspace_iff T v).mp hv
    have hk : x ∈ d.projection.ker := by
      rw [d.kernel]
      exact h hx
    exact hk

end LayerModule

namespace Seed

/-- Multiplication of representatives is composition of actual ambient conjugations. -/
theorem firstStar_mul (m n : M) :
    firstStar geometry (m * n) =
      (firstStar geometry n).map (MulAut.conj (embedM R m)).toMonoidHom := by
  unfold firstStar
  rw [map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change embedM R (m * n) * x * (embedM R (m * n))⁻¹ =
    embedM R m * (embedM R n * x * (embedM R n)⁻¹) * (embedM R m)⁻¹
  simp only [map_mul, mul_inv_rev, mul_assoc]

/-- The definition descends to a first-color coset under the explicit
normalization obligation of the selected frame. -/
theorem firstStar_right_mul {f : Frame source} {s : CriticalSegment geometry}
    (hf : Compatible f s) (m : M) (p : f.parabolic false) :
    firstStar geometry (m * p) = firstStar geometry m := by
  rw [firstStar_mul]
  have hp : embedM R (p : M) ∈ normalizer (edgeStar R geometry (alpha R) (beta R)) :=
    hf.first_star_normalized (mem_map_of_mem _ p.property)
  have he : firstStar geometry (p : M) = edgeStar R geometry (alpha R) (beta R) :=
    mem_normalizer_iff_map_conj_eq.mp hp
  rw [he]
  rfl

/-- Every first-color layer lies in the literal starred stabilizer span. -/
theorem firstStar_le_star (m : M) :
    firstStar geometry m ≤ VStar R geometry (alpha R) (beta R) := by
  have hm : embedM R m ∈ stabilizer R (alpha R) := by
    rw [alpha, stabilizer_m_base]
    exact ⟨m, rfl⟩
  exact le_iSup (fun g : stabilizer R (alpha R) =>
    (edgeStar R geometry (alpha R) (beta R)).map (MulAut.conj g.val).toMonoidHom)
    ⟨embedM R m, hm⟩

/-- The first tilde layers use the original starred quotient inside V_alpha/Z_alpha. -/
theorem firstTildeStar_le_star (d : LayerModule source (V R (alpha R))) (m : M) :
    firstTildeStar (geometry := geometry) d m ≤
      d.subspace (VStar R geometry (alpha R) (beta R)) :=
  d.subspace_mono (firstStar_le_star m)

/-- The adjacent fixed-space sum still lies in the actual starred quotient. -/
theorem secondTildeStar_le_star (d : LayerModule source (V R (alpha R)))
    (f : Frame source) (m : M) :
    secondTildeStar (geometry := geometry) d f m ≤
      d.subspace (VStar R geometry (alpha R) (beta R)) := by
  apply iSup_le
  intro p
  exact inf_le_left.trans (firstTildeStar_le_star d (m * p))

/-- Each second-color layer is fixed by its actual intrinsic parabolic core. -/
theorem secondTildeStar_le_fixed (d : LayerModule source (V R (alpha R)))
    (f : Frame source) (m : M) :
    secondTildeStar (geometry := geometry) d f m ≤
      fixedSpace d.representation ((secondCore f m).map source.projection) := by
  exact iSup_le fun _ => inf_le_right

/-- The seed's normalization premise lifts to normalization of its literal preimage. -/
theorem Input.preimage_normalized {d : LayerModule source (V R (alpha R))}
    {f : Frame source} {c : Vertex R} (x : Input (geometry := geometry) d f c) :
    f.ambient true ≤ normalizer (d.preimage x.space) := by
  apply d.preimage_normalized x.space (f.parabolic true)
  · exact (f.ambient_le true).trans (DistanceEight.V_normalized R (alpha R))
  · exact x.normalized

/-- The preimage includes all of Z_alpha, as passage modulo Z_alpha requires. -/
theorem Input.Z_le_preimage {d : LayerModule source (V R (alpha R))}
    {f : Frame source} {c : Vertex R} (x : Input (geometry := geometry) d f c) :
    Z R (alpha R) ≤ d.preimage x.space := by
  intro z hz
  exact d.inf_Z_le_preimage x.space ⟨hz, Z_le_VBall R (alpha R) 2 hz⟩

/-- The opening commutator bound in (3) follows from the actual midpoint
kernel containment of the seed preimage. -/
theorem Input.commutator_le_midpoint_Z {d : LayerModule source (V R (alpha R))}
    {f : Frame source} {c : Vertex R} (x : Input (geometry := geometry) d f c)
    (radius : RadiusFacts R geometry) (hc : color R c = false) :
    ⁅d.preimage x.space, V R c⁆ ≤ Z R c := by
  rw [commutator_comm]
  exact (commutator_mono le_rfl x.preimage_le).trans (radius.commutator_le_Z c hc)

/-- The large-intersection branch makes the actual midpoint quotient image nonzero. -/
theorem midpoint_image_ne_bot (d : LayerModule source (V R (alpha R)))
    (radius : RadiusFacts R geometry) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) : d.subspace (Z R s.middle) ≠ ⊥ := by
  intro h
  apply large_intersection_not_le_Z radius s hs
  apply (d.subspace_eq_bot_iff (Z R s.middle) ?_).mp h
  exact (Z_le_orbitSpan s.middle).trans
    (orbitSpan_le_radius s.middle ((cosetGraph R).dist_comm.trans s.first_distance).le)

/-- The adjacent first-color cosets are exactly those indexed by the
second parabolic in the definition of secondTildeStar. -/
theorem Frame.incident_iff (f : Frame source) (x : f.Vertex false) (m : M) :
    f.Incident x (QuotientGroup.mk m) ↔
      ∃ p : f.parabolic true, QuotientGroup.mk (m * p) = x := by
  constructor
  · rintro ⟨n, hn, hnm⟩
    have hp : m⁻¹ * n ∈ f.parabolic true := QuotientGroup.eq.mp hnm.symm
    refine ⟨⟨m⁻¹ * n, hp⟩, ?_⟩
    simpa only [mul_inv_cancel_left] using hn
  · rintro ⟨p, hp⟩
    refine ⟨m * p, hp, ?_⟩
    apply Eq.symm
    apply QuotientGroup.eq.mpr
    simpa only [inv_mul_cancel_left] using p.property

private theorem secondCore_mul (f : Frame source) (m n : M) :
    secondCore f (m * n) = (secondCore f n).map (MulAut.conj m).toMonoidHom := by
  unfold secondCore
  rw [map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change (m * n) * x * (m * n)⁻¹ = m * (n * x * n⁻¹) * m⁻¹
  simp only [mul_inv_rev, mul_assoc]

/-- Intrinsic core normality makes the second core independent of its coset representative. -/
theorem secondCore_right_mul (f : Frame source) (m : M) (p : f.parabolic true) :
    secondCore f (m * p) = secondCore f m := by
  rw [secondCore_mul]
  have hp : secondCore f (p : M) = f.core true :=
    mem_normalizer_iff_map_conj_eq.mp (f.core_normalized true p.property)
  rw [hp]
  rfl

/-- The adjacent fixed-space sum is a well-defined second-color coset layer. -/
theorem secondTildeStar_right_mul (d : LayerModule source (V R (alpha R)))
    (f : Frame source) (m : M) (p : f.parabolic true) :
    secondTildeStar (geometry := geometry) d f (m * p) =
      secondTildeStar (geometry := geometry) d f m := by
  unfold secondTildeStar
  rw [secondCore_right_mul]
  apply le_antisymm
  · apply iSup_le
    intro q
    apply le_iSup_of_le (p * q)
    simp only [Subgroup.coe_mul, mul_assoc, le_refl]
  · apply iSup_le
    intro q
    apply le_iSup_of_le (p⁻¹ * q)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left, le_refl]

end Seed
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
