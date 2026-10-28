module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Consequences

/-!
# Ambient subgroup algebra for propagation of the seed

Taking the preimage of a quotient image adds exactly the relative Z_alpha
kernel. Thus the local seed preimage is Z_alpha times its actual parabolic
conjugate span, and lies in the full midpoint orbit span.

For the propagation on MS93 (1993), pp.910--911, define the conjugate span
of that seed under the two-core at a second-color vertex. If the geometric
calculation puts this subgroup in Q_c, and its conjugating core together
with V_c and Q_alpha generates G_alpha, then it is the full orbit span. The normalization by V_c and Q_alpha is proved
from the radius commutator bounds, inside the original free amalgam.
The delta3--delta4 calculation and actor generation remain explicit
obligations (see Actors for the issue with the printed base-core formula); they are not conclusions of this algebraic reduction.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

namespace Seed
namespace LayerModule
variable {S : Subgroup (FreeAmalgam R)} (d : LayerModule source S)

/-- A literal subgroup is contained in the preimage of its quotient image. -/
theorem le_preimage_subspace (T : Subgroup (FreeAmalgam R)) (hT : T ≤ S) :
    T ≤ d.preimage (d.subspace T) := by
  intro t ht
  apply (d.mem_preimage_iff _ _).mpr
  exact ⟨hT ht, (d.mem_subspace_iff _ _).mpr ⟨⟨t, hT ht⟩, ht, rfl⟩⟩

/-- The preimage adds precisely the relative kernel, without choosing an
abstract isomorphism for either the subgroup or the quotient. -/
theorem preimage_subspace_eq (T : Subgroup (FreeAmalgam R)) (hT : T ≤ S) :
    d.preimage (d.subspace T) = (Z R (alpha R) ⊓ S) ⊔ T := by
  apply le_antisymm
  · intro t ht
    obtain ⟨htS, ht⟩ := (d.mem_preimage_iff _ _).mp ht
    obtain ⟨z, hzT, hz⟩ := (d.mem_subspace_iff _ _).mp ht
    let t' : S := ⟨t, htS⟩
    have he : d.projection z = d.projection t' := Multiplicative.toAdd.injective hz
    have hk : t' * z⁻¹ ∈ d.projection.ker := by
      change d.projection (t' * z⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]
    rw [d.kernel] at hk
    have htZ : t * (z : FreeAmalgam R)⁻¹ ∈ Z R (alpha R) ⊓ S :=
      ⟨hk, S.mul_mem htS (S.inv_mem z.property)⟩
    have hm := ((Z R (alpha R) ⊓ S) ⊔ T).mul_mem
      ((show Z R (alpha R) ⊓ S ≤ (Z R (alpha R) ⊓ S) ⊔ T from le_sup_left) htZ)
      ((show T ≤ (Z R (alpha R) ⊓ S) ⊔ T from le_sup_right) hzT)
    simpa only [inv_mul_cancel_right] using hm
  · exact sup_le (d.inf_Z_le_preimage _) (le_preimage_subspace d T hT)

end LayerModule

/-- The local conjugate-span identity gives an equality of actual ambient
subgroups after restoring the Z_alpha kernel. -/
theorem LocalConsequences.preimage_eq
    {d : LayerModule source (V R (alpha R))} {f : Frame source} {c : Vertex R}
    {x : Input (geometry := geometry) d f c} (hlocal : LocalConsequences d f c x)
    (hc : (cosetGraph R).dist (alpha R) c = 2) :
    d.preimage x.space = Z R (alpha R) ⊔ conjugateSpanBy (Z R c) (f.ambient true) := by
  have hspan : conjugateSpanBy (Z R c) (f.ambient true) ≤ orbitSpan c :=
    conjugateSpanBy_le (Z_le_orbitSpan c)
      ((f.ambient_le true).trans (orbitSpan_normalized c))
  rw [hlocal.conjugate_span, LayerModule.preimage_subspace_eq d _
    (hspan.trans (orbitSpan_le_radius c ((cosetGraph R).dist_comm.trans hc).le)),
    inf_eq_left.mpr (show Z R (alpha R) ≤ V R (alpha R) from Z_le_VBall R (alpha R) 2)]

/-- In particular the midpoint line itself is in the actual seed preimage. -/
theorem LocalConsequences.Z_le_preimage
    {d : LayerModule source (V R (alpha R))} {f : Frame source} {c : Vertex R}
    {x : Input (geometry := geometry) d f c} (hlocal : LocalConsequences d f c x)
    (hc : (cosetGraph R).dist (alpha R) c = 2) :
    Z R c ≤ d.preimage x.space := by
  rw [hlocal.preimage_eq hc]
  exact (le_conjugateSpanBy _ _).trans le_sup_right

/-- Local seed recognition places the seed preimage in the genuine full
orbit span, including the restored Z_alpha kernel. -/
theorem LocalConsequences.preimage_le_orbitSpan [Finite M]
    {d : LayerModule source (V R (alpha R))} {f : Frame source} {c : Vertex R}
    {x : Input (geometry := geometry) d f c} (hlocal : LocalConsequences d f c x)
    (hc : (cosetGraph R).dist (alpha R) c = 2) :
    d.preimage x.space ≤ orbitSpan c := by
  rw [hlocal.preimage_eq hc]
  exact sup_le (Z_le_orbitSpan_of_distance_two c hc)
    (conjugateSpanBy_le (Z_le_orbitSpan c)
      ((f.ambient_le true).trans (orbitSpan_normalized c)))

/-- The subgroup U from printed p.911, with m representing delta4. Its
conjugating core is Q_delta4, distinct from the base Q_delta2. -/
noncomputable def propagatedSpan {d : LayerModule source (V R (alpha R))} {f : Frame source}
    {c : Vertex R} (x : Input (geometry := geometry) d f c) (m : M) :
    Subgroup (FreeAmalgam R) :=
  conjugateSpanBy (d.preimage x.space) ((secondCore f m).map (embedM R))

/-- The candidate propagated subgroup still lies in the actual orbit span. -/
theorem propagatedSpan_le_orbitSpan [Finite M]
    {d : LayerModule source (V R (alpha R))} {f : Frame source} {c : Vertex R}
    {x : Input (geometry := geometry) d f c} (hlocal : LocalConsequences d f c x)
    (hc : (cosetGraph R).dist (alpha R) c = 2) (m : M) :
    propagatedSpan x m ≤ orbitSpan c := by
  apply conjugateSpanBy_le (hlocal.preimage_le_orbitSpan hc)
  apply le_trans (map_le_range (embedM R) _)
  change Mbar R ≤ _
  exact (stabilizer_m_base R).symm ▸ orbitSpan_normalized c

/-- Q_alpha normalizes every intermediate subgroup between Z_alpha and
V_alpha, by the literal radius commutator bound. -/
theorem kernel_normalizes_intermediate (radius : RadiusFacts R geometry)
    (T : Subgroup (FreeAmalgam R)) (hZT : Z R (alpha R) ≤ T)
    (hTV : T ≤ V R (alpha R)) : Q R (alpha R) ≤ normalizer T := by
  apply le_normalizer_iff_commutator_le_left.mpr
  exact ((commutator_mono hTV le_rfl).trans
    (radius.commutator_le_Z (alpha R) rfl)).trans hZT

/-- The source actor generation identifies the propagated candidate with
V_0 once the delta3--delta4 containment and the actual actor generation have
been established. Full orbit normalization is derived here. -/
theorem propagatedSpan_eq_orbitSpan [Finite M]
    (radius : RadiusFacts R geometry)
    {d : LayerModule source (V R (alpha R))} {f : Frame source}
    (s : CriticalSegment geometry) {x : Input (geometry := geometry) d f s.middle}
    (hlocal : LocalConsequences d f s.middle x) (m : M)
    (hmid : propagatedSpan x m ≤ Q R s.middle)
    (hgen : (V R s.middle ⊔ (secondCore f m).map (embedM R)) ⊔ Q R (alpha R) =
      stabilizer R (alpha R)) :
    propagatedSpan x m = orbitSpan s.middle := by
  have hXU : d.preimage x.space ≤ propagatedSpan x m := le_conjugateSpanBy _ _
  have hZU : Z R s.middle ≤ propagatedSpan x m :=
    (hlocal.Z_le_preimage s.first_distance).trans hXU
  have hZaU : Z R (alpha R) ≤ propagatedSpan x m := x.Z_le_preimage.trans hXU
  have hUO := propagatedSpan_le_orbitSpan hlocal s.first_distance m
  have hUV : propagatedSpan x m ≤ V R (alpha R) :=
    hUO.trans (orbitSpan_le_radius _
      ((cosetGraph R).dist_comm.trans s.first_distance).le)
  have hVc : V R s.middle ≤ normalizer (propagatedSpan x m) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    rw [commutator_comm]
    exact ((commutator_mono le_rfl hmid).trans
      (radius.commutator_le_Z s.middle s.middle_color)).trans hZU
  have hn : stabilizer R (alpha R) ≤ normalizer (propagatedSpan x m) := by
    rw [← hgen]
    exact sup_le (sup_le hVc (le_normalizer_conjugateSpanBy _ _))
      (kernel_normalizes_intermediate radius _ hZaU hUV)
  exact le_antisymm hUO (orbitSpan_le_of_normalized _ _ hZU hn)

/-- Containment of the full span follows from the same concrete
geometric obligations, rather than from a normalization certificate. -/
theorem orbitSpan_le_kernel_of_propagated [Finite M]
    (radius : RadiusFacts R geometry)
    {d : LayerModule source (V R (alpha R))} {f : Frame source}
    (s : CriticalSegment geometry) {x : Input (geometry := geometry) d f s.middle}
    (hlocal : LocalConsequences d f s.middle x) (m : M)
    (hmid : propagatedSpan x m ≤ Q R s.middle)
    (hgen : (V R s.middle ⊔ (secondCore f m).map (embedM R)) ⊔ Q R (alpha R) =
      stabilizer R (alpha R)) :
    orbitSpan s.middle ≤ Q R s.middle := by
  rw [← propagatedSpan_eq_orbitSpan radius s hlocal m hmid hgen]
  exact hmid

end Seed
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
