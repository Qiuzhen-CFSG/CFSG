module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.PointParabolic

/-!
# Actor control in a native Mathieu parabolic preimage

The full max1 projection has a two-group kernel. A non-two seed normal in
a trio preimage therefore remains non-two and normal in the actual Mathieu
trio stabilizer. If its conjugate closure by an actor inside max1 stays in
that preimage, the native Mathieu trio-core theorem forces the projected
actor into the trio stabilizer. Taking the full inverse image retains the
entire kernel and controls the original actor.

JankoMax1Actor applies this to the same original exterior parabolic and
projected actor, then supplies the ambient normalizer conclusion. Simultaneous
containment in this native max1 remains explicit; this does not establish
that containment for two independently selected cover rows.
Source: Aschbacher–Smith 12.5.4, printed p.819/PDF p.836.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.MathieuParabolic
open Janko4.Cardinality MathieuHallActors
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
local notation "M" => max1Subgroup matrixA_mul_self matrixB_pow_four
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups

/-- A native max1 actor whose seed closure stays in the same trio preimage
is contained in that preimage. The entire elementary kernel is retained. -/
theorem actor_le_of_trio_preimage (J U A : Subgroup M)
    (hJ : ∃ g : Sporadic.Mathieu.M24, J = (trioStabilizer standardTrio).comap
      ((MulAut.conj g).toMonoidHom.comp projection))
    (hUJ : U ≤ J) (hJU : J ≤ normalizer (U : Set M))
    (hnt : ¬ IsPGroup 2 U) (hc : conjugateSpanBy U A ≤ J) : A ≤ J := by
  obtain ⟨g, hg⟩ := hJ
  let f := (MulAut.conj g).toMonoidHom.comp projection
  have hk : f.ker = projection.ker := by
    ext x
    change MulAut.conj g (projection x) = 1 ↔ projection x = 1
    exact (MulAut.conj g).map_eq_one_iff
  have hkp : IsPGroup 2 f.ker := by
    rw [hk, projection_ker, localKernel_eq_twoCore]
    exact pCore_isPGroup
  have hmap : J.map f = trioStabilizer standardTrio := by
    rw [hg]
    exact map_comap_eq_self_of_surjective
      ((MulAut.conj g).surjective.comp projection_surjective) _
  have hup : U.map f ≤ trioStabilizer standardTrio := (map_mono hUJ).trans_eq hmap
  have hnorm : trioStabilizer standardTrio ≤ normalizer (U.map f : Set _) :=
    hmap ▸ (map_mono hJU).trans (U.le_normalizer_map f)
  have hnot : ¬ IsPGroup 2 (U.map f) := fun ht =>
    hnt ((ht.comap_of_ker_isPGroup f hkp).to_le (le_comap_map f U))
  have hspan : conjugateSpanBy (U.map f) (A.map f) ≤ trioStabilizer standardTrio := by
    rw [← map_conjugateSpanBy]
    exact (map_mono hc).trans_eq hmap
  have hactor := Sporadic.Mathieu.M24LocalGeometry.TrioNormalSeeds.actor_le_of_seed_closure
    (U.map f) (A.map f) hup ((normal_subgroupOf_iff_le_normalizer hup).mpr hnorm)
    hnot hspan
  rw [hg]
  exact map_le_iff_le_comap.mp hactor

end Janko4.LocalStructure.MathieuParabolic
