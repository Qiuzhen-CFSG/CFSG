module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.Transport

/-!
# The remaining preliminary displacement obligation

The middle paragraph on printed p.898 first bounds the displacement by
Z_i Z_(i+2), before sharpening it to Z_(i+2). The four centers recorded here
are exactly those consumed by the forward and reflected sharpening windows.
This record is an outstanding source obligation, not an addition to Earlier
or a constructor asserting that the estimate holds.

The backward estimate is proved from the actual turn on the supplied path,
using covariance and normalization by the center's stabilizer.
Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3), printed p.898.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators
open PathCentrality NormalizerTransfer
variable {M : Type*} [Group M] {R : Subgroup M}

/-- The preliminary displacement bound in the middle paragraph of p.898.
This is an explicit outstanding source obligation, not part of Earlier. -/
structure PreliminaryOnPath {a : Vertex R} (p : SourcePath R a) : Prop where
  forward : ∀ i : ℕ, Even i → 4 ≤ i → i ≤ 10 →
    ⁅hatV R (p.walk.getVert i) (p.walk.getVert (i + 2)),
      Q R (p.walk.getVert (i + 2))⁆ ≤ Z R (p.walk.getVert i) ⊔ Z R (p.walk.getVert (i + 2))

/-- Reflection of the preliminary bound uses the supplied turn at the same
center. No independently chosen path is substituted. -/
theorem PreliminaryOnPath.backward {a : Vertex R} {p : SourcePath R a}
    (preliminary : PreliminaryOnPath p) {i : ℕ}
    (hi : Even i) (hi4 : 4 ≤ i) (hi10 : i ≤ 10) :
    ⁅hatV R (p.walk.getVert i) (p.walk.getVert (i - 2)),
      Q R (p.walk.getVert (i - 2))⁆ ≤ Z R (p.walk.getVert i) ⊔ Z R (p.walk.getVert (i - 2)) := by
  obtain ⟨g, hg, ht⟩ := p.turns i hi (by omega) (by omega)
  have h := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (preliminary.forward i hi hi4 hi10)
  have hmap : (hatV R (p.walk.getVert i) (p.walk.getVert (i + 2))).map
      (MulAut.conj g⁻¹).toMonoidHom = hatV R (p.walk.getVert i) (p.walk.getVert (i + 2)) :=
    mem_normalizer_iff_map_conj_eq.mp
      (hatV_normalized R _ _ ((stabilizer R _).inv_mem hg))
  rw [map_commutator, Subgroup.map_sup, hmap,
    ← Q_act, ← Z_act, ← Z_act, show act R g (p.walk.getVert i) = p.walk.getVert i from hg,
    ht, ← backward_hatV_eq_forward p hi (by omega) (by omega)] at h
  exact h

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators
