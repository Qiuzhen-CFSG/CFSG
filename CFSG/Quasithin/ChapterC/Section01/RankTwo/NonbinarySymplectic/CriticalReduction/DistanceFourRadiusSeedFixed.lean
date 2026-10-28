module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSeedFixed
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSeedFixed

/-!
# Every radius seed is fixed modulo the full fixed preimage

One actual fixed-radius large-back configuration makes its entire edge
kernel quadratic on the full moving seed. The full-seed displacement
therefore lies in the edge's central seed. Ordinary edge transitivity
transports this inclusion to every edge. It then lies in the full B-group
at each incident original-group vertex, for every radius seed.

This strengthens the seed-fixedness step in MS93 (5.12)(2), printed p.926.
No two-step stabilizer orbit or equality of distinct normal spans is used.
The internal import deliberately reuses the local quadratic-to-edge-omega
proof; no private declaration occurs in the public statement.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- In the actual fixed-radius large-back branch, every full radius seed
is fixed modulo the full B-subgroup by its entire incident edge kernel.
The sharper central edge-seed inclusion is retained as well. -/
theorem Input.replacement_distance_four_radius_seed_fixed
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hlarge : Nat.card F < (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u))
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    ∀ v w c : Vertex d.radical, color d.radical v=false →
      Adjacent d.radical v w → Adjacent d.radical c w →
      ⁅Z d.radical c,Q d.radical w⁆ ≤
        Z d.radical w ⊓ B d.radical v (geometry.Z_normal v) := by
  let t := path.walk.getVert 1
  have hl := path.length_eq_b
  have hat : Adjacent d.radical a t := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  obtain ⟨_,_,hquad,_,_,_⟩ :=
    h.replacement_distance_four_fixed_edge d path hb back hmid hlarge hfixed
  have hedge : ⁅Z d.radical a,Q d.radical t⁆ ≤ Z d.radical t :=
    quadratic_seed_displacement_le_edge h d (by omega) path.start_color hat hquad
  intro v w c hv hvw hcw
  have hcwcol := adjacent_color_ne d.radical hcw
  have hvwcol := adjacent_color_ne d.radical hvw
  have hw : color d.radical w=true := by
    cases hw : color d.radical w
    · exact (hvwcol (hv.trans hw.symm)).elim
    · rfl
  have hc : color d.radical c=false := by
    cases hc : color d.radical c
    · rfl
    · exact (hcwcol (hc.trans hw.symm)).elim
  have hbound : ⁅Z d.radical c,Q d.radical w⁆ ≤ Z d.radical w := by
    obtain ⟨g,hg | hg⟩ := edge_transitive d.radical hat hcw
    · have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hedge
      simpa only [map_commutator,←Z_act,←Q_act,hg.1,hg.2] using hh
    · have hw : color d.radical w=false := by
        rw [←hg.1,action_preserves_color]
        exact path.start_color
      exact (hcwcol (hc.trans hw.symm)).elim
  exact le_inf hbound (hbound.trans ((adjacent_Z_le d.radical hv hvw).trans
    (Escape.EdgeTransfer.Z_le_B (by omega : 2 < geometry.b d.radical) v hv)))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
