module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFixedSeedBudget
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourOriginalResidualSpan

/-!
# General fixed-radius b4 endgame data

The actual critical path itself supplies both oriented field-sized seed
indices. With an actual midpoint orbit selector, the literal original
residual is exactly the midpoint-span commutator and the moving radius. Its
root fixed-preimage index is at most q, and its midpoint intersection retains
the entire original derived subgroup. This is the source (3.10)(i) bridge with the
original Q-kernels and full fixed preimages retained.
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

/-- The original path and actual midpoint orbit now carry the complete
fixed-radius source continuation, including exact Q0 identification. -/
theorem Input.replacement_distance_four_general_b4_endgame
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (path.walk.getVert 2))
    (hga : act d.radical g a=z)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    let e := path.walk.getVert 2
    let Q₀ := ⁅Q d.radical a,Ltilde d.radical a⁆
    let W := localZSpan d.radical e a
    (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical e)=Nat.card F ∧
      (B d.radical e (geometry.Z_normal e)).relIndex (U d.radical z)=Nat.card F ∧
      Q₀=⁅W,Ltilde d.radical a⁆ ∧ Q₀=Vcirc d.radical a ∧
      (commutatorPreimage Q₀ (Z d.radical z) (U d.radical a)).relIndex Q₀ ≤ Nat.card F ∧
      (Q d.radical e).relIndex Q₀ ≤ Nat.card F ∧
      ⁅Q₀,Q₀⁆=⁅W,W⁆ ∧ Nat.card (⁅Q₀,Q₀⁆ : Subgroup (FreeAmalgam d.radical)) ≤ Nat.card F ∧
      ⁅Q₀ ⊓ Q d.radical e,Q₀ ⊓ Q d.radical e⁆=⁅Q₀,Q₀⁆ ∧
      distanceFourRootSpanWhole geometry a e z n := by
  let e := path.walk.getVert 2
  let Q₀ := ⁅Q d.radical a,Ltilde d.radical a⁆
  let W := localZSpan d.radical e a
  have hfirst := h.replacement_distance_four_fixed_path_seed_index d path hb hfixed
  have hlast := h.replacement_distance_four_fixed_path_terminal_seed_index d path hb hfixed
  have hq := h.replacement_distance_four_original_residual_eq_span_commutator d path hb
    g hg hga hfixed hfirst.le hlast.le
  have hres := h.replacement_distance_four_residual_terminal_fixed_index d path hb
    g hg hga hfixed hfirst.le hlast.le
  have hwhole := h.replacement_distance_four_root_span_whole d path hb
    g hg hga hfixed hfirst.le hlast.le
  obtain ⟨hder,hcard,hstable⟩ := h.replacement_distance_four_original_residual_derived d path hb
    g hg hga hfixed hfirst.le hlast.le
  have himage := h.replacement_distance_four_residual_image d path hb hfixed hfirst.le
  have hl := path.length_eq_b
  have hWV : W ≤ V d.radical a := localZSpan_le_V d.radical (by
    rw [SimpleGraph.dist_comm,path.dist_start (by omega)])
  have hQcirc : Q₀=Vcirc d.radical a := le_antisymm
    (hq.le.trans (commutator_mono hWV le_rfl))
    (commutator_mono (geometry.V_le_Q (by omega) a path.start_color) le_rfl)
  exact ⟨hfirst,hlast,hq,hQcirc,hres.2,himage,hder,hcard,hstable _ himage,hwhole⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
