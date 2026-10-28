module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusFixedCentrality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexSaturation

/-!
# The actual midpoint span image from its seed budget

Write W = <Z_e^{G_a}> for the literal midpoint e of a critical path.
The equality G_a = L_a Q_a and normalization of Z_e by Q_a give
W <= Vcirc_a join Z_e, without a large critical support path. In the
fixed-radius branch, Vcirc_a centralizes the full B_a. Since Z_e is
abelian, W therefore centralizes the whole Z_e intersect B_a.

The U_e-index budget now bounds the fixed index of W on the original
natural cover at e, and hence its image modulo the full Q_e kernel.
The full Z_e, B_a and fixed attachment remain in the argument; no
whole-span naturality or equality W = Vcirc_a is used.
Source: the first image estimate in the final paragraph of MS93 (5.12),
printed p.927. The preceding source (3) seed-index bound remains explicit.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem midpoint_span_le_moving_sup_seed
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4) :
    localZSpan d.radical (path.walk.getVert 2) a ≤
      Vcirc d.radical a ⊔ Z d.radical (path.walk.getVert 2) := by
  let e := path.walk.getVert 2
  let P := Vcirc d.radical a
  let J := P ⊔ Z d.radical e
  have hl := path.length_eq_b
  have hd : (cosetGraph d.radical).dist a e=2 := path.dist_start (by omega)
  have hZV : Z d.radical e ≤ V d.radical a :=
    (Z_le_localZSpan _ _ _).trans (localZSpan_le_V _ (by rw [SimpleGraph.dist_comm,hd]))
  have hLJ : Ltilde d.radical a ≤ normalizer (J : Set (FreeAmalgam d.radical)) := by
    change Ltilde d.radical a ≤ normalizer ((P ⊔ Z d.radical e : Subgroup _) : Set _)
    rw [sup_comm]
    exact normalizes_sup_of_displacement _ _ _
      ((Ltilde_le_stabilizer a).trans (Vcirc_normalized a))
      (commutator_mono hZV le_rfl)
  have hQJ : Q d.radical a ≤ normalizer (J : Set (FreeAmalgam d.radical)) :=
    (le_inf
      ((show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1).trans
        (Vcirc_normalized a))
      ((Q_le_stabilizer_of_dist_two d.radical a e path.start_color hd).trans
        (Z_normalized d.radical e))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ := vertex_coordinates_with_kernel d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) path.start_color
  have hS : Ltilde d.radical a ⊔ Q d.radical a=stabilizer d.radical a := by
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d geometry (by omega),←MonoidHom.range_eq_map,hir]
  have hSJ : stabilizer d.radical a ≤ normalizer (J : Set (FreeAmalgam d.radical)) :=
    hS ▸ sup_le hLJ hQJ
  apply iSup_le
  intro g
  rw [Z_act]
  exact (map_mono (show Z d.radical e ≤ J from le_sup_right)).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (hSJ ((stabilizer d.radical a).inv_mem g.property)))

/-- The actual full midpoint span has image of order at most q at its
seed vertex whenever the literal seed has B-moving index at most q. -/
theorem Input.replacement_distance_four_root_span_image
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hi : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F) :
    (Q d.radical (path.walk.getVert 2)).relIndex
      (localZSpan d.radical (path.walk.getVert 2) a) ≤ Nat.card F := by
  let e := path.walk.getVert 2
  let W := localZSpan d.radical e a
  let B₀ := B d.radical a (geometry.Z_normal a)
  let A := Z d.radical e ⊓ B₀
  have hl := path.length_eq_b
  have he : color d.radical e=false := (path.vertex_color (by omega)).mpr (by decide)
  have hd : (cosetGraph d.radical).dist a e=2 := path.dist_start (by omega)
  have hWB : W ≤ Vcirc d.radical a ⊔ Z d.radical e :=
    midpoint_span_le_moving_sup_seed h d path hb
  have hPB : Vcirc d.radical a ≤ centralizer (B₀ : Set (FreeAmalgam d.radical)) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (radius_moving_centralizes_full_B geometry (by omega) path.start_color hfixed)
  let := geometry.Z_elementary (by omega) e he
  have hWA : W ≤ centralizer (A : Set (FreeAmalgam d.radical)) :=
    hWB.trans (sup_le (hPB.trans (centralizer_le inf_le_right))
      ((le_centralizer (Z d.radical e)).trans (centralizer_le inf_le_left)))
  have hUC : U d.radical e ⊓ B₀ ≤ centralizer (W : Set (FreeAmalgam d.radical)) :=
    (inf_le_inf (U_le_Z e) le_rfl).trans (le_centralizer_iff.mp hWA)
  let := finite_Z d.radical e
  let : Finite (U d.radical e) :=
    Finite.of_injective (inclusion (U_le_Z e)) (inclusion_injective _)
  have hidx := relIndex_le_of_le_left hUC (L := U d.radical e) index_ne_zero_of_finite
  rw [inf_relIndex_left] at hidx
  have hWQ : W ≤ Q d.radical a :=
    localZSpan_le_Q d.radical path.start_color (by rw [SimpleGraph.dist_comm,hd]) (by omega)
  exact h.replacement_field_fixed_index_image_bound d geometry (by omega) he W
    (hWQ.trans (Q_le_stabilizer_of_dist_two d.radical a e path.start_color hd))
    (hidx.trans hi)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
