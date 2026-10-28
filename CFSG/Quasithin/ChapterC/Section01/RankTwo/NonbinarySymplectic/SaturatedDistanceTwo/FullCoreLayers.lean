module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.WholeSection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.FixedAttachment

/-!
# Full central layers at distance two

The centralizer of an actual critical layer in the opposite whole core lies
in U C_Q(L): a fixed vector outside the natural submodule of the dual cover
would give a quadratic refinement, excluded by the actual critical action.
The common edge omega-center is such a centralizer. Its conjugates under
the endpoint stabilizer generate Z, so Z lies in U C_Q(L) at every endpoint.
Factoring its central involutions then gives Z = U Z_t with the entire
component-fixed attachment retained in the actual incident edge center.

These comparisons hold at the original field degree without an order-q
critical-image premise. They provide the full layers for MS93 (3.7)(2)--(6),
printed pp.873--876, using the dual-cover argument of (1.5)(ii) and (3.4).
They do not collapse the whole core or prove the field restriction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The complete generated Z-layer lies in the natural core with its full
fixed supplement at distance two, before selecting an order-q critical pair. -/
theorem Z_le_moving_sup_fixed_of_distance_two
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a : Vertex d.radical} (ha : color d.radical a = false) :
    Z d.radical a ≤ U d.radical a ⊔ fixedCore d.radical a := by
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := d.radical) (geometry := g) ha
  have hd : (cosetGraph d.radical).dist a z = 2 :=
    path.critical.1.trans ((g.distance_constant _ path.start_color).trans hb)
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two d.radical a z hd
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have hZQ : Z d.radical a ≤ Q d.radical a :=
    (g.omega_bound a ha (by
      rw [g.distance_constant a ha]; change 0 < g.b d.radical; omega)).trans (omegaCenter_le _)
  have hseed : edgeOmega d.radical t ≤ U d.radical a ⊔ fixedCore d.radical a := by
    apply (show edgeOmega d.radical t ≤ Q d.radical a ⊓
      centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) from ?_).trans
      (critical_core_centralizer_le_moving_sup_fixed h d rev hb)
    have hZz : Z d.radical z ≤ Q d.radical t :=
      Z_le_Q_of_dist_lt d.radical z (g.exists_critical z path.end_color) (by
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
          g.distance_constant z path.end_color]
        change 1 < g.b d.radical
        omega)
    refine le_inf ((show edgeOmega d.radical t ≤ Z d.radical a from ?_).trans hZQ)
      (fun x hx y hy => (mem_omegaCenter_iff.mp hx).2.2 y (hZz hy))
    rw [Z,if_pos ha]
    exact le_iSup_of_le t (le_iSup_of_le hat le_rfl)
  have hSL : stabilizer d.radical a ≤ normalizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
    have hh := le_normalizer_map (H := pResidual 2 (stabilizer d.radical a))
      (stabilizer d.radical a).subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hD : stabilizer d.radical a ≤ normalizer
      (fixedCore d.radical a : Set (FreeAmalgam d.radical)) :=
    (le_inf (Q_normalized d.radical a)
      (hSL.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hn := (le_inf (U_normalized a) hD).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)
  rw [Z,if_pos ha]
  apply iSup_le
  intro b
  apply iSup_le
  intro hab
  obtain ⟨u,hu,hub⟩ := stabilizer_transitive_neighbors d.radical a hat hab
  rw [←hub,edgeOmega_act]
  exact (map_mono hseed).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (hn ((stabilizer d.radical a).inv_mem hu)))

/-- The full Z-layer has the actual incident edge center as fixed supplement
at every nonbinary distance-two endpoint. No order-q or Sylow premise is used. -/
theorem Z_eq_moving_sup_edge_of_distance_two
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    Z d.radical a = U d.radical a ⊔ Z d.radical t := by
  have hZX := g.omega_bound a ha (by
    rw [g.distance_constant a ha]; change 0 < g.b d.radical; omega)
  have hUZ : U d.radical a ≤ Z d.radical a := U_le_Z a
  have hUD : U d.radical a ≤ centralizer (fixedCore d.radical a : Set (FreeAmalgam d.radical)) :=
    (hUZ.trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a ha))).trans (centralizer_le inf_le_left)
  apply le_antisymm ?_ (sup_le hUZ (Sp4Four.edge_Z_le_endpoint d.radical ha hat))
  intro x hx
  have hprod := Z_le_moving_sup_fixed_of_distance_two h d g hb ha hx
  rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _
    (hUD.trans (Subgroup.centralizer_le_normalizer _))] at hprod
  obtain ⟨u,hu,v,hv,rfl⟩ := hprod
  have hvX : v ∈ X d.radical a := by
    have hh := (X d.radical a).mul_mem
      ((X d.radical a).inv_mem (hZX (hUZ hu))) (hZX hx)
    simpa only [inv_mul_cancel_left] using hh
  exact mul_mem (mem_sup_left hu) (mem_sup_right
    (replacement_fixed_X_le_edge h d (g := g) (by omega) ha hat ⟨hvX,hv.2⟩))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
