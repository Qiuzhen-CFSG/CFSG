module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.PairedRadical

/-!
# Reversing the source triple commutators in the parabolic branches

Let T be the common full radical and T₀ its component part at an endpoint.
In either saturated parabolic case, [T,T] lies in both endpoint cores.
It therefore centralizes the opposite Z-layer. Together with the already
proved [Z′,T₀,Q] = 1, the three-subgroups identity gives [Z′,Q,T₀] = 1.
This is the second, differently ordered assertion in MS93 (3.7)(1).

The critical commutator [Z,Z′] consequently centralizes T₀ and Q, hence
T = T₀Q. It lies in the actual midpoint omega-center, with its entire
central attachment retained. The paired source theorem applies these
arguments on both sides of the same literal marked radical. It retains
the Sylow case as an explicit alternative; its source exclusion and the
later field restriction are not asserted here.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(1), printed p.873.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition Theory.SpecificGroups.SymplecticFour
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

namespace EdgeMarking
variable {h d} {a z t : Vertex d.radical} (c : EdgeMarking h d a t)

/-- Reverse the order of Q and T₀ using the opposite endpoint kernel.
All commutators are taken in the original free amalgam. -/
theorem opposite_Z_reversed_triple
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (ha : color d.radical a = false) (hz : color d.radical z = false)
    (hZ : Z d.radical z ≤ Q d.radical t)
    (c' : EdgeMarking h d z t) (hab : IsMulCommutative c.action.range) :
    ⁅⁅Z d.radical z,Q d.radical a⁆,componentRadical d a t⁆ = ⊥ := by
  have hab' : IsMulCommutative c'.action.range := c.paired_action_ranges c' ▸ hab
  have h1 : ⁅⁅Q d.radical a,componentRadical d a t⁆,Z d.radical z⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact ((commutator_mono c.core_le_edge inf_le_left).trans
      (c'.full_radical_commutator_le_core hab')).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical z hz)))
  have h2 : ⁅⁅componentRadical d a t,Z d.radical z⁆,Q d.radical a⁆ = ⊥ := by
    rw [commutator_comm (componentRadical d a t)]
    exact (c.opposite_componentRadical_displacement g hb ha (Z d.radical z) hZ hab).2
  exact commutator_commutator_eq_bot_of_rotate h1 h2

end EdgeMarking

omit [Finite H] in
private theorem seed_le_midpoint
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) : Z d.radical a ≤ Q d.radical t := by
  apply Z_le_Q_of_dist_lt d.radical a (g.exists_critical a ha)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hat),
    g.distance_constant a ha]
  change 1 < g.b d.radical
  omega

/-- The complete critical commutator is elementary and central in the
full common radical, hence belongs to its actual omega-center Zₜ. -/
theorem critical_commutator_le_midpoint_Z_of_abelian
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hab : IsMulCommutative c.action.range) :
    ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical t := by
  have hZaT := seed_le_midpoint d g hb path.start_color hat
  have hZzT := seed_le_midpoint d g hb path.end_color hzt
  have hZaQ : Z d.radical a ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical a (g.exists_critical a path.start_color)
    rw [SimpleGraph.dist_self,g.distance_constant a path.start_color]
    change 0 < g.b d.radical
    omega
  have hRa : ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical a := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp
      ((hZzT.trans c.edge_le).trans (Z_normalized d.radical a))
  have hT₀ : ⁅Z d.radical a,Z d.radical z⁆ ≤
      centralizer (componentRadical d a t : Set (FreeAmalgam d.radical)) := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hZaQ).trans
      (commutator_eq_bot_iff_le_centralizer.mp
        (c.opposite_Z_reversed_triple g hb path.start_color path.end_color hZzT c' hab))
  have hQ := hRa.trans (commutator_eq_bot_iff_le_centralizer.mp
    (Z_centralizes_Q d.radical a path.start_color))
  have hcentral : ⁅Z d.radical a,Z d.radical z⁆ ≤
      centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    rw [←c.componentRadical_sup_core g (by omega)]
    exact sup_le (le_centralizer_iff.mp hT₀) (le_centralizer_iff.mp hQ)
  have ht : color d.radical t = true := by
    have hn := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all [path.start_color]
  have hZt : Z d.radical t = omegaCenter (Q d.radical t) := by
    simp [Z,ht,edgeOmega]
  rw [hZt]
  have hZaX := g.omega_bound a path.start_color (by
    rw [g.distance_constant a path.start_color]
    change 0 < g.b d.radical
    omega)
  intro x hx
  exact mem_omegaCenter_iff.mpr ⟨hZaT (hRa hx),
    (mem_omegaCenter_iff.mp (hZaX (hRa hx))).2.1,hcentral hx⟩

/-- Source (3.7)(1) on both sides in the saturated parabolic branches,
together with the midpoint containment of the critical commutator. The
full-Sylow alternative still requires its separate source argument. -/
theorem paired_source_triples_or_sylow
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t) :
    (⁅Z d.radical z,componentRadical d a t⁆ ≤ U d.radical a ∧
      ⁅⁅Z d.radical z,Q d.radical a⁆,componentRadical d a t⁆ = ⊥ ∧
      ⁅Z d.radical a,componentRadical d z t⁆ ≤ U d.radical z ∧
      ⁅⁅Z d.radical a,Q d.radical z⁆,componentRadical d z t⁆ = ⊥ ∧
      ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical t) ∨
      ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) = c.action.range := by
  rcases marked_radical_elementary_or_sylow h d g (by omega) hsat with he | hs
  · left
    let : IsElementaryAbelian 2 c.action.range := c.action_range.symm ▸ he
    let : IsElementaryAbelian 2 c'.action.range := c'.action_range.symm ▸ he
    have hZaT := seed_le_midpoint d g hb path.start_color hat
    have hZzT := seed_le_midpoint d g hb path.end_color hzt
    exact ⟨(c.opposite_componentRadical_displacement g hb path.start_color
        (Z d.radical z) hZzT inferInstance).1,
      c.opposite_Z_reversed_triple g hb path.start_color path.end_color hZzT c' inferInstance,
      (c'.opposite_componentRadical_displacement g hb path.end_color
        (Z d.radical a) hZaT inferInstance).1,
      c'.opposite_Z_reversed_triple g hb path.end_color path.start_color hZaT c inferInstance,
      critical_commutator_le_midpoint_Z_of_abelian h d g hb path hat hzt c c' inferInstance⟩
  · right
    rwa [c.action_range]

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
