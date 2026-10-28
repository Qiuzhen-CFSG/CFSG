module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.ComponentIntersection

/-!
# Paired whole-radical commutators

The saturated marked radical is a point radical, a plane radical or a
full Sylow subgroup. In the first two cases its abelian image puts the
derived subgroup of the common full radical in both endpoint cores.
Since T₀ ∩ Q = U, each component radical then moves the opposite whole
critical Z-layer into U. Each complete fixed attachment centralizes its
own T₀; its displacement under the opposite T₀ lies in the opposite U
and in its own full-core Frattini subgroup.

These are the parabolic-branch comparisons beginning MS93 (3.7)(1),
printed p.873. The Sylow alternative is retained explicitly. The reversed
triple commutator in that source clause, equality of the paired fixed
kernels and the field restriction are not asserted here.
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
include h

/-- Both parabolic images are elementary abelian; the full Sylow case is
retained as its literal subgroup alternative. -/
theorem marked_radical_elementary_or_sylow
    (g : Geometry d.radical) (hb : 0 < g.b d.radical)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical) :
    IsElementaryAbelian 2 ((d.ambient.subgroupOf K).map (componentProjection h)) ∨
      ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
        (d.ambient.subgroupOf K).map (componentProjection h) := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  rcases marked_radical_alternatives h d g hb hsat with ⟨u,hu⟩ | hs
  · left
    let D := (d.ambient.subgroupOf K).map (componentProjection h)
    let : IsElementaryAbelian 2 (D.map (MulAut.conj u).toMonoidHom) := by
      rcases hu with ⟨he,_⟩ | ⟨he,_⟩
      · rw [he]
        exact SymplecticConjugatePair.pointRadical_elementary
      · rw [he]
        exact SymplecticConjugatePair.planeRadical_elementary
    let e := D.equivMapOfInjective (MulAut.conj u).toMonoidHom (MulAut.conj u).injective
    exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  · exact Or.inr hs

namespace EdgeMarking
variable {h d} {a t : Vertex d.radical} (c : EdgeMarking h d a t)

omit [Finite F] [CharP F 2] in
/-- In an abelian marked image, all full-radical commutators lie in the
entire endpoint core. -/
theorem full_radical_commutator_le_core
    (hab : IsMulCommutative c.action.range) :
    ⁅Q d.radical t,Q d.radical t⁆ ≤ Q d.radical a := by
  have hker : ⁅(⊤ : Subgroup (Q d.radical t)),⊤⁆ ≤ c.action.ker := by
    change ⁅(⊤ : Subgroup (Q d.radical t)),⊤⁆ ≤ (⊥ : Subgroup (Sp F)).comap c.action
    rw [←map_le_iff_le_comap,map_commutator,←MonoidHom.range_eq_map]
    exact (commutator_self_eq_bot_iff.mpr hab).le
  have hh := map_mono (f := (Q d.radical t).subtype) hker
  rwa [map_commutator,←MonoidHom.range_eq_map,range_subtype,c.action_kernel,
    map_subgroupOf_eq_of_le c.core_le_edge] at hh

omit h [Field F] [Finite H] [Finite F] [CharP F 2] in
/-- The complete fixed attachment centralizes T₀, not just its elementary part. -/
theorem fixedCore_centralizes_componentRadical :
    ⁅fixedCore d.radical a,componentRadical d a t⁆ = ⊥ :=
  commutator_eq_bot_iff_le_centralizer.mpr
    (inf_le_right.trans (centralizer_le inf_le_right))

/-- The opposite whole Z-layer is moved into U by T₀ when the full
radical image is abelian. The resulting displacement centralizes Q. -/
theorem opposite_componentRadical_displacement
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (ha : color d.radical a = false) (B : Subgroup (FreeAmalgam d.radical))
    (hB : B ≤ Q d.radical t) (hab : IsMulCommutative c.action.range) :
    ⁅B,componentRadical d a t⁆ ≤ U d.radical a ∧
      ⁅⁅B,componentRadical d a t⁆,Q d.radical a⁆ = ⊥ := by
  have hN := le_normalizer_iff_commutator_le_right.mp
    (hB.trans c.componentRadical_normalized)
  have hQ := (commutator_mono hB (show componentRadical d a t ≤ Q d.radical t from inf_le_left)).trans
    (c.full_radical_commutator_le_core hab)
  have hU := (le_inf hN hQ).trans_eq (c.componentRadical_inf_core g hb ha)
  exact ⟨hU,commutator_eq_bot_iff_le_centralizer.mpr
    ((hU.trans (U_le_Z a)).trans
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha)))⟩

end EdgeMarking

/-- In the two parabolic branches the same full-radical derived subgroup
lies in both exact cores. Each T₀ moves the opposite full critical layer
into its own natural core. The Sylow branch is not discarded. -/
theorem paired_componentRadical_displacement_or_sylow
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t) :
    (⁅Q d.radical t,Q d.radical t⁆ ≤ Q d.radical a ⊓ Q d.radical z ∧
      ⁅Z d.radical z,componentRadical d a t⁆ ≤ U d.radical a ∧
      ⁅⁅Z d.radical z,componentRadical d a t⁆,Q d.radical a⁆ = ⊥ ∧
      ⁅Z d.radical a,componentRadical d z t⁆ ≤ U d.radical z ∧
      ⁅⁅Z d.radical a,componentRadical d z t⁆,Q d.radical z⁆ = ⊥) ∨
    ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) = c.action.range := by
  rcases marked_radical_elementary_or_sylow h d g (by omega) hsat with he | hs
  · left
    let : IsElementaryAbelian 2 c.action.range := c.action_range.symm ▸ he
    let : IsElementaryAbelian 2 c'.action.range := c'.action_range.symm ▸ he
    have hZa : Z d.radical a ≤ Q d.radical t :=
      Z_le_Q_of_dist_lt d.radical a (g.exists_critical a path.start_color) (by
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hat),
          g.distance_constant a path.start_color]
        change 1 < g.b d.radical
        omega)
    have hZz : Z d.radical z ≤ Q d.radical t :=
      Z_le_Q_of_dist_lt d.radical z (g.exists_critical z path.end_color) (by
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
          g.distance_constant z path.end_color]
        change 1 < g.b d.radical
        omega)
    obtain ⟨ha,ha'⟩ := c.opposite_componentRadical_displacement g hb path.start_color
      (Z d.radical z) hZz inferInstance
    obtain ⟨hz,hz'⟩ := c'.opposite_componentRadical_displacement g hb path.end_color
      (Z d.radical a) hZa inferInstance
    exact ⟨le_inf (c.full_radical_commutator_le_core inferInstance)
      (c'.full_radical_commutator_le_core inferInstance),ha,ha',hz,hz'⟩
  · right
    rwa [c.action_range]

/-- The two whole fixed attachments can move under the opposite T₀ only
inside both its natural core and their own Frattini subgroup. This retains
the complete non-elementary attachments. The Sylow case remains explicit. -/
theorem paired_full_fixedCore_displacement_or_sylow
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t) :
    (⁅fixedCore d.radical a,componentRadical d z t⁆ ≤
        U d.radical z ⊓ (frattini (Q d.radical a)).map (Q d.radical a).subtype ∧
      ⁅fixedCore d.radical z,componentRadical d a t⁆ ≤
        U d.radical a ⊓ (frattini (Q d.radical z)).map (Q d.radical z).subtype) ∨
    ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) = c.action.range := by
  rcases marked_radical_elementary_or_sylow h d g (by omega) hsat with he | hs
  · left
    let : IsElementaryAbelian 2 c.action.range := c.action_range.symm ▸ he
    let : IsElementaryAbelian 2 c'.action.range := c'.action_range.symm ▸ he
    constructor
    · refine le_inf ?_ ?_
      · exact (c'.opposite_componentRadical_displacement g hb path.end_color
          (fixedCore d.radical a) (inf_le_left.trans c.core_le_edge) inferInstance).1
      · exact (commutator_mono le_rfl inf_le_left).trans
          (fixedCore_displacement_le_frattini h d g hb path.start_color c)
    · refine le_inf ?_ ?_
      · exact (c.opposite_componentRadical_displacement g hb path.start_color
          (fixedCore d.radical z) (inf_le_left.trans c'.core_le_edge) inferInstance).1
      · exact (commutator_mono le_rfl inf_le_left).trans
          (fixedCore_displacement_le_frattini h d g hb path.end_color c')
  · right
    rwa [c.action_range]

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
