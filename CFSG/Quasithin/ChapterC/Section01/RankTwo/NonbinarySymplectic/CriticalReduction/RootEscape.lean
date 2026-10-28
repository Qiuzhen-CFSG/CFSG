module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ShiftedPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusChief
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.IntersectionMovement

/-!
# The exact root alternative to a backward critical shift

Select the actual escaping neighboring conjugate on the characteristic
replacement. If its full seed escapes the penultimate kernel, the native
backward path is constructed with its original overlap. Otherwise the
same seed lies in the truncated radius and hence in the endpoint stabilizer.
The arbitrary-degree comparison gives both critical indices equal to q
and fixed index at least q on the full endpoint intersection. The genuine
(5.2)(iii) and radius-two stabilizer containment supply its normalization
and quadratic action on this same full seed.

This is a proved alternative, not an exclusion of its root case. The
Thompson/parabolic choices in source (5.5)--(5.6) remain to be constructed
before claiming the general source (5.7) selection or its terminal uses.
Source: Meierfrankenfeld--Stellmacher (1993), (3.3), (5.2)(iii), (5.7),
printed pp.867, 915, 919. The trapped-radius consumer is `RadiusTrapping`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- An actual neighboring conjugate either constructs the backward path,
or lies in the penultimate kernel and yields the full quadratic root case.
The intersection in the fixed-index bound includes all central attachments. -/
theorem Input.replacement_backward_path_or_root_escape
    {geometry : Geometry d.radical} {a t z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) :
    ∃ u x, Adjacent d.radical u t ∧ x ∈ stabilizer d.radical a ∧
      Adjacent d.radical a (act d.radical x t) ∧
      Adjacent d.radical (act d.radical x u) (act d.radical x t) ∧
      ((∃ back : CriticalPath d.radical geometry (act d.radical x u)
          (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = act d.radical x t ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∨
      (Z d.radical (act d.radical x u) ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
        ¬ Z d.radical z ≤ normalizer
          ((Z d.radical (act d.radical x u) ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        (Q d.radical z).relIndex (Z d.radical a) = Nat.card F ∧
        (Q d.radical a).relIndex (Z d.radical z) = Nat.card F ∧
        Nat.card F ≤ (centralizer (Z d.radical (act d.radical x u) : Set (FreeAmalgam d.radical))).relIndex
          (Z d.radical z ⊓ Q d.radical a) ∧
        (X d.radical z ⊓ Q d.radical a ≤ normalizer (Z d.radical (act d.radical x u) : Set _)) ∧
        ⁅⁅X d.radical z ⊓ Q d.radical a,Z d.radical (act d.radical x u)⁆,
          Z d.radical (act d.radical x u)⁆ = ⊥)) := by
  obtain ⟨u,hut,_,x,hx,hn⟩ := h.replacement_exists_critical_neighbor_escape d path (by omega) hat
  have hxa : act d.radical x a = a := hx
  have hatx : Adjacent d.radical a (act d.radical x t) := by
    rw [←hxa]
    exact (adjacent_act_iff d.radical x _ _).mpr hat
  have hutx := (adjacent_act_iff d.radical x _ _).mpr hut
  rw [Subgroup.map_sup,←Z_act d.radical x u,←Z_act d.radical x a,hxa] at hn
  refine ⟨u,x,hut,hx,hatx,hutx,?_⟩
  by_cases hk : Z d.radical (act d.radical x u) ≤
      Q d.radical (path.walk.getVert (path.walk.length-2))
  · right
    let Y := Z d.radical (act d.radical x u)
    have hYV : Y ≤ V d.radical a := le_sup_left.trans (neighbor_seed_join_le_radius hatx hutx)
    have hYZ : Y ≤ stabilizer d.radical z :=
      (le_inf hYV hk).trans (truncated_radius_le_endpoint_stabilizer path (by omega))
    have hYQ := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
    obtain ⟨hi,hi'⟩ := h.replacement_critical_indices_eq_field_of_seed_escape d path
      (by omega) Y hYZ hYQ hn
    have hindex := h.replacement_seed_actor_centralizer_index_ge_field d path (by omega)
      Y hYZ hYQ hn Y le_rfl hYZ
    have hcolor : color d.radical (act d.radical x u) = false := by
      have hne₁ := adjacent_color_ne d.radical hatx
      have hne₂ := adjacent_color_ne d.radical hutx
      rw [path.start_color] at hne₁
      cases ht : color d.radical (act d.radical x t) <;>
        cases hu : color d.radical (act d.radical x u) <;> simp_all
    have hAY : X d.radical z ⊓ Q d.radical a ≤ normalizer (Y : Set _) :=
      (inf_le_right.trans (Q_le_stabilizer_of_dist_le_two a (act d.radical x u)
        path.start_color hcolor (by rw [SimpleGraph.dist_comm]; exact neighbor_distance_le_two hatx hutx))).trans
        (Z_normalized d.radical (act d.radical x u))
    have htrip := (h.replacement_radius_commutator_bounds d geometry hb path.start_color z
      (path.walk.getVert (path.walk.length-2))).2
    exact ⟨hk,hn,hi,hi',hindex,hAY,le_bot_iff.mp
      ((commutator_mono (commutator_mono le_rfl (le_inf hYV hk)) (le_inf hYV hk)).trans_eq htrip)⟩
  · exact Or.inl (exists_backward_path_of_not_le geometry (by omega) path hatx hutx hk)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
