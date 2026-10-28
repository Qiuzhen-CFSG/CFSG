module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PointSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootEscape
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.PairedChoice

/-!
# Selected paths in the full point-mover root branch

The point-radical selector uses one residual conjugator for every actual
neighboring mover. Transporting it through the graph's right action retains
the prescribed neighbor's full mover, its exact U-index modulo B, whole
stabilizer generation and the fixed subgroup on the full original edge Z.
If the endpoint normalized the selected seed join, generation would make
the original nonnormal neighbor join locally normal. Thus the selected
neighbor either supplies an overlapping backward critical path or the
full trapped-root obstruction, with both critical indices equal to q and
quadratic action on the same full seed. MS3 supplies a nonnormal neighbor
in the final application.

This settles the large-movement, field-sized-endpoint selection subcase
of MS93 (5.5)--(5.7), printed pp.915--919. The trapped-root case remains
explicit; the backward path has the original critical distance. No strict
B-index bound is inferred from nonnormality.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Apply the point selector to any prescribed nonnormal neighbor.
The same conjugator preserves its exact U-index modulo the full B preimage. -/
theorem Input.replacement_large_movement_selected_root_at_neighbor
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hct : Adjacent d.radical c t)
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hJm : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a)) :
    ∃ g ∈ Ltilde d.radical a,
      let w := act d.radical g⁻¹ t
      let v := act d.radical g⁻¹ c
      let J := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2)
      Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
      (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) =
        (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ∧
      J.map (MulAut.conj g).toMonoidHom = Subgroup.SmallMover.join
        (U d.radical v) (Q d.radical v) (Q d.radical w) (Nat.card F^2) ∧
      J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z = stabilizer d.radical a ∧
      Z d.radical t ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      ¬ Z d.radical z ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ((∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = w ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∨
      (Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
        (Q d.radical z).relIndex (Z d.radical a) = Nat.card F ∧
        (Q d.radical a).relIndex (Z d.radical z) = Nat.card F ∧
        Nat.card F ≤ (centralizer (Z d.radical v : Set (FreeAmalgam d.radical))).relIndex
          (Z d.radical z ⊓ Q d.radical a) ∧
        X d.radical z ⊓ Q d.radical a ≤ normalizer (Z d.radical v : Set _) ∧
        ⁅⁅X d.radical z ⊓ Q d.radical a,Z d.radical v⁆,Z d.radical v⁆ = ⊥)) := by
  obtain ⟨g,hg,hall⟩ := h.replacement_large_movement_root_selection d path hb hat hfirst hsmall hJm
  obtain ⟨hgen,hfixed⟩ := hall c hct
  let S := stabilizer d.radical a
  let w := act d.radical g⁻¹ t
  let v := act d.radical g⁻¹ c
  let J := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)
  have hgS : g ∈ S := Ltilde_le_stabilizer a hg
  have hga : act d.radical g⁻¹ a = a := S.inv_mem hgS
  have haw : Adjacent d.radical a w := by
    rw [←hga]
    exact (adjacent_act_iff d.radical g⁻¹ _ _).mpr hat
  have hvw : Adjacent d.radical v w := (adjacent_act_iff d.radical g⁻¹ _ _).mpr hct
  have hJw : J.map (MulAut.conj g).toMonoidHom ≤ Q d.radical w := by
    simpa only [w,Q_act,inv_inv] using map_mono (f := (MulAut.conj g).toMonoidHom)
      (Subgroup.SmallMover.join_le (U d.radical c) (Q d.radical c) (Q d.radical t) (Nat.card F^2))
  have hn : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hbad
    have hwhole : S ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
      change stabilizer d.radical a ≤ _
      rw [←hgen]
      exact sup_le (hJw.trans (edge_normalizes_neighbor_seed_join haw hvw)) hbad
    have hZa : (Z d.radical a).map (MulAut.conj g⁻¹).toMonoidHom = Z d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a (S.inv_mem hgS))
    have hZv : (Z d.radical v).map (MulAut.conj g⁻¹).toMonoidHom = Z d.radical c := by
      rw [show Z d.radical v = (Z d.radical c).map (MulAut.conj g).toMonoidHom by
        simp only [v,Z_act,inv_inv],Subgroup.map_map]
      have hh : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
          MonoidHom.id (FreeAmalgam d.radical) := by
        apply MonoidHom.ext
        intro x
        change g⁻¹*(g*x*g⁻¹)*(g⁻¹)⁻¹=x
        group
      rw [hh,Subgroup.map_id]
    have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hwhole
    have hS : S.map (MulAut.conj g⁻¹).toMonoidHom = S :=
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer (S.inv_mem hgS))
    rw [map_normalizer_eq_of_bijective _ (MulAut.conj g⁻¹).bijective,
      Subgroup.map_sup,hZv,hZa,hS] at hm
    exact hnormal hm
  have hindex := movingIndex_act geometry (d := c) (by omega) path.start_color g⁻¹ (S.inv_mem hgS)
  have htransport : J.map (MulAut.conj g).toMonoidHom = Subgroup.SmallMover.join
      (U d.radical v) (Q d.radical v) (Q d.radical w) (Nat.card F^2) := by
    dsimp only [v,w]
    rw [U_act,Q_act,Q_act,inv_inv,←Subgroup.SmallMover.join_map _ (MulAut.conj g).injective]
  refine ⟨g,hg,haw,hvw,hindex,htransport,hgen,hfixed,hn,?_⟩
  by_cases hk : Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2))
  · right
    have hYV : Z d.radical v ≤ V d.radical a :=
      le_sup_left.trans (neighbor_seed_join_le_radius haw hvw)
    have hYS : Z d.radical v ≤ stabilizer d.radical z :=
      (le_inf hYV hk).trans (truncated_radius_le_endpoint_stabilizer path (by omega))
    have hYQ := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
    obtain ⟨hi,hi'⟩ := h.replacement_critical_indices_eq_field_of_seed_escape d path
      (by omega) (Z d.radical v) hYS hYQ hn
    have hindex := h.replacement_seed_actor_centralizer_index_ge_field d path (by omega)
      (Z d.radical v) hYS hYQ hn (Z d.radical v) le_rfl hYS
    have hcolor : color d.radical v = false := by
      have hn₁ := adjacent_color_ne d.radical haw
      have hn₂ := adjacent_color_ne d.radical hvw
      rw [path.start_color] at hn₁
      cases ht : color d.radical w <;> cases hv : color d.radical v <;> simp_all
    have hAY : X d.radical z ⊓ Q d.radical a ≤ normalizer (Z d.radical v : Set _) :=
      (inf_le_right.trans (Q_le_stabilizer_of_dist_le_two a v path.start_color hcolor
        (by rw [SimpleGraph.dist_comm]; exact neighbor_distance_le_two haw hvw))).trans
          (Z_normalized d.radical v)
    have htrip := (h.replacement_radius_commutator_bounds d geometry hb path.start_color z
      (path.walk.getVert (path.walk.length-2))).2
    exact ⟨hk,hi,hi',hindex,hAY,le_bot_iff.mp
      ((commutator_mono (commutator_mono le_rfl (le_inf hYV hk)) (le_inf hYV hk)).trans_eq htrip)⟩
  · exact Or.inl (exists_backward_path_of_not_le geometry (by omega) path haw hvw hk)

/-- The actual one-root point selector yields a neighboring seed which
either gives the overlapping backward path or the full trapped-root case.
MS3 supplies the nonnormal neighboring seed internally. -/
theorem Input.replacement_large_movement_selected_root_alternative
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hJm : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a)) :
    ∃ c, Adjacent d.radical c t ∧ ∃ g ∈ Ltilde d.radical a,
      let w := act d.radical g⁻¹ t
      let v := act d.radical g⁻¹ c
      let J := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2)
      Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
      (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) =
        (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ∧
      J.map (MulAut.conj g).toMonoidHom = Subgroup.SmallMover.join
        (U d.radical v) (Q d.radical v) (Q d.radical w) (Nat.card F^2) ∧
      J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z = stabilizer d.radical a ∧
      Z d.radical t ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      ¬ Z d.radical z ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ((∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = w ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∨
      (Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
        (Q d.radical z).relIndex (Z d.radical a) = Nat.card F ∧
        (Q d.radical a).relIndex (Z d.radical z) = Nat.card F ∧
        Nat.card F ≤ (centralizer (Z d.radical v : Set (FreeAmalgam d.radical))).relIndex
          (Z d.radical z ⊓ Q d.radical a) ∧
        X d.radical z ⊓ Q d.radical a ≤ normalizer (Z d.radical v : Set _) ∧
        ⁅⁅X d.radical z ⊓ Q d.radical a,Z d.radical v⁆,Z d.radical v⁆ = ⊥)) := by
  obtain ⟨c,hct,hnormal,_⟩ := h.replacement_exists_critical_neighbor_escape d path (by omega) hat
  exact ⟨c,hct,h.replacement_large_movement_selected_root_at_neighbor d path hb hat hfirst hct hnormal hsmall hJm⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
