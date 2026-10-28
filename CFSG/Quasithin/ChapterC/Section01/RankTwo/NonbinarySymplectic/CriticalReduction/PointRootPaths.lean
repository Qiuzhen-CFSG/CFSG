module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PointSelectedPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootTrappedPaths

/-!
# Backward paths for full point movers

The selected individual mover and the critical endpoint generate the original
vertex stabilizer. In the root case a trapped neighboring seed therefore has
its full fixed kernel normalized by the residual. The small-radius bound puts
that kernel in B, contradicting the original moving index greater than q.

The argument retains the same original neighbor and selector, its literal
smaller mover, whole edge-Z fixed subgroup, B-relative index and every overlap.
Source: MS93 (5.5), (5.7), printed pp.915--919, the full point-mover branch.
This does not assert a bound on the original or replacement critical distance.
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

/-- The same full point-mover selector gives an actual backward path in
the critical-root case. The B-relative bound excludes the trapped alternative. -/
theorem Input.replacement_large_movement_root_backward_path
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hct : Adjacent d.radical c t)
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c))
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
      (∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = w ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) := by
  have hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hn
    have hidx := (neighbor_seed_join_index_le geometry (by omega) path.start_color hat hct).trans
      (h.replacement_root_neighbor_seed_index_le_cube d path hb hat hct hsmall)
    have hq : 1 < Nat.card F := Finite.one_lt_card
    have hBY := h.replacement_small_radius_le_B d geometry (by omega) path.start_color
      (Z d.radical c ⊔ Z d.radical a) (neighbor_seed_join_le_radius hat hct)
      ((Ltilde_le_stabilizer a).trans hn)
      (lt_of_le_of_lt hidx ((pow_lt_pow_iff_right₀ hq).mpr (by decide)))
    have hone := relIndex_eq_one.mpr (((U_le_Z c).trans le_sup_left).trans hBY)
    rw [hone] at hmove
    exact (not_lt_of_ge hq.le) hmove
  obtain ⟨g,hg,haw,hvw,hindex,htransport,hgen,hfixed,hn,hback⟩ :=
    h.replacement_large_movement_selected_root_at_neighbor d path hb hat hfirst hct
      hnormal hsmall hJm
  refine ⟨g,hg,haw,hvw,hindex,htransport,hgen,hfixed,hn,?_⟩
  rcases hback with hback | htrap
  · exact hback
  · have hres : Ltilde d.radical a ≤
        Subgroup.SmallMover.join (U d.radical (act d.radical g⁻¹ c))
          (Q d.radical (act d.radical g⁻¹ c)) (Q d.radical (act d.radical g⁻¹ t))
          (Nat.card F^2) ⊔ Z d.radical z := by
      rw [←htransport,hgen]
      exact Ltilde_le_stabilizer a
    exact False.elim ((h.replacement_unequal_trapped_root_excluded d path hb haw hvw hn hres
      (hindex ▸ hmove)) htrap.1)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
