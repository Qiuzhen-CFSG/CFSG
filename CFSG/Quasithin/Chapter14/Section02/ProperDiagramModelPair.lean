module
public import Theory.SpecificGroups.PSL3.BorelTwoParabolics
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.BorelOvergroups
public import Theory.SpecificGroups.SymplecticFour.BorelLocalCover
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.MarkedParabolicPair
/-!
# Standard parabolics under a Borel-preserving automorphism

For PSL₃, maximality and Borel-overgroup coverage force a Borel-preserving
automorphism to permute the standard point and line parabolics. For Sp₄,
characteristic two passes through an equivalence of the image parabolic,
and the corresponding local coverage gives the same pair.

Source: Aschbacher–Smith, 14.2.8(3), printed p.983.
-/

public section
open Subgroup Theory.GroupTheory
private theorem core_centralizer_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : centralizer (pCore 2 A : Set A) ≤ pCore 2 A) :
    centralizer (pCore 2 B : Set B) ≤ pCore 2 B := by
  intro b hb
  have hh : e.symm b ∈ centralizer (pCore 2 A : Set A) := by
    intro x hx
    apply e.injective
    have he : e x ∈ pCore 2 B := by
      rw [← pCore_map_iso 2 e]
      exact mem_map_of_mem _ hx
    simpa only [map_mul,e.apply_symm_apply] using hb (e x) he
  rw [← pCore_map_iso 2 e]
  exact ⟨e.symm b,h hh,e.apply_symm_apply b⟩

namespace Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F]
theorem point_parabolic_map_pair_of_borel (a : MulAut (ProjectiveSpecialLinearGroup (Fin 3) F))
    (hB : (borel F).map a.toMonoidHom = borel F) :
    (pointParabolic F).map a.toMonoidHom = pointParabolic F ∨
      (pointParabolic F).map a.toMonoidHom = lineParabolic F := by
  have hp := (projective_parabolics_isCoatom F).1
  have hm := (a.mapSubgroup.isCoatom_iff _).mpr hp
  have hb : borel F ≤ (pointParabolic F).map a.toMonoidHom := by
    rw [← hB]
    apply map_mono
    rw [← projective_parabolics_inf F]
    exact inf_le_left
  rcases BorelOvergroups.overgroup_borel F _ hb hm.ne_top with h | h
  · exact Or.inl ((hm.le_iff_eq hp.ne_top).mp h).symm
  · exact Or.inr ((hm.le_iff_eq (projective_parabolics_isCoatom F).2.ne_top).mp h).symm
theorem line_parabolic_map_pair_of_borel (a : MulAut (ProjectiveSpecialLinearGroup (Fin 3) F))
    (hB : (borel F).map a.toMonoidHom = borel F) :
    (lineParabolic F).map a.toMonoidHom = pointParabolic F ∨
      (lineParabolic F).map a.toMonoidHom = lineParabolic F := by
  have hp := (projective_parabolics_isCoatom F).2
  have hm := (a.mapSubgroup.isCoatom_iff _).mpr hp
  have hb : borel F ≤ (lineParabolic F).map a.toMonoidHom := by
    rw [← hB]
    apply map_mono
    rw [← projective_parabolics_inf F]
    exact inf_le_right
  rcases BorelOvergroups.overgroup_borel F _ hb hm.ne_top with h | h
  · exact Or.inl ((hm.le_iff_eq (projective_parabolics_isCoatom F).1.ne_top).mp h).symm
  · exact Or.inr ((hm.le_iff_eq (projective_parabolics_isCoatom F).2.ne_top).mp h).symm
end Matrix.PSL3.LinearThree

namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
open BorelActionGeometry
theorem point_parabolic_map_pair_of_borel {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n) (a : MulAut (Sp F))
    (hB : borel.map a.toMonoidHom = borel) :
    pointParabolic.map a.toMonoidHom = pointParabolic ∨
      pointParabolic.map a.toMonoidHom = planeParabolic := by
  have hm := (a.mapSubgroup.isCoatom_iff _).mpr pointParabolic_isCoatom
  have hb : borel ≤ pointParabolic.map a.toMonoidHom := by
    rw [← hB]
    exact map_mono inf_le_left
  have hc := core_centralizer_transport (a.subgroupMap pointParabolic)
    (pointParabolic_selfCentralizing_core hF hn)
  rcases borel_overgroup_parabolic_of_characteristicTwo _ hb hc with h | h
  · exact Or.inl ((hm.le_iff_eq pointParabolic_isCoatom.ne_top).mp h).symm
  · exact Or.inr ((hm.le_iff_eq planeParabolic_isCoatom.ne_top).mp h).symm
theorem plane_parabolic_map_pair_of_borel {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n) (a : MulAut (Sp F))
    (hB : borel.map a.toMonoidHom = borel) :
    planeParabolic.map a.toMonoidHom = pointParabolic ∨
      planeParabolic.map a.toMonoidHom = planeParabolic := by
  have hm := (a.mapSubgroup.isCoatom_iff _).mpr planeParabolic_isCoatom
  have hb : borel ≤ planeParabolic.map a.toMonoidHom := by
    rw [← hB]
    exact map_mono inf_le_right
  have hc := core_centralizer_transport (a.subgroupMap planeParabolic)
    (planeParabolic_selfCentralizing_core hF hn)
  rcases borel_overgroup_parabolic_of_characteristicTwo _ hb hc with h | h
  · exact Or.inl ((hm.le_iff_eq pointParabolic_isCoatom.ne_top).mp h).symm
  · exact Or.inr ((hm.le_iff_eq planeParabolic_isCoatom.ne_top).mp h).symm
end Theory.SpecificGroups.SymplecticFour
