module
public import CFSG.Quasithin.Chapter5.Section03UnitaryNativeLift.Models
public import CFSG.Quasithin.Chapter5.Section03UnitaryNativeLift.PairGeometry

/-!
# The geometric inputs for native paired unitary completions

Whole-overlap completions inherit the native five-path action and valences.
They therefore have girth at least eight before any order bound is used.
The actual marked projective reflections lie outside the opposite parabolic;
these facts will produce the common eight-cycle in the paired completion.
The five-dimensional proof uses the full preimage of a projective stabilizer,
not injectivity of the SU₅ projection.

Source: Aschbacher–Smith F.4.5–6 and F.4.16–17, pp.275–277,282–283.
The short wrappers reproduce private geometric steps from the accepted
unitary completion modules while preserving their public boundaries.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter5.UnitaryNativeLift
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry hiding Vertex base
open Subgroup.CosetGeometry.RankTwo SimpleGraph SimpleGraph.PathTransitivePolygon
open ChapterF.SourceCompletion.UnitaryNonbinary

namespace Four
open ChapterF.GreenBook.LieModels.UnitaryFour Theory.SpecificGroups.ClassicalUnitary
private theorem thick (m : ℕ) (hm : 1 ≤ m)
     {M : Type*} [Group M]
    (c : RankTwoAmalgam.FaithfulCompletion (extension m hm).amalgam (G := M))
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (v a b : Vertex c.cosetFamily) :
    ∃ z, (graph c.cosetFamily).Adj v z ∧ z ≠ a ∧ z ≠ b := by
  classical
  have hq : 2 ≤ 2^m := by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hm
  have hc : 2 < Nat.card ((graph c.cosetFamily).neighborSet v) := by
    rw [four_completion_card_neighbors m hm (extension m hm) c hoverlap v]
    cases v.type <;> simp [fourDegree] <;> nlinarith
  have : Finite ((graph c.cosetFamily).neighborSet v) := Nat.finite_of_card_ne_zero (by omega)
  let := Fintype.ofFinite ((graph c.cosetFamily).neighborSet v)
  rw [Nat.card_eq_fintype_card] at hc
  obtain ⟨x,y,z,hxy,hxz,hyz⟩ := Fintype.two_lt_card_iff.mp hc
  by_contra hh
  push Not at hh
  have hx : x.val = a ∨ x.val = b := by
    by_cases ha : x.val = a
    · exact Or.inl ha
    · exact Or.inr (hh x.val x.property ha)
  have hy : y.val = a ∨ y.val = b := by
    by_cases ha : y.val = a
    · exact Or.inl ha
    · exact Or.inr (hh y.val y.property ha)
  have hz : z.val = a ∨ z.val = b := by
    by_cases ha : z.val = a
    · exact Or.inl ha
    · exact Or.inr (hh z.val z.property ha)
  have hxy' : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  have hxz' : x.val ≠ z.val := fun h => hxz (Subtype.ext h)
  have hyz' : y.val ≠ z.val := fun h => hyz (Subtype.ext h)
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    rcases hz with hz | hz <;> simp_all

theorem girth (m : ℕ) (hm : 1 ≤ m) {M : Type*} [Group M]
    (c : RankTwoAmalgam.FaithfulCompletion (extension m hm).amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range = c.middle.range) : Paired.GirthEight c :=
  cycle_bound_of_five_transitive (Paired.graphAction c) (thick m hm c ho)
    (four_completion_rootPathTransitive_five m hm (extension m hm) c ho)
    (·.type) (fun h => h.1)

open UnitaryFourFlag UnitaryFourGeneration
variable (m : ℕ) (hm : 1 ≤ m)
local notation "F" => MatrixField m
local notation "σ" => fieldConj m
local notation "hσ" => fieldConj_involutive m hm
local notation "J" => UnitaryFourFlag.form F σ hσ
theorem point_out : (FourWeyl.point m hm).val ∉ planeParabolic m hm := by
  intro h
  have hh : middleSwap F σ hσ ∈ planeParabolicSU F J :=
    (mem_map_iff_mem (project_injective F J)).mp h
  have hz := (mem_planeParabolicSU F J _).mp hh |>.2.2.1
  simp [middleSwap,middleSwapMatrix,involutionElement] at hz

theorem plane_out : (FourWeyl.plane m hm).val ∉ pointParabolic m hm := by
  intro h
  have hh : pairSwap F σ hσ ∈ pointParabolicSU F J :=
    (mem_map_iff_mem (project_injective F J)).mp h
  have hz := (mem_pointParabolicSU F J _).mp hh |>.1
  simp [pairSwap,pairSwapMatrix,involutionElement] at hz

end Four

namespace Five
private theorem thick (U : ChapterF.GreenBook.UnitaryFive.Model 4)
     {M : Type*} [Group M]
    (c : RankTwoAmalgam.FaithfulCompletion (extension U).amalgam (G := M))
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (v a b : Vertex c.cosetFamily) :
    ∃ z, (graph c.cosetFamily).Adj v z ∧ z ≠ a ∧ z ≠ b := by
  classical
  have hc : 2 < Nat.card ((graph c.cosetFamily).neighborSet v) := by
    rw [five_completion_card_neighbors U (extension U) c hoverlap v]
    cases v.type <;> decide
  have : Finite ((graph c.cosetFamily).neighborSet v) := Nat.finite_of_card_ne_zero (by omega)
  let := Fintype.ofFinite ((graph c.cosetFamily).neighborSet v)
  rw [Nat.card_eq_fintype_card] at hc
  obtain ⟨x,y,z,hxy,hxz,hyz⟩ := Fintype.two_lt_card_iff.mp hc
  by_contra hh
  push Not at hh
  have hx : x.val = a ∨ x.val = b := by
    by_cases ha : x.val = a
    · exact Or.inl ha
    · exact Or.inr (hh x.val x.property ha)
  have hy : y.val = a ∨ y.val = b := by
    by_cases ha : y.val = a
    · exact Or.inl ha
    · exact Or.inr (hh y.val y.property ha)
  have hz : z.val = a ∨ z.val = b := by
    by_cases ha : z.val = a
    · exact Or.inl ha
    · exact Or.inr (hh z.val z.property ha)
  have hxy' : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  have hxz' : x.val ≠ z.val := fun h => hxz (Subtype.ext h)
  have hyz' : y.val ≠ z.val := fun h => hyz (Subtype.ext h)
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    rcases hz with hz | hz <;> simp_all

theorem girth (U : ChapterF.GreenBook.UnitaryFive.Model 4) {M : Type*} [Group M]
    (c : RankTwoAmalgam.FaithfulCompletion (extension U).amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range = c.middle.range) : Paired.GirthEight c :=
  cycle_bound_of_five_transitive (Paired.graphAction c) (thick U c ho)
    (five_completion_rootPathTransitive_five U (extension U) c ho)
    (·.type) (fun h => h.1)

open Theory.SpecificGroups.UnitaryFive SmallCompletion.FivePaths
variable (U : ChapterF.GreenBook.UnitaryFive.Model 4) (t : U.F) (ht : t + U.form.conj t = 1)
private theorem project_mem (W : Submodule U.F (Fin 5 → U.F)) (g : U.form.specialSubgroup) :
    project U.form g∈parabolic U.form W ↔ g∈specialStabilizer U.form W := by
  change g∈((specialStabilizer U.form W).map (project U.form)).comap (project U.form) ↔ _
  rw [Subgroup.comap_map_eq_self (ker_project_le_specialStabilizer U.form W)]

theorem point_out : (FiveWeyl.point U t ht).val∉U.rightParabolic := by
  intro h
  have hh := (project_mem U (Theory.SpecificGroups.UnitaryFive.plane U.F) _).mp h
  have hz := coordinates_plane U.form t _ hh 4 1 (by simp) (by simp)
  rw [coordinates_middleSwap,middle_matrix] at hz
  exact one_ne_zero hz

theorem plane_out : (FiveWeyl.plane U t ht).val∉U.leftParabolic := by
  intro h
  have hh := (project_mem U (line U.F) _).mp h
  have hz := coordinates_line U.form t _ hh 1 (by decide)
  rw [coordinates_pairSwap,pair_matrix] at hz
  exact one_ne_zero hz

end Five
end CFSG.Quasithin.Chapter5.UnitaryNativeLift
