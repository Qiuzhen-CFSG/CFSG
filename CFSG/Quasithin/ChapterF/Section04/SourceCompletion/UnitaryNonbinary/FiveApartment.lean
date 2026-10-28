module
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FiveFixed
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FixedApartment
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FiveGeometry
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FiveWeyl

/-!
# Closing the marked apartment for full PSU₅(4) extensions

The SU₅ split-torus calculations descend through the actual projective
quotient: the scalar kernel fixes both subspaces, so their exact stabilizers
are full preimages. Native fixed-neighbor separation transfers to every
full-extension completion with the whole overlap. Its proved quadrangle
metric closes the marked apartment and makes the rotation's fourth power
lie in the whole middle, with square one.

This retains field sixteen, unitary parameter four, scalar kernel five,
and every outer factor. Eliminating the remaining outer involution and
recognizing the projective group remain necessary. Source: Aschbacher–Smith
F.4.10,16–17,24, printed pp.279,282–283,287 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FiveWeyl
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.UnitaryFive
open SmallCompletion.FivePaths
variable (U : GreenBook.UnitaryFive.Model 4) (t : U.F) (ht : t + U.form.conj t=1)
local notation "K" => FixedBy.subfield U.F U.form.conj

def splitTorus (p : Kˣ × Kˣ) : (U.leftParabolic ⊓ U.rightParabolic : Subgroup U.Carrier) :=
  ⟨project U.form (SmallCompletion.FiveFixed.torus U.form t ht U.matrix p.1 p.2),
    ⟨⟨_,(SmallCompletion.FiveFixed.torus_mem U.form t ht U.matrix p.1 p.2).1,rfl⟩,
      ⟨_,(SmallCompletion.FiveFixed.torus_mem U.form t ht U.matrix p.1 p.2).2,rfl⟩⟩⟩

private theorem project_mem (W : Submodule U.F (Fin 5 → U.F)) (g : U.form.specialSubgroup) :
    project U.form g∈parabolic U.form W ↔ g∈specialStabilizer U.form W := by
  change g∈((specialStabilizer U.form W).map (project U.form)).comap (project U.form) ↔ _
  rw [Subgroup.comap_map_eq_self (ker_project_le_specialStabilizer U.form W)]

private theorem point_torus (p : Kˣ × Kˣ) :
    (point U t ht).val*(splitTorus U t ht p).val*(point U t ht).val=
      (splitTorus U t ht (p.1,p.2⁻¹)).val := by
  change project U.form _ * project U.form _ * project U.form _ = project U.form _
  rw [←map_mul,←map_mul,SmallCompletion.FiveFixed.point_torus]

private theorem plane_torus (p : Kˣ × Kˣ) :
    (plane U t ht).val*(splitTorus U t ht p).val*(plane U t ht).val=
      (splitTorus U t ht (p.2,p.1)).val := by
  change project U.form _ * project U.form _ * project U.form _ = project U.form _
  rw [←map_mul,←map_mul,SmallCompletion.FiveFixed.plane_torus]

private theorem point_out : (point U t ht).val∉U.rightParabolic := by
  intro h
  have hh := (project_mem U (Theory.SpecificGroups.UnitaryFive.plane U.F) _).mp h
  have hz := coordinates_plane U.form t _ hh 4 1 (by simp) (by simp)
  rw [coordinates_middleSwap,middle_matrix] at hz
  exact one_ne_zero hz

private theorem plane_out : (plane U t ht).val∉U.leftParabolic := by
  intro h
  have hh := (project_mem U (line U.F) _).mp h
  have hz := coordinates_line U.form t _ hh 1 (by decide)
  rw [coordinates_pairSwap,pair_matrix] at hz
  exact one_ne_zero hz

private theorem fixed_cosets (i : Bool)
    (g : SourceExtension.nativeFamily (P₀ := U.leftParabolic) (P₁ := U.rightParabolic) i)
    (hfix : ∀ p,g.val⁻¹*(splitTorus U t ht p).val*g.val∈U.leftParabolic ⊓ U.rightParabolic) :
    g.val∈U.leftParabolic ⊓ U.rightParabolic ∨
      (if i then (plane U t ht).val else (point U t ht).val)*g.val∈U.leftParabolic ⊓ U.rightParabolic := by
  have hq : 2 < Nat.card K := by
    change 2 < Nat.card {x : U.F // U.form.conj x=x}
    rw [fixed_card_four U.form U.card U.conjugation]
    decide
  obtain ⟨a,ha⟩ := project_surjective U.form g.val
  have hf (x y : Kˣ) : a⁻¹*SmallCompletion.FiveFixed.torus U.form t ht U.matrix x y*a∈
      specialStabilizer U.form (line U.F) ⊓ specialStabilizer U.form (Theory.SpecificGroups.UnitaryFive.plane U.F) := by
    have hh := hfix (x,y)
    rw [←ha] at hh
    change (project U.form a)⁻¹ * project U.form _ * project U.form a∈_ at hh
    rw [←map_inv,←map_mul,←map_mul] at hh
    exact ⟨(project_mem U _ _).mp hh.1,(project_mem U _ _).mp hh.2⟩
  have send (z : U.form.specialSubgroup)
      (hz : z∈specialStabilizer U.form (line U.F) ⊓ specialStabilizer U.form (Theory.SpecificGroups.UnitaryFive.plane U.F)) :
      project U.form z∈U.leftParabolic ⊓ U.rightParabolic :=
    ⟨⟨z,hz.1,rfl⟩,⟨z,hz.2,rfl⟩⟩
  cases i
  · have hg : a∈specialStabilizer U.form (line U.F) := (project_mem U _ _).mp (ha.symm ▸ g.property)
    rcases SmallCompletion.FiveFixed.point_fixed_coset U.form t ht U.matrix hq a hg hf with h | h
    · exact Or.inl (ha ▸ send a h)
    · right
      have hh := send _ h
      rw [map_mul,ha] at hh
      exact hh
  · have hg : a∈specialStabilizer U.form (Theory.SpecificGroups.UnitaryFive.plane U.F) :=
      (project_mem U _ _).mp (ha.symm ▸ g.property)
    rcases SmallCompletion.FiveFixed.plane_fixed_coset U.form t ht U.matrix hq a hg hf with h | h
    · exact Or.inl (ha ▸ send a h)
    · right
      have hh := send _ h
      rw [map_mul,ha] at hh
      exact hh

/-- The actual PSU₅(4) split-torus apartment closes in the full marked
completion. The projective scalar kernel and all outer factors are retained. -/
theorem fourth_mem_middle (E : FiveExtension U) {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hcard : Nat.card M≤Nat.card E.carrier) : rotation U t ht E c ^ 4∈c.middle.range := by
  have hgeo := five_completion_quadrangle U E c ho hcard
  exact E.nativeRotation_four_mem_middle c (splitTorus U t ht) (five_conj_injective U) ho
    (point U t ht) (plane U t ht) (point_sq U t ht) (plane_sq U t ht)
    (point_out U t ht) (plane_out U t ht)
    (fun p => ⟨(p.1,p.2⁻¹),point_torus U t ht p⟩)
    (fun p => ⟨(p.2,p.1),plane_torus U t ht p⟩)
    (fixed_cosets U t ht false) (fixed_cosets U t ht true) hgeo.2.1 hgeo.1

/-- Apartment closure and native centralizer control give eighth power one;
the possible outer involutory fourth power remains explicit. -/
theorem eighth_eq_one (E : FiveExtension U) {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hcard : Nat.card M≤Nat.card E.carrier) : rotation U t ht E c ^ 8=1 := by
  have hh := power_sq_eq_one_of_middle U t ht E c 4 (fourth_mem_middle U t ht E c ho hcard)
  simpa only [←pow_mul] using hh
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FiveWeyl
