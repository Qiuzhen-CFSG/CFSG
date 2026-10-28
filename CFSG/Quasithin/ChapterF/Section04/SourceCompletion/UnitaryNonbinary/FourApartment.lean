module
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourFixed
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FixedApartment
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FourGeometry
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FourWeyl

/-!
# Closing the marked apartment for full PSU₄ extensions

The native split torus and its two fixed-neighbor calculations descend
through the actual injective SU₄ projection. They transfer to the full
completion, where the proved quadrangle metric closes the marked apartment.
Thus the fourth rotation power belongs to the whole overlap, and its square
is one by the native Borel centralizer calculation. Both q = 4 and even
outer degree remain included.

The possible outer involution is retained: this is apartment closure, not
PSU recognition. Source: Aschbacher–Smith F.4.10,16–17,24,
printed pp.279,282–283,287 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FourWeyl
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourGeneration
variable (m : ℕ) (hm : 1 ≤ m)
local notation "F" => MatrixField m
local notation "σ" => fieldConj m
local notation "hσ" => fieldConj_involutive m hm
local notation "K" => PointLocal.FixedField m
local notation "J" => UnitaryFourFlag.form F σ hσ
local notation "π" => project F J

def splitTorus (p : Kˣ × Kˣ) :
    (pointParabolic m hm ⊓ planeParabolic m hm : Subgroup (ProjectiveGroup m hm)) :=
  ⟨π (SmallCompletion.FourFixed.torus F σ hσ p.1 p.2).val,
    ⟨⟨_,(SmallCompletion.FourFixed.torus F σ hσ p.1 p.2).property.1,rfl⟩,
      ⟨_,(SmallCompletion.FourFixed.torus F σ hσ p.1 p.2).property.2,rfl⟩⟩⟩

private theorem point_torus (p : Kˣ × Kˣ) :
    (point m hm).val*(splitTorus m hm p).val*(point m hm).val=
      (splitTorus m hm (p.1,p.2⁻¹)).val := by
  change π _ * π _ * π _ = π _
  rw [←map_mul,←map_mul,SmallCompletion.FourFixed.point_torus]

private theorem plane_torus (p : Kˣ × Kˣ) :
    (plane m hm).val*(splitTorus m hm p).val*(plane m hm).val=
      (splitTorus m hm (p.2,p.1)).val := by
  change π _ * π _ * π _ = π _
  rw [←map_mul,←map_mul,SmallCompletion.FourFixed.plane_torus]

private theorem point_out : (point m hm).val ∉ planeParabolic m hm := by
  intro h
  have hh : middleSwap F σ hσ ∈ planeParabolicSU F J :=
    (mem_map_iff_mem (project_injective F J)).mp h
  have hz := (mem_planeParabolicSU F J _).mp hh |>.2.2.1
  simp [middleSwap,middleSwapMatrix,involutionElement] at hz

private theorem plane_out : (plane m hm).val ∉ pointParabolic m hm := by
  intro h
  have hh : pairSwap F σ hσ ∈ pointParabolicSU F J :=
    (mem_map_iff_mem (project_injective F J)).mp h
  have hz := (mem_pointParabolicSU F J _).mp hh |>.1
  simp [pairSwap,pairSwapMatrix,involutionElement] at hz

private theorem fixed_cosets (hmgt : 1 < m) (i : Bool)
    (g : SourceExtension.nativeFamily (P₀ := pointParabolic m hm) (P₁ := planeParabolic m hm) i)
    (hfix : ∀ p, g.val⁻¹*(splitTorus m hm p).val*g.val∈pointParabolic m hm ⊓ planeParabolic m hm) :
    g.val∈pointParabolic m hm ⊓ planeParabolic m hm ∨
      (if i then (plane m hm).val else (point m hm).val)*g.val∈pointParabolic m hm ⊓ planeParabolic m hm := by
  have hq : 2 < Nat.card K := by
    rw [PointLocal.fixedField_card m hm]
    exact (show 2^1<2^m from Nat.pow_lt_pow_right (by decide) hmgt)
  obtain ⟨a,ha⟩ := project_surjective F J g.val
  have hf (x y : Kˣ) : a⁻¹*(SmallCompletion.FourFixed.torus F σ hσ x y).val*a∈borelSU F J := by
    have hh := hfix (x,y)
    rw [←ha] at hh
    change π a⁻¹ * π _ * π a∈_ at hh
    rw [←map_mul,←map_mul] at hh
    exact ⟨(mem_map_iff_mem (project_injective F J)).mp hh.1,
      (mem_map_iff_mem (project_injective F J)).mp hh.2⟩
  have send (z : MatrixGroup m hm) (hz : z∈borelSU F J) :
      π z∈pointParabolic m hm ⊓ planeParabolic m hm :=
    ⟨⟨z,hz.1,rfl⟩,⟨z,hz.2,rfl⟩⟩
  cases i
  · have hg : a∈pointParabolicSU F J := (mem_map_iff_mem (project_injective F J)).mp (ha.symm ▸ g.property)
    rcases SmallCompletion.FourFixed.point_fixed_coset F σ hσ hq a hg hf with h | h
    · exact Or.inl (ha ▸ send a h)
    · right
      have hh := send _ h
      rw [map_mul,ha] at hh
      exact hh
  · have hg : a∈planeParabolicSU F J := (mem_map_iff_mem (project_injective F J)).mp (ha.symm ▸ g.property)
    rcases SmallCompletion.FourFixed.plane_fixed_coset F σ hσ hq a hg hf with h | h
    · exact Or.inl (ha ▸ send a h)
    · right
      have hh := send _ h
      rw [map_mul,ha] at hh
      exact hh

/-- The original order bound closes the split-torus marked apartment in
any full extension, including q = 4 and extensions of even degree. -/
theorem fourth_mem_middle (hmgt : 1 < m) (E : FourExtension m hm)
    {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hcard : Nat.card M≤Nat.card E.carrier) : rotation m hm E c ^ 4∈c.middle.range := by
  have hgeo := four_completion_quadrangle m hm hmgt E c ho hcard
  exact E.nativeRotation_four_mem_middle c (splitTorus m hm) (four_conj_injective m hm) ho
    (point m hm) (plane m hm) (point_sq m hm) (plane_sq m hm) (point_out m hm) (plane_out m hm)
    (fun p => ⟨(p.1,p.2⁻¹),point_torus m hm p⟩)
    (fun p => ⟨(p.2,p.1),plane_torus m hm p⟩)
    (fixed_cosets m hm hmgt false) (fixed_cosets m hm hmgt true) hgeo.2.1 hgeo.1

/-- The marked rotation has eighth power one. Its possible outer
involutory fourth power is not discarded. -/
theorem eighth_eq_one (hmgt : 1 < m) (E : FourExtension m hm)
    {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hcard : Nat.card M≤Nat.card E.carrier) : rotation m hm E c ^ 8=1 := by
  have hh := power_sq_eq_one_of_middle m hm E c 4 (fourth_mem_middle m hm hmgt E c ho hcard)
  simpa only [←pow_mul] using hh
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FourWeyl
