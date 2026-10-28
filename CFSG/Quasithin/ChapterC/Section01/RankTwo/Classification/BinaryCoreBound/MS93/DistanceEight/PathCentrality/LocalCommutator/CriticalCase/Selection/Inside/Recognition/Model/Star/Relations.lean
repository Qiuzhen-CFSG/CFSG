module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition.Model.Star.Algebra
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Calculations
/-!
# Eliminating the central parabolic action

Write s for the coordinate swap, t for the shear, and a,b for the two chosen
point movers. The product (a⁻¹ta)(b⁻¹tb) is t, while st has order three.
For a vector whose parabolic differences are globally fixed, displacement of
av·bv under t is therefore its displacement under t at v. If s fixes av·bv,
then st acts on this product by a fixed binary difference. Its order three
forces that difference to vanish. The existing cubic factorization of A₄
and its two cosets in the point parabolic finish pointwise fixation.

This is the nonsplit-extension step in the index-two branch of MS93 (1.6),
printed pp.845–847. The separate geometry argument must supply the pair relation.
-/

@[expose] public section
open Subgroup Matrix
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
open Escape.Initial.Natural.Splitting
namespace Star

-- All four actors are in the actual determinant-one matrix group.
def swap : SL := ⟨!![1,0,0; 0,0,1; 0,1,0], by decide⟩
def shear : SL := ⟨!![1,0,0; 0,1,1; 0,0,1], by decide⟩
def first : SL := ⟨!![0,1,0; 1,0,0; 0,0,1], by decide⟩
def second : SL := ⟨!![1,1,0; 1,0,0; 0,0,1], by decide⟩

theorem shear_mem : shear ∈ PSL3Two.pointParabolicSL := by
  rw [PSL3Two.mem_pointParabolicSL_iff]; decide

theorem swap_mem : swap ∈ PSL3Two.pointParabolicSL := by
  rw [PSL3Two.mem_pointParabolicSL_iff]; decide

theorem swap_shear_cube : (swap * shear) ^ 3 = 1 := by decide

theorem conjugate_first_mem : first⁻¹ * shear * first ∈ PSL3Two.pointParabolicSL := by
  rw [PSL3Two.mem_pointParabolicSL_iff]; decide

theorem conjugate_second_mem : second⁻¹ * shear * second ∈ PSL3Two.pointParabolicSL := by
  rw [PSL3Two.mem_pointParabolicSL_iff]; decide

theorem conjugates_mul :
    (first⁻¹ * shear * first) * (second⁻¹ * shear * second) = shear := by decide

-- A representative finite certificate: six possible invertible binary 2x2 Levi blocks.
theorem parabolic_cosets (k : SL) (hk : k ∈ PSL3Two.pointParabolicSL) :
    k ∈ PSL3Two.MarkedAutomorphisms.pointA ∨ k * shear ∈ PSL3Two.MarkedAutomorphisms.pointA := by
  have h : ∀ k : SL, k ∈ PSL3Two.pointParabolicSL →
      k ∈ PSL3Two.MarkedAutomorphisms.pointA ∨ k * shear ∈ PSL3Two.MarkedAutomorphisms.pointA := by
    decide +kernel
  exact h k hk

variable {E : Type*} [Group E] [IsElementaryAbelian 2 E]
set_option backward.isDefEq.respectTransparency false

theorem difference_transport (ρ : SL →* MulAut E) (a g : SL) (w : E) :
    actionDifference ρ g (ρ a w) = ρ a (w⁻¹ * ρ (a⁻¹ * g * a) w) := by
  change (ρ a w)⁻¹ * ρ g (ρ a w) = _
  simp only [map_mul, map_inv, MulAut.mul_apply]
  congr 1
  exact ((ρ a).apply_symm_apply _).symm

/-- A single escaping-pair relation kills the possible central sign action.
The hypotheses are equations in the original carrier and allow nonsplit extensions. -/
theorem fixed_of_central_differences_of_pair_relation (ρ : SL →* MulAut E) (w : E)
    (hcentral : ∀ k ∈ PSL3Two.pointParabolicSL, ∀ g : SL,
      ρ g (w⁻¹ * ρ k w) = w⁻¹ * ρ k w)
    (hpair : ρ swap (ρ first w * ρ second w) = ρ first w * ρ second w) :
    ∀ k ∈ PSL3Two.pointParabolicSL, ρ k w = w := by
  let δ := centralDifferenceHom ρ PSL3Two.pointParabolicSL w hcentral
  let v := ρ first w * ρ second w
  have hd : actionDifference ρ shear v = w⁻¹ * ρ shear w := by
    rw [show v = ρ first w * ρ second w from rfl, map_mul,
      difference_transport, difference_transport,
      hcentral _ conjugate_first_mem first, hcentral _ conjugate_second_mem second]
    change δ ⟨first⁻¹ * shear * first, conjugate_first_mem⟩ *
      δ ⟨second⁻¹ * shear * second, conjugate_second_mem⟩ = δ ⟨shear,shear_mem⟩
    rw [← map_mul]
    apply congrArg δ
    exact Subtype.ext conjugates_mul
  have hdcentral (g : SL) : ρ g (v⁻¹ * ρ shear v) = v⁻¹ * ρ shear v := by
    change ρ g (actionDifference ρ shear v) = actionDifference ρ shear v
    rw [hd]
    exact hcentral shear shear_mem g
  have hcd : v⁻¹ * ρ (swap * shear) v = v⁻¹ * ρ shear v := by
    have he : ρ shear v = v * (v⁻¹ * ρ shear v) := by simp
    have hp : ρ swap v = v := hpair
    rw [ρ.map_mul, MulAut.mul_apply, he, map_mul, hp, hdcentral]
  have hcv : ρ (swap * shear) v = v :=
    fixed_of_cube_of_fixed_difference ρ (swap * shear) v swap_shear_cube (by
      rw [hcd]
      exact hdcentral _)
  have hzero : actionDifference ρ shear v = 1 := by
    change v⁻¹ * ρ shear v = 1
    rw [← hcd, hcv, inv_mul_cancel]
  have hshear : ρ shear w = w := by
    rw [hd] at hzero
    exact (inv_mul_eq_one.mp hzero).symm
  have hcubic (k : SL) (hk : k ∈ PSL3Two.pointParabolicSL) (hc : k ^ 3 = 1) :
      ρ k w = w := fixed_of_cube_of_fixed_difference ρ k w hc (hcentral k hk k)
  have hA (k : SL) (hk : k ∈ PSL3Two.MarkedAutomorphisms.pointA) : ρ k w = w := by
    rcases PSL3Two.MarkedAutomorphisms.cubic_factor k hk with hc | hc
    · exact hcubic k (PSL3Two.MarkedAutomorphisms.pointA_le hk) hc
    · have h₁ := hcubic PSL3Two.MarkedAutomorphisms.cubic
        (PSL3Two.MarkedAutomorphisms.pointA_le PSL3Two.MarkedAutomorphisms.cubic_mem)
        PSL3Two.MarkedAutomorphisms.cubic_cube
      have h₂ := hcubic (PSL3Two.MarkedAutomorphisms.cubic⁻¹ * k)
        (PSL3Two.pointParabolicSL.mul_mem
          (PSL3Two.pointParabolicSL.inv_mem
            (PSL3Two.MarkedAutomorphisms.pointA_le PSL3Two.MarkedAutomorphisms.cubic_mem))
          (PSL3Two.MarkedAutomorphisms.pointA_le hk)) hc
      have he := congrArg (ρ PSL3Two.MarkedAutomorphisms.cubic) h₂
      simpa only [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left, h₁] using he
  intro k hk
  rcases parabolic_cosets k hk with ha | ha
  · exact hA k ha
  · simpa only [map_mul, MulAut.mul_apply, hshear] using hA (k * shear) ha

end Star
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
