module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.Models.Rigidity
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.ModelOffenders.ExplicitOffenders.InvolutionDisplacement.InvolutionClass
public import Theory.Representation.DualCommutator

/-!
# Involution displacement and the full fixed-space codimension

Three conjugate elementary involutions generate SL₃(2). Their displacement
images span the full commutator space, so its dimension is at most three
times the displacement of any involution. Applying this to the dual bounds
the codimension of the whole-group fixed space.

The generator argument is adapted from ExtensionControl.Dimension; conjugacy
uses the existing checked InvolutionClass theorem. No new enumeration of
offenders or covering modules occurs here.
Source context: Meierfrankenfeld–Stellmacher (1993), printed pp.863,877.
-/

public section
open Subgroup Representation Representation.BinaryOffender Matrix
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.Models
private def x : SL := ⟨!![1,1,0;0,1,0;0,0,1], by decide⟩
private def y : SL := ⟨!![1,0,0;0,1,1;0,0,1], by decide⟩
private def z : SL := ⟨!![1,0,0;0,1,0;1,0,1], by decide⟩

private theorem three_generate : Subgroup.closure ({x,y,z} : Set SL) = ⊤ := by
  apply top_unique
  intro g _
  let H := Subgroup.closure ({x,y,z} : Set SL)
  have hx : x ∈ H := Subgroup.subset_closure (by simp)
  have hy : y ∈ H := Subgroup.subset_closure (by simp)
  have hz : z ∈ H := Subgroup.subset_closure (by simp)
  apply Atlas.sl_elementary_induction (fun g => g ∈ H) ?_ (fun _ _ => H.mul_mem) g
  intro i j hij a
  have he : ∀ (i j : Fin 3) (hij : i ≠ j) (a : ZMod 2),
      SpecialLinearGroup.transvection hij a = 1 ∨
      SpecialLinearGroup.transvection hij a = x ∨
      SpecialLinearGroup.transvection hij a = y ∨
      SpecialLinearGroup.transvection hij a = z ∨
      SpecialLinearGroup.transvection hij a = x * y * x * y ∨
      SpecialLinearGroup.transvection hij a = y * z * y * z ∨
      SpecialLinearGroup.transvection hij a = z * x * z * x := by decide
  rcases he i j hij a with h | h | h | h | h | h | h <;> rw [h]
  · exact H.one_mem
  · exact hx
  · exact hy
  · exact hz
  · exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) hx) hy
  · exact H.mul_mem (H.mul_mem (H.mul_mem hy hz) hy) hz
  · exact H.mul_mem (H.mul_mem (H.mul_mem hz hx) hz) hx

private def cycle : SL := ⟨!![0,0,1;1,0,0;0,1,0], by decide⟩
private theorem conjugate_y : cycle * x * cycle⁻¹ = y := by decide
private theorem conjugate_z : cycle * y * cycle⁻¹ = z := by decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) SL V)

private theorem bound_by_involution :
    Module.finrank (ZMod 2) (Coinvariants.ker ρ) ≤ 3 * fixedCodim ρ (Subgroup.zpowers x) := by
  let D (g : SL) := LinearMap.range (ρ g - LinearMap.id)
  let U := (D x ⊔ D y) ⊔ D z
  let H : Subgroup SL := {
    carrier := {g | ∀ v, ρ g v - v ∈ U}
    one_mem' := by intro v; simp
    mul_mem' := by
      intro g h hg hh v
      have hm := U.add_mem (hg (ρ h v)) (hh v)
      simpa only [map_mul, Module.End.mul_apply, sub_add_sub_cancel] using hm
    inv_mem' := by
      intro g hg v
      have hm := U.neg_mem (hg (ρ g⁻¹ v))
      simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply, neg_sub] using hm
  }
  have hd (g : SL) (hg : D g ≤ U) : g ∈ H := by
    intro v
    exact hg ⟨v, rfl⟩
  have hH : H = ⊤ := by
    apply top_unique
    rw [← three_generate]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with rfl | rfl | rfl
    · exact hd x (le_sup_of_le_left le_sup_left)
    · exact hd y (le_sup_of_le_left le_sup_right)
    · exact hd z le_sup_right
  have hU : Coinvariants.ker ρ ≤ U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    exact (show g ∈ H from hH ▸ Subgroup.mem_top g) v
  have hy : fixedCodim ρ (Subgroup.zpowers y) = fixedCodim ρ (Subgroup.zpowers x) := by
    rw [← conjugate_y, fixedCodim_zpowers_conj]
  have hz : fixedCodim ρ (Subgroup.zpowers z) = fixedCodim ρ (Subgroup.zpowers x) := by
    rw [← conjugate_z, fixedCodim_zpowers_conj, hy]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (D x) (D y)
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (D x ⊔ D y) (D z)
  have hu := Submodule.finrank_mono hU
  have hx' := fixedCodim_zpowers_eq_displacement_rank ρ x
  have hy' := fixedCodim_zpowers_eq_displacement_rank ρ y
  have hz' := fixedCodim_zpowers_eq_displacement_rank ρ z
  change fixedCodim ρ (Subgroup.zpowers x) = Module.finrank (ZMod 2) (D x) at hx'
  change fixedCodim ρ (Subgroup.zpowers y) = Module.finrank (ZMod 2) (D y) at hy'
  change fixedCodim ρ (Subgroup.zpowers z) = Module.finrank (ZMod 2) (D z) at hz'
  change Module.finrank (ZMod 2) (Coinvariants.ker ρ) ≤
    Module.finrank (ZMod 2) (((D x ⊔ D y) ⊔ D z) : Submodule (ZMod 2) V) at hu
  omega

theorem commutator_finrank_le_three_mul (a : SL) (ha : a ^ 2 = 1) (hne : a ≠ 1) :
    Module.finrank (ZMod 2) (Coinvariants.ker ρ) ≤ 3 * fixedCodim ρ (zpowers a) := by
  obtain ⟨c, hc⟩ := AbelianCore.DoubleCopy.CoverModels.ModelOffenders.InvolutionDisplacement.involution_conjugate_transvection a ha hne
  have hx : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : ZMod 2) = x := by decide
  rw [hx] at hc
  have he : a = c * x * c⁻¹ := by rw [← hc, mul_inv_cancel_right]
  rw [he, fixedCodim_zpowers_conj]
  exact bound_by_involution ρ

theorem fixedCodim_top_le_three_mul (a : SL) (ha : a ^ 2 = 1) (hne : a ≠ 1) :
    fixedCodim ρ ⊤ ≤ 3 * fixedCodim ρ (zpowers a) := by
  have hfix : fixedSpace ρ ⊤ = invariants ρ := by
    ext v
    exact ⟨fun h g => h ⟨g, mem_top g⟩, fun h g => h g.val⟩
  rw [fixedCodim, hfix, ρ.finrank_quotient_invariants_eq_dual_commutator]
  have h := commutator_finrank_le_three_mul ρ.dual a ha hne
  rw [fixedCodim_zpowers_dual] at h
  exact h

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.Models
