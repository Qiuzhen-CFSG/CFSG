module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ModuleData
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.ReplacementConstruction
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The six-dimensional bound for commutator-generated binary SL₃(2) FF-modules

The three elementary involutions in positions (0,1), (1,2), (2,0) generate
SL₃(2), and every involution is conjugate to each of them. The whole
commutator space is the sum of their three displacement images. An offender
has rank at most two; a nonidentity element in it therefore displaces at most
two dimensions, giving a total dimension at most six.

The matrix identities and involution conjugacy are checked by kernel reduction.
The rank bound uses the existing marked PSL₂(7) comparison. This argument
applies before any splitting or semisimplicity assertion. In conjunction with
the irreducible catalogue, it reduces the binary specialization of
Aschbacher–Smith B.5.1 (printed pp.99–101) to one natural head or the
natural-by-natural extensions of B.4.9 (pp.92–95), in the combined manuscript
of 1 March 2004.
-/

public section
open Representation Representation.BinaryOffender Matrix
namespace CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition.ExtensionControl

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

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem involution_conjugacy : ∀ a : SL, a ^ 2 = 1 → a ≠ 1 →
    ∃ c : SL, c * a = x * c := by decide +kernel

private def cycle : SL := ⟨!![0,0,1;1,0,0;0,1,0], by decide⟩
private theorem conjugate_y : cycle * x * cycle⁻¹ = y := by decide
private theorem conjugate_z : cycle * y * cycle⁻¹ = z := by decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) SL V)

private theorem bound_by_involution (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤) :
    Module.finrank (ZMod 2) V ≤ 3 * fixedCodim ρ (Subgroup.zpowers x) := by
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
  have hU : U = ⊤ := by
    apply top_unique
    rw [← hfull]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, v, _, rfl⟩
    exact (show g ∈ H from hH ▸ Subgroup.mem_top g) v
  have hy : fixedCodim ρ (Subgroup.zpowers y) = fixedCodim ρ (Subgroup.zpowers x) := by
    rw [← conjugate_y, fixedCodim_zpowers_conj]
  have hz : fixedCodim ρ (Subgroup.zpowers z) = fixedCodim ρ (Subgroup.zpowers x) := by
    rw [← conjugate_z, fixedCodim_zpowers_conj, hy]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (D x) (D y)
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (D x ⊔ D y) (D z)
  have hu : Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) V := by
    rw [hU, finrank_top]
  have hx' := fixedCodim_zpowers_eq_displacement_rank ρ x
  have hy' := fixedCodim_zpowers_eq_displacement_rank ρ y
  have hz' := fixedCodim_zpowers_eq_displacement_rank ρ z
  change fixedCodim ρ (Subgroup.zpowers x) = Module.finrank (ZMod 2) (D x) at hx'
  change fixedCodim ρ (Subgroup.zpowers y) = Module.finrank (ZMod 2) (D y) at hy'
  change fixedCodim ρ (Subgroup.zpowers z) = Module.finrank (ZMod 2) (D z) at hz'
  change Module.finrank (ZMod 2) (((D x ⊔ D y) ⊔ D z) : Submodule (ZMod 2) V) = _ at hu
  omega

/-- Every elementary abelian two-subgroup of the actual SL₃(2) has rank at most two. -/
theorem elementary_rank_le_two (A : Subgroup SL) (hA : IsElementaryAbelian 2 A) :
    rank A ≤ 2 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) ≃* SL :=
    Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.trans Matrix.PSL3Two.equiv.symm
  have hr : primeRank 2 SL ≤ 2 := by
    rw [← Theory.GroupTheory.primeRank_equiv 2 e, Theory.PSL2.primeField_two_rank (by decide : 3 < 7)]
  have hc := (primeRank_le_iff_elementary_card_le SL).mp hr A hA
  have hl := Nat.log_monotone (b := 2) hc
  simpa only [Representation.BinaryOffender.rank, Nat.log_pow (by decide : 1 < 2)] using hl

/-- Every full-commutator binary SL₃(2) FF-module has dimension at most six.
Faithfulness is not needed for this bound. -/
theorem finrank_le_six (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (hFF : IsFFModule ρ) : Module.finrank (ZMod 2) V ≤ 6 := by
  obtain ⟨A, hA⟩ := hFF
  have ha : ∃ a ∈ A, a ≠ (1 : SL) := by
    by_contra! ha
    apply hA.1.1
    apply le_bot_iff.mp
    intro a haA
    exact ha a haA
  obtain ⟨a, ha, hne⟩ := ha
  let : IsElementaryAbelian 2 A := hA.1.2
  obtain ⟨c, hc⟩ := involution_conjugacy a
    (elemPow_eq_one_of_isElementaryAbelian a ha) hne
  have he : c * a * c⁻¹ = x := by rw [hc, mul_inv_cancel_right]
  have hx : fixedCodim ρ (Subgroup.zpowers x) = fixedCodim ρ (Subgroup.zpowers a) := by
    rw [← he, fixedCodim_zpowers_conj]
  have hle : fixedSpace ρ A ≤ fixedSpace ρ (Subgroup.zpowers a) :=
    fixedSpace_antitone ρ ((Subgroup.zpowers_le).mpr ha)
  have hh := Submodule.finrank_mono hle
  have h1 := fixedCodim_add_finrank ρ A
  have h2 := fixedCodim_add_finrank ρ (Subgroup.zpowers a)
  have hr := elementary_rank_le_two A hA.1.2
  have hb := bound_by_involution ρ hfull
  have hbudget := hA.2
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition.ExtensionControl
