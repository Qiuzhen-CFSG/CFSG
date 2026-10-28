module

public import Theory.Mathieu.SchurMultipliers.M24TwoPrimary.Reduction
public import Theory.Mathieu.M24.ChapterHStabilizers.OctadAction
public import Theory.GroupTheory.CentralBinaryKernelSquares
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.Group

/-!
# Elementary translation preimages in double extensions of the octad stabilizer

The native stabilizer induces every linear automorphism of its binary
four-dimensional pointwise kernel. Thus all nonidentity translations are
conjugate. A central kernel of order two makes the square independent of the
lift, and conjugation fixes that square. All nonzero translations therefore
have a common lift square. On a three-dimensional subspace the seven nonzero
squares and the central commutator identity force this square to be one.

The coordinates and conjugations are those of the literal octad action. The
last theorem applies the calculation to the full preimage under the original
perfect central covering map.

Source context: Aschbacher–Smith, I.1.3, printed p.407; GLS3 §6.1 and the
native E₁₆.A₈ subgroup in Table 5.3e. This proves the elementary-preimage input
to the local two-primary multiplier calculation.
-/

open Subgroup PerfectCentralCovering
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.LinearFourCore
open Sporadic.Mathieu.M24ChapterHStabilizers.OctadAction
open scoped commutatorElement
namespace Sporadic.Mathieu.SchurMultipliers.M24TwoPrimary

@[expose] public section
noncomputable section

/-- The literal pointwise octad kernel in the native binary four-space coordinates. -/
def translationCoordinates : octadKernel ≃* Multiplicative Space :=
  (MulEquiv.subgroupCongr seed_core_eq_kernel.symm).trans (coreCoordinates seedOctad)

private theorem linear_transitive (x y : Space) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : Space ≃ₗ[ZMod 2] Space, g x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) Space x hx
  let ey := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) Space y hy
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨g, ?_⟩
  have h := hg (ex 1)
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [ex, ey] using h.symm

/-- All nonidentity translations are conjugate inside the actual octad stabilizer. -/
theorem octadKernel_isConj (a b : octadKernel) (ha : a ≠ 1) (hb : b ≠ 1) :
    IsConj (a : OctadGroup) (b : OctadGroup) := by
  let ea : Core seedOctad := (MulEquiv.subgroupCongr seed_core_eq_kernel.symm) a
  let eb : Core seedOctad := (MulEquiv.subgroupCongr seed_core_eq_kernel.symm) b
  have hne (v : octadKernel) (hv : v ≠ 1) : (translationCoordinates v).toAdd ≠ 0 := by
    intro h
    apply hv
    apply translationCoordinates.injective
    exact h.trans (map_one translationCoordinates).symm
  obtain ⟨g, hg⟩ := linear_transitive _ _ (hne a ha) (hne b hb)
  obtain ⟨t, ht⟩ := linearAction_surjective seedOctad g
  have he : coreConjugate seedOctad t ea = eb := by
    apply (coreCoordinates seedOctad).injective
    apply Multiplicative.toAdd.injective
    rw [coreCoordinates_conjugation, naturalAction_quotientEquiv, ht]
    exact hg
  have hval := congrArg Subtype.val he
  rw [coreConjugate_coe] at hval
  exact isConj_iff.mpr ⟨t, hval⟩

/-- Bilinearity of the central commutator forbids a common nontrivial square
on all seven nonzero vectors of a binary three-space. -/
private theorem seven_squares {R : Type*} [Group R] (a b c k : R)
    (h2 : k ^ 2 = 1)
    (ha : a ^ 2 = k) (hb : b ^ 2 = k) (hc : c ^ 2 = k)
    (hab : (a*b)^2 = k) (hac : (a*c)^2 = k)
    (hbc : (b*c)^2 = k) (habc : (a*(b*c))^2 = k)
    (hsa : a ^ 2 ∈ center R)
    (hcomm : ∀ y ∈ ({b, c, b*c} : Set R), ⁅a,y⁆ ∈ center R) : k = 1 := by
  have hmul (y : R) (hy : y ∈ ({b,c,b*c} : Set R)) :
      (a*y)^2 = a^2 * y^2 * ⁅a,y⁆ := by
    symm
    calc
      a^2 * y^2 * ⁅a,y⁆ = ⁅a,y⁆ * (a^2*y^2) := mem_center_iff.mp (hcomm y hy) _
      _ = a*y*a⁻¹*(y⁻¹*a^2)*y^2 := by simp only [commutatorElement_def, mul_assoc]
      _ = a*y*a⁻¹*(a^2*y⁻¹)*y^2 := by rw [mem_center_iff.mp hsa]
      _ = (a*y)^2 := by simp only [pow_two]; group
  have hkk : k*k = 1 := by simpa [pow_two] using h2
  have hab' : ⁅a,b⁆ = k := by simpa [ha, hb, hab, hkk] using (hmul b (by simp)).symm
  have hac' : ⁅a,c⁆ = k := by simpa [ha, hc, hac, hkk] using (hmul c (by simp)).symm
  have habc' : ⁅a,b*c⁆ = k := by simpa [ha, hbc, habc, hkk] using (hmul (b*c) (by simp)).symm
  have hh : ⁅a,b*c⁆ = ⁅a,b⁆ * ⁅a,c⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hcent := mem_center_iff.mp (hcomm c (by simp)) b
    calc
      _ = ⁅a,b⁆ * (b * ⁅a,c⁆) * b⁻¹ := by group
      _ = ⁅a,b⁆ * ⁅a,c⁆ := by rw [hcent]; group
  simpa [habc', hab', hac', hkk] using hh

/-- Every central extension of the native octad stabilizer by a group of order
two has elementary preimage of the pointwise kernel. -/
theorem elementaryKernelPreimage_of_double_kernel
    {L : Type*} [Group L] (q : L →* OctadGroup)
    (hq : Function.Surjective q) (hz : q.ker ≤ center L)
    (hcard : Nat.card q.ker = 2) : ElementaryKernelPreimage q := by
  have h2 (z : L) (hz' : z ∈ q.ker) : z^2 = 1 := by
    have h := pow_card_eq_one' (x := (⟨z, hz'⟩ : q.ker))
    rw [hcard] at h
    exact congrArg Subtype.val h
  have hsq (x : L) (hx : q x ∈ octadKernel) : x^2 ∈ q.ker := by
    change q (x^2) = 1
    rw [map_pow]
    exact congrArg Subtype.val (kernel_sq ⟨q x, hx⟩)
  have hcomm (x y : L) (hx : q x ∈ octadKernel) (hy : q y ∈ octadKernel) :
      ⁅x,y⁆ ∈ center L := by
    apply hz
    change q ⁅x,y⁆ = 1
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact congrArg Subtype.val (kernel_mul_comm ⟨q x, hx⟩ ⟨q y, hy⟩)
  have hsame (x y : L) (hx : q x ∈ octadKernel) (hy : q y ∈ octadKernel)
      (hx' : q x ≠ 1) (hy' : q y ≠ 1) : x^2 = y^2 := by
    apply q.square_eq_of_isConj_map_of_central_binary_kernel hq hz h2 (hz (hsq x hx))
    exact octadKernel_isConj ⟨q x,hx⟩ ⟨q y,hy⟩
      (fun he => hx' (congrArg Subtype.val he)) (fun he => hy' (congrArg Subtype.val he))
  intro x hx
  by_cases hx' : q x = 1
  · exact h2 x hx'
  let j : Multiplicative Space →* OctadGroup :=
    octadKernel.subtype.comp translationCoordinates.symm.toMonoidHom
  have hj : Function.Injective j :=
    octadKernel.subtype_injective.comp translationCoordinates.symm.injective
  have hmem (v : Space) (y : L) (hy : q y = j (Multiplicative.ofAdd v)) :
      q y ∈ octadKernel := by
    rw [hy]
    exact (translationCoordinates.symm (Multiplicative.ofAdd v)).property
  have hvalue (v : Space) (hv : v ≠ 0) (y : L)
      (hy : q y = j (Multiplicative.ofAdd v)) : y^2 = x^2 := by
    apply hsame y x (hmem v y hy) hx _ hx'
    rw [hy]
    intro he
    apply hv
    exact congrArg Multiplicative.toAdd (hj (he.trans (map_one j).symm))
  let va : Space := ![1,0,0,0]
  let vb : Space := ![0,1,0,0]
  let vc : Space := ![0,0,1,0]
  obtain ⟨a, ha⟩ := hq (j (Multiplicative.ofAdd va))
  obtain ⟨b, hb⟩ := hq (j (Multiplicative.ofAdd vb))
  obtain ⟨c, hc⟩ := hq (j (Multiplicative.ofAdd vc))
  have hadd (u v : Space) (y z : L)
      (hy : q y = j (Multiplicative.ofAdd u)) (hz' : q z = j (Multiplicative.ofAdd v)) :
      q (y*z) = j (Multiplicative.ofAdd (u+v)) := by
    rw [map_mul, hy, hz', ← map_mul]
    rfl
  have hab := hadd va vb a b ha hb
  have hac := hadd va vc a c ha hc
  have hbc := hadd vb vc b c hb hc
  have habc := hadd va (vb+vc) a (b*c) ha hbc
  apply seven_squares a b c (x^2) (h2 _ (hsq x hx))
    (hvalue va (by decide) a ha) (hvalue vb (by decide) b hb)
    (hvalue vc (by decide) c hc) (hvalue (va+vb) (by decide) (a*b) hab)
    (hvalue (va+vc) (by decide) (a*c) hac) (hvalue (vb+vc) (by decide) (b*c) hbc)
    (hvalue (va+(vb+vc)) (by decide) (a*(b*c)) habc)
    (hz (hsq a (hmem va a ha)))
  intro y hy
  rcases hy with h | h | h
  · have he : y = b := h
    subst y
    exact hcomm a b (hmem va a ha) (hmem vb b hb)
  · have he : y = c := h
    subst y
    exact hcomm a c (hmem va a ha) (hmem vc c hc)
  · have he : y = b*c := h
    subst y
    exact hcomm a (b*c) (hmem va a ha) (hmem (vb+vc) (b*c) hbc)

/-- Application to the full octad preimage in the original perfect central cover. -/
theorem m24_double_cover_elementary_preimage {E : Type*} [Group E]
    (f : Cover E M24) (hcard : Nat.card f.toMonoidHom.ker = 2) :
    ElementaryKernelPreimage (octadProjection f) :=
  elementaryKernelPreimage_of_double_kernel (octadProjection f)
    (octadProjection_surjective f) (octadProjection_ker_le_center f)
    ((octadProjection_kernel_card f).trans hcard)

end
end
end Sporadic.Mathieu.SchurMultipliers.M24TwoPrimary
