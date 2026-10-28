module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.PureImageBound
import Mathlib.Tactic.Group

/-!
# Kernel displacement forced by actual pure lifts

A first-class involution in the literal x-fiber is kernel-conjugate to x:
the complete fiber census excludes its other representative. Thus a kernel
element in a pure elementary extension lies in the displacement of every
outside-kernel lift. Local conjugation transports this assertion to every
actual lift, and the final theorem uses the original Mathieu projection and
binary kernel coordinates. No lift, kernel, or container alternative is
assumed.

Source: Kleidman--Wilson (1988), Section 2.1, p.489. This supplies the
lift-dependent restriction needed to distinguish common and exceptional
image geometry; it does not assert whole-normalizer placement.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
open Cardinality KernelCount QuotientCount.Image
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits
open Simplicity.Max1Fusion.InvolutionFibers
open NativePair LinearFive InvolutionCentralizers.Second
open M22Images.KernelAction InvolutionCentralizers.Second.FiveAction
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup
  Cardinality.localKernel basis localX localY outsideRepresentative
set_option backward.isDefEq.respectTransparency true

local notation "x₀" => (localX matrixA_mul_self matrixB_pow_four : M)

private theorem x_square : x₀ * x₀ = 1 := localX_mul_self _ _
private theorem x_inv : x₀⁻¹ = x₀ := inv_eq_of_mul_eq_one_left x_square
private theorem E_inv (n : ℕ) : (kernelValue n)⁻¹ = kernelValue n :=
  inv_eq_of_mul_eq_one_left (kernelValue_square n)

private theorem x_kernel_conjugate (m n : ℕ) :
    kernelValue n * (x₀ * kernelValue m) * (kernelValue n)⁻¹ =
      x₀ * kernelValue (Nat.xor (Nat.xor (maskImage xMasks n) m) n) := by
  rw [kernelValue_xor,kernelValue_xor,E_inv]
  have h := right_conj_mask_x matrixA_mul_self matrixB_pow_four n
  change x₀⁻¹ * kernelValue n * x₀ = kernelValue (maskImage xMasks n) at h
  rw [← h]
  group

private theorem x_square_equation (m : Fin 2048)
    (hs : (x₀ * kernelValue m.val)^2 = 1) :
    Nat.xor (maskImage xMasks m.val) m.val = 0 := by
  have he : kernelValue (Nat.xor (maskImage xMasks m.val) m.val) = kernelValue 0 := by
    rw [kernelValue_xor,kernelValue_zero]
    have h := right_conj_mask_x matrixA_mul_self matrixB_pow_four m.val
    change x₀⁻¹ * kernelValue m.val * x₀ = kernelValue (maskImage xMasks m.val) at h
    rw [← h,x_inv]
    simpa only [pow_two,mul_assoc] using hs
  exact kernelValue_injective (square_bound false m) (by decide) he

/-- A first-class involution in the literal x-fiber differs from x by an
actual kernel commutator. -/
theorem first_x_fiber_displacement (w : M) (hw : w ∈ max1Kernel)
    (hp : IsConj a ((x₀ * w : M) : Model)) :
    ∃ u ∈ max1Kernel, w = x₀⁻¹ * u * x₀ * u⁻¹ := by
  obtain ⟨m,hm⟩ := maskValue_surjective matrixA_mul_self matrixB_pow_four ⟨w,hw⟩
  have he : kernelValue m.val = w := congrArg Subtype.val hm
  subst w
  have ho : orderOf ((x₀ * kernelValue m.val : M) : Model) = 2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hp
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq a).trans orderOf_a
  have hs : (x₀ * kernelValue m.val)^2 = 1 := by
    apply Subtype.ext
    exact ho ▸ pow_orderOf_eq_one ((x₀ * kernelValue m.val : M) : Model)
  obtain ⟨hi,heq⟩ := reduction false m (x_square_equation m hs)
  have hc := x_kernel_conjugate m.val (witness false m.val).2
  change Nat.xor (Nat.xor (maskImage xMasks (witness false m.val).2) m.val)
    (witness false m.val).2 = outsideMask (witness false m.val).1 at heq
  rw [heq] at hc
  have hr : outsideRepresentative matrixA_mul_self matrixB_pow_four (witness false m.val).1 =
      x₀ * kernelValue (outsideMask (witness false m.val).1) := by
    simp only [outsideRepresentative, if_pos (hi.mpr rfl)]
    rfl
  have hf := (outside_first_iff _).mp (hp.trans (isConj_iff.mpr
    ⟨(kernelValue (witness false m.val).2 : Model),
      (congrArg (fun u : M => (u : Model)) hc).trans
        (congrArg (fun u : M => (u : Model)) hr).symm⟩))
  have hzero : (witness false m.val).1 = 0 := by
    rcases hf with h | h
    · exact h
    · have hi' := hi.mpr rfl
      rw [h] at hi'
      norm_num at hi'
  rw [hzero] at hc
  change kernelValue _ * (x₀ * kernelValue m.val) * (kernelValue _)⁻¹ =
    x₀ * kernelValue 0 at hc
  rw [kernelValue_zero,mul_one] at hc
  refine ⟨(kernelValue (witness false m.val).2)⁻¹,
    max1Kernel.inv_mem (maskValue _ _ _).property,?_⟩
  calc
    _ = x₀⁻¹ * ((kernelValue (witness false m.val).2)⁻¹ *
      (kernelValue (witness false m.val).2 * (x₀ * kernelValue m.val) *
        (kernelValue (witness false m.val).2)⁻¹) * kernelValue (witness false m.val).2) := by group
    _ = _ := by rw [hc]; simp only [inv_inv,mul_assoc]

/-- Every actual kernel element of a pure native-pair extension lies in the
kernel displacement of each of its outside-kernel lifts. -/
theorem pure_extension_kernel_displacement (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (z : M) (hz : (z : Model) ∈ X) (hzk : z ∉ max1Kernel)
    (w : M) (hw : (w : Model) ∈ X) (hwk : w ∈ max1Kernel) :
    ∃ u ∈ max1Kernel, w = z⁻¹ * u * z * u⁻¹ := by
  obtain ⟨g,hg⟩ := pure_extension_first_lift X hpair hpure z hz hzk
  have hprod : ((z * w : M) : Model) ≠ 1 := by
    intro he
    have he' : z * w = 1 := Subtype.ext he
    exact hzk ((eq_inv_iff_mul_eq_one.mpr he').symm ▸ max1Kernel.inv_mem hwk)
  have hp := (hpure _ (X.mul_mem hz hw) hprod).trans
    (isConj_iff.mpr ⟨(g : Model),rfl⟩)
  have hp' : IsConj a ((x₀ * (MulAut.conj g) w : M) : Model) := by
    rw [← hg,← map_mul]
    exact hp
  have hw' : (MulAut.conj g) w ∈ max1Kernel :=
    (inferInstance : max1Kernel.Normal).conj_mem w hwk g
  obtain ⟨u,hu,he⟩ := first_x_fiber_displacement ((MulAut.conj g) w) hw' hp'
  refine ⟨g⁻¹ * u * g,?_,?_⟩
  · simpa only [inv_inv] using (inferInstance : max1Kernel.Normal).conj_mem u hu (g⁻¹)
  · change g * w * g⁻¹ = x₀⁻¹ * u * x₀ * u⁻¹ at he
    change g * z * g⁻¹ = x₀ at hg
    rw [← hg] at he
    calc
      w = g⁻¹ * (g * w * g⁻¹) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹)⁻¹ * u * (g * z * g⁻¹) * u⁻¹) * g := by rw [he]
      _ = _ := by group

/-- All first-class lifts of the same nontrivial image as an actual pure
extension element are conjugate by the binary kernel. This conjugator fixes
the native pair pointwise; it does not assert that the chosen lift is
preserved by the whole normalizer. -/
theorem pure_extension_lift_fiber_transitive (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (z : M) (hz : (z : Model) ∈ X) (hzk : z ∉ max1Kernel)
    (t : M) (ht : IsConj a (t : Model)) (himage : starHom t = starHom z) :
    ∃ u ∈ max1Kernel, (MulAut.conj u) z = t := by
  obtain ⟨g,hg⟩ := pure_extension_first_lift X hpair hpure z hz hzk
  let w : M := x₀⁻¹ * (g * t * g⁻¹)
  have hw : w ∈ max1Kernel := by
    rw [← starHom_ker]
    apply MonoidHom.mem_ker.mpr
    change starHom (x₀⁻¹ * (g * t * g⁻¹)) = 1
    have hq : starHom x₀ = starHom g * starHom z * (starHom g)⁻¹ := by
      rw [← hg]
      change starHom (g * z * g⁻¹) = _
      rw [map_mul,map_mul,map_inv]
    rw [map_mul,map_inv,map_mul,map_mul,map_inv,himage,hq,inv_mul_cancel]
  have hp : IsConj a ((x₀ * w : M) : Model) := by
    have he : x₀ * w = g * t * g⁻¹ := mul_inv_cancel_left _ _
    rw [he]
    exact ht.trans (isConj_iff.mpr ⟨(g : Model),rfl⟩)
  obtain ⟨e,he,hwe⟩ := first_x_fiber_displacement w hw hp
  have hgt : g * t * g⁻¹ = e * x₀ * e⁻¹ := by
    calc
      _ = x₀ * w := (mul_inv_cancel_left _ _).symm
      _ = _ := by rw [hwe]; group
  refine ⟨g⁻¹ * e * g,?_,?_⟩
  · simpa only [inv_inv] using (inferInstance : max1Kernel.Normal).conj_mem e he (g⁻¹)
  · change (g⁻¹ * e * g) * z * (g⁻¹ * e * g)⁻¹ = t
    change g * z * g⁻¹ = x₀ at hg
    calc
      _ = g⁻¹ * (e * (g * z * g⁻¹) * e⁻¹) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹) * g := by rw [hg,hgt]
      _ = t := by group

/-- Coordinate form of the actual-lift restriction, using the literal star
projection and the original eleven-bit kernel. -/
theorem pure_extension_kernel_mask (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (p : StarGroup) (hp : p ∈ (X.subgroupOf M).map starHom) (hp1 : p ≠ 1)
    (m : Fin 2048) (hm : (kernelValue m.val : Model) ∈ X) :
    ∃ n : Fin 2048, SylowCore.starMask p n.val ^^^ n.val = m.val := by
  obtain ⟨z,hz,rfl⟩ := hp
  have hzk : z ∉ max1Kernel := by
    intro hk
    exact hp1 (MonoidHom.mem_ker.mp (starHom_ker.symm ▸ hk))
  obtain ⟨u,hu,he⟩ := pure_extension_kernel_displacement X hpair hpure z hz hzk
    (kernelValue m.val) hm (maskValue _ _ _).property
  obtain ⟨n,hn⟩ := maskValue_surjective matrixA_mul_self matrixB_pow_four ⟨u,hu⟩
  have hn' : kernelValue n.val = u := congrArg Subtype.val hn
  have hz2 : z * z = 1 := by
    apply Subtype.ext
    simpa only [pow_two,Subgroup.coe_mul,Subgroup.coe_one] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : Model) hz
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_left hz2
  rw [← hn',hzi,E_inv] at he
  have hc := kernel_conjugation z n.val
  rw [hzi] at hc
  rw [hc,← kernelValue_xor] at he
  refine ⟨n,?_⟩
  exact kernelValue_injective
    (Nat.xor_lt_two_pow (n := 11) (SylowCore.Transport.starMask_lt _ _) n.isLt)
    m.isLt he.symm

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
