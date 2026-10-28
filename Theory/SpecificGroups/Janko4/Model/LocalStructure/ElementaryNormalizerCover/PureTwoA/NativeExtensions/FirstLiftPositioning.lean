module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.NinthKernelRanks

/-!
# Excluding the ninth actual lift in a native-pair extension

The seven-mask kernel calculation excludes the ninth outside lift even
before maximality is used. A Mathieu conjugator keeps the marked pair in the
binary kernel. Purity would place both transported generators among the seven
masks, whose pair rank is at most sixteen; simultaneous conjugacy preserves
the native pair's rank twenty. Consequently every outside-kernel element of
a pure extension is locally conjugate to the first lift x. At maximal
TWO-local level one such lift exists, and the same conjugator positions the
whole original subgroup and both whole ambient local groups.

Source: Kleidman--Wilson (1988), Section 2.1, p.489. This proves an actual
lift restriction from native certificates; it does not assert the remaining
extension-dependent whole-normalizer placement.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
open Cardinality KernelCount QuotientCount.Image
open Simplicity.Max1Fusion NativePair LinearFive InvolutionCentralizers.Second
open Simplicity.Max1Fusion.KernelOrbits
open InvolutionCentralizers.Second.FiveAction
open M22Images.KernelAction
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup
  Cardinality.localKernel basis
set_option backward.isDefEq.respectTransparency true

private theorem ninth_not_kernel :
    outsideRepresentative matrixA_mul_self matrixB_pow_four 9 ∉ max1Kernel := by
  intro h
  let q : M := (localX matrixA_mul_self matrixB_pow_four * localY matrixA_mul_self matrixB_pow_four)^7
  have hr : outsideRepresentative matrixA_mul_self matrixB_pow_four 9 = q * kernelValue 254 := rfl
  have hq : q ∈ max1Kernel := by
    have hh := max1Kernel.mul_mem h (maskValue matrixA_mul_self matrixB_pow_four 254).property
    rw [hr,mul_assoc,kernelValue_square,mul_one] at hh
    exact hh
  let : IsElementaryAbelian 2 max1Kernel := localKernel_elementary _ _
  have hs := elemPow_eq_one_of_isElementaryAbelian (p := 2) q hq
  have he : q^2 = seed := by
    change ((localX matrixA_mul_self matrixB_pow_four * localY matrixA_mul_self matrixB_pow_four)^7)^2 = _
    rw [← pow_mul]
    rfl
  rw [he] at hs
  have ho := seed_order
  rw [congrArg (fun u : M => (u : Model)) hs,Subgroup.coe_one,orderOf_one] at ho
  contradiction

/-- No Mathieu conjugate of a pure native-pair extension contains the ninth
outside lift. This obstruction uses the actual lift and both kernel generators. -/
theorem ninth_not_in_pure_extension (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x) (g : M) :
    (outsideRepresentative matrixA_mul_self matrixB_pow_four 9 : Model) ∉
      X.map (MulAut.conj (g : Model)).toMonoidHom := by
  intro ht
  let Y := X.map (MulAut.conj (g : Model)).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  have hpY : ∀ y ∈ Y, y ≠ 1 → IsConj a y := by
    rintro y ⟨v,hv,rfl⟩ hy
    exact (hpure v hv (fun he => hy (by rw [he,map_one]))).trans
      (isConj_iff.mpr ⟨(g : Model),rfl⟩)
  have hm (m : ℕ) : SylowCore.starMask (starHom g) m < 2048 :=
    SylowCore.Transport.starMask_lt _ _
  let m0 : Fin 2048 := ⟨SylowCore.starMask (starHom g) 818,hm 818⟩
  let m1 : Fin 2048 := ⟨SylowCore.starMask (starHom g) 1449,hm 1449⟩
  have hc (m : ℕ) : (MulAut.conj (g : Model)) (kernelValue m : Model) =
      (kernelValue (SylowCore.starMask (starHom g) m) : Model) := by
    exact congrArg (fun u : M => (u : Model)) (kernel_conjugation g m)
  have h0 : (kernelValue m0.val : Model) ∈ Y :=
    (hc 818) ▸ mem_map_of_mem (MulAut.conj (g : Model)).toMonoidHom
      (hpair (subset_closure (by simp)))
  have h1 : (kernelValue m1.val : Model) ∈ Y :=
    (hc 1449) ▸ mem_map_of_mem (MulAut.conj (g : Model)).toMonoidHom
      (hpair (subset_closure (by simp)))
  have hp0 : IsConj a (kernelValue m0.val : Model) :=
    first_is_first.trans (isConj_iff.mpr ⟨(g : Model),hc 818⟩)
  have hp1 : IsConj a (kernelValue m1.val : Model) :=
    second_is_first.trans (isConj_iff.mpr ⟨(g : Model),hc 1449⟩)
  have select (m : Fin 2048) (hx : (kernelValue m.val : Model) ∈ Y)
      (hp : IsConj a (kernelValue m.val : Model)) : ∃ j : Fin 7, m.val = ninthPureMask j := by
    have hprod : ((outsideRepresentative matrixA_mul_self matrixB_pow_four 9 * kernelValue m.val : M) : Model) ∈ Y :=
      Y.mul_mem ht hx
    have hn : ((outsideRepresentative matrixA_mul_self matrixB_pow_four 9 * kernelValue m.val : M) : Model) ≠ 1 := by
      intro he
      have he' : outsideRepresentative matrixA_mul_self matrixB_pow_four 9 * kernelValue m.val = 1 := Subtype.ext he
      have he'' := eq_inv_iff_mul_eq_one.mpr he'
      exact ninth_not_kernel (he''.symm ▸ max1Kernel.inv_mem (maskValue matrixA_mul_self matrixB_pow_four m.val).property)
    exact ninth_pure_kernel_mask m hp (hpY _ hprod hn)
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hprod)
  obtain ⟨i,hi⟩ := select m0 h0 hp0
  obtain ⟨j,hj⟩ := select m1 h1 hp1
  have hr := pairRank_conj (g : Model) (kernelValue 818) (kernelValue 1449)
  rw [hc 818,hc 1449,native_pairRank] at hr
  change pairRank (kernelValue m0.val) (kernelValue m1.val) = 20 at hr
  rw [hi,hj] at hr
  have hb := ninth_kernel_pairRank_le i j
  omega

/-- Every actual outside-kernel element in a pure extension of the native
pair is conjugate inside max1 to x. The alternative ninth lift is excluded. -/
theorem pure_extension_first_lift (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (z : M) (hz : (z : Model) ∈ X) (hk : z ∉ max1Kernel) :
    ∃ g : M, (MulAut.conj g) z = localX matrixA_mul_self matrixB_pow_four := by
  have hz1 : (z : Model) ≠ 1 := by
    intro he
    exact hk ((Subtype.ext he : z = 1).symm ▸ max1Kernel.one_mem)
  obtain ⟨i,g,hi,hg⟩ := first_lift_normal_form z hk (hpure _ hz hz1)
  rcases hi with rfl | rfl
  · refine ⟨g,?_⟩
    have he : outsideRepresentative matrixA_mul_self matrixB_pow_four 0 = localX matrixA_mul_self matrixB_pow_four := by
      simp [outsideRepresentative,outsideMask,binaryProduct_zero]
    exact hg.trans he
  · exact (ninth_not_in_pure_extension X hpair hpure g
      ((congrArg (fun u : M => (u : Model)) hg) ▸ mem_map_of_mem _ hz)).elim

/-- Maximality excludes the trivial image; the lift analysis then supplies
one actual x-marking, with all original subgroup and local-group transports. -/
theorem maximal_pure_first_lift_positioning (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    ∃ g : M,
      let Y := X.map (MulAut.conj (g : Model)).toMonoidHom
      nativePair.map (MulAut.conj (g : Model)).toMonoidHom ≤ Y ∧
      Y ≤ M ∧ centralizer (Y : Set Model) ≤ M ∧
      (localX matrixA_mul_self matrixB_pow_four : Model) ∈ Y ∧
      (∀ y ∈ Y, y ≠ 1 → IsConj a y) ∧
      IsMaximalTwoLocal (normalizer (Y : Set Model)) ∧
      centralizer (Y : Set Model) = (centralizer (X : Set Model)).map
        (MulAut.conj (g : Model)).toMonoidHom ∧
      normalizer (Y : Set Model) = (normalizer (X : Set Model)).map
        (MulAut.conj (g : Model)).toMonoidHom := by
  obtain ⟨i,g,hi,hP,hM,hC,hz,hp,hm,hct,hnt⟩ :=
    maximal_pure_extension_lift_positioning X hpair hpure hmax
  rcases hi with rfl | rfl
  · have he : outsideRepresentative matrixA_mul_self matrixB_pow_four 0 =
        localX matrixA_mul_self matrixB_pow_four := by
      simp [outsideRepresentative,outsideMask,binaryProduct_zero]
    exact ⟨g,hP,hM,hC,he ▸ hz,hp,hm,hct,hnt⟩
  · exact (ninth_not_in_pure_extension X hpair hpure g hz).elim

/-- Every nonidentity element of the literal Mathieu image is fixed-point-free.
The conclusion follows from its actual first-class lift, not from its order. -/
theorem pure_extension_image_fixed_point_free (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (p : StarGroup) (hp : p ∈ (X.subgroupOf M).map starHom) (hp1 : p ≠ 1) :
    ∀ i : Fin 24, p.val i ≠ i := by
  obtain ⟨z,hz,rfl⟩ := hp
  have hk : z ∉ max1Kernel := by
    intro hk
    apply hp1
    exact MonoidHom.mem_ker.mp (starHom_ker.symm ▸ hk)
  obtain ⟨g,hg⟩ := pure_extension_first_lift X hpair hpure z hz hk
  have hq := congrArg starHom hg
  have hx : (starHom (localX matrixA_mul_self matrixB_pow_four)).val = starX :=
    actionImageEquivStarGroup_x _ _
  intro i hi
  have he := congrArg (fun u : StarGroup => u.val ((starHom g).val i)) hq
  have hc : ((starHom ((MulAut.conj g) z)).val) ((starHom g).val i) =
      (starHom g).val ((starHom z).val i) := by
    simp only [MulAut.conj_apply,map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv,
      Equiv.Perm.mul_apply,Equiv.Perm.inv_def,Equiv.symm_apply_apply]
  rw [hc,hi,hx] at he
  have hn : ∀ i : Fin 24, starX i ≠ i := by decide +kernel
  exact hn _ he.symm

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
