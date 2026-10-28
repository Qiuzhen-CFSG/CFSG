module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.PureSecond.Pairs
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.SecondKernelPairs

/-!
# Intrinsic outer-half symmetry and the native invariant form

Every commuting pair of involutions has symmetric membership in the embedded
solvable residuals of its full centralizers. The first-class census handles
mixed pairs. In the second centralizer the elementary kernel branch is already
inner in both directions; the outside census and certified first-class bridges
handle all other pairs. The resulting alternating binary form is therefore
unconditional and invariant under the literal elementary-subgroup normalizer.

Source: Kleidman--Wilson (1988), p.487, Corollary 1.1.4. This supplies the
symmetry premise of the native elementary-normalizer-cover argument; radical
coverage and surviving normalizer quotients are separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
open Janko4.Cardinality Janko4.Simplicity.Max1Fusion
open Janko4.InvolutionCentralizers.Second
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel localKernelSeed

private theorem seed_isConj_standard : IsConj (seed : Model) ((Janko4.a * Janko4.b * Janko4.a * Janko4.b * Janko4.b)^5) := by
  obtain ⟨g, hg⟩ := seed_fuses_second matrixA_mul_self matrixB_pow_four
  have ha : Simplicity.a matrixA_mul_self = Janko4.a := by apply toMatrix_injective; rfl
  have hb : Simplicity.b matrixB_pow_four = Janko4.b := by apply toMatrix_injective; rfl
  have hw : Simplicity.word Janko4.a Janko4.b "ababb" = Janko4.a * Janko4.b * Janko4.a * Janko4.b * Janko4.b := by
    simp [Simplicity.word, mul_assoc]
  rw [ha, hb, hw] at hg
  exact isConj_iff.mpr ⟨g, hg.symm⟩

/-- Symmetry throughout the full centralizer of the second-class seed. -/
theorem second_centralizer_symmetry (y : Model) (hy : orderOf y = 2)
    (hc : Commute (seed : Model) y) :
    InnerRelated (seed : Model) y ↔ InnerRelated y (seed : Model) := by
  let u : InvolutionCentralizers.Second.Local :=
    ⟨y, ambient_le_max1 (mem_centralizer_singleton_iff.mpr hc.eq.symm)⟩
  by_cases hk : u ∈ max1Kernel
  · rcases OuterReduction.involution_isConj_of_max1_odd_index
      OuterReduction.max1_odd_index_unconditional hy with ha | hb
    · exact (innerRelated_symm_of_first y _ ha seed_order hc.symm).symm
    · have hpair := second_kernel_pair_inner u hk (seed_isConj_standard.trans hb)
      exact ⟨fun _ => hpair.2, fun _ => hpair.1⟩
  · have hu : orderOf u = 2 :=
      (orderOf_injective (max1Subgroup matrixA_mul_self matrixB_pow_four).subtype
        Subtype.val_injective u).symm.trans hy
    obtain ⟨i, g, hg⟩ := outside_coverage_of_quotient_and_fibers matrixA_mul_self matrixB_pow_four
      (quotient_involution_coverage _ _) (involution_fibers _ _) u hk hu
    have hs : g * seed * g⁻¹ ∈ max1Kernel :=
      (inferInstance : max1Kernel.Normal).conj_mem _ (localKernelSeed_mem _ _) g
    obtain ⟨m, hm⟩ := KernelOrbits.maskValue_surjective matrixA_mul_self matrixB_pow_four ⟨_, hs⟩
    let e := MulAut.conj (g : Model)
    have hx' : (((KernelOrbits.maskValue matrixA_mul_self matrixB_pow_four m.val).val) : Model) = e (seed : Model) :=
      congrArg (fun k : max1Kernel => (k.val : Model)) hm
    have hy' : (outsideRepresentative matrixA_mul_self matrixB_pow_four i : Model) = e y :=
      congrArg Subtype.val hg
    have ho : orderOf (e (seed : Model)) = 2 := (e.orderOf_eq _).trans seed_order
    have ho' : orderOf (e y) = 2 := (e.orderOf_eq _).trans hy
    have hc' : Commute (e (seed : Model)) (e y) := hc.map e.toMonoidHom
    have hh := PureSecond.outside_kernel_symmetry i m (hx'.symm ▸ ho) (hy'.symm ▸ ho')
      (by simpa only [hx', hy'] using hc')
    rw [hx', hy'] at hh
    exact (innerRelated_equiv e (seed : Model) y).symm.trans
      (hh.trans (innerRelated_equiv e y (seed : Model)))

/-- Full intrinsic commuting-involution symmetry in the native J₄ model. -/
theorem innerRelated_symm (x y : Model) (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hc : Commute x y) : InnerRelated x y ↔ InnerRelated y x := by
  rcases OuterReduction.involution_isConj_of_max1_odd_index
    OuterReduction.max1_odd_index_unconditional hx with ha | hb
  · exact innerRelated_symm_of_first x y ha hy hc
  · obtain ⟨g, hg⟩ := isConj_iff.mp (seed_isConj_standard.trans hb)
    let e := MulAut.conj g⁻¹
    have hx' : e x = (seed : Model) := by
      rw [← hg]
      simp [e, mul_assoc]
    have hy' : orderOf (e y) = 2 := (e.orderOf_eq y).trans hy
    have hc' : Commute (seed : Model) (e y) := by
      simpa only [MulEquiv.coe_toMonoidHom, hx'] using hc.map e.toMonoidHom
    have hh := second_centralizer_symmetry (e y) hy' hc'
    rw [← hx'] at hh
    exact (innerRelated_equiv e x y).symm.trans (hh.trans (innerRelated_equiv e y x))

variable (X : Subgroup Model) [IsElementaryAbelian 2 X]

/-- The canonical outer-half form, with its intrinsic symmetry fully discharged. -/
@[expose] def intrinsicElementaryForm : LinearMap.BilinForm (ZMod 2) (Additive X) :=
  elementaryForm X innerRelated_symm

@[simp] theorem intrinsicElementaryForm_apply (x y : Additive X) :
    intrinsicElementaryForm X x y = outerValue x.toMul y.toMul := rfl

theorem intrinsicElementaryForm_isAlt : (intrinsicElementaryForm X).IsAlt :=
  elementaryForm_isAlt X innerRelated_symm

theorem intrinsicElementaryForm_isSymm : (intrinsicElementaryForm X).IsSymm :=
  elementaryForm_isSymm X innerRelated_symm

/-- For a nonidentity first entry, zero means membership in the actual full
centralizer's embedded solvable residual. -/
theorem intrinsicElementaryForm_eq_zero_iff (x y : Additive X) (hx : x ≠ 0) :
    intrinsicElementaryForm X x y = 0 ↔ InnerRelated x.toMul y.toMul :=
  elementaryForm_eq_zero_iff X innerRelated_symm x y hx

/-- Simultaneous ambient conjugacy preserves the form and its literal embeddings. -/
theorem intrinsicElementaryForm_equiv (Y : Subgroup Model) [IsElementaryAbelian 2 Y]
    (e : Model ≃* Model) (f : X ≃* Y) (hf : ∀ x : X, (f x : Model) = e x)
    (x y : Additive X) :
    intrinsicElementaryForm Y (Additive.ofMul (f x.toMul)) (Additive.ofMul (f y.toMul)) =
      intrinsicElementaryForm X x y :=
  elementaryForm_equiv X innerRelated_symm Y e f hf x y

/-- The actual ambient normalizer preserves the intrinsic form. -/
theorem intrinsicElementaryForm_normalizer (g : normalizer (X : Set Model)) (x y : Additive X) :
    intrinsicElementaryForm X (Additive.ofMul (g • x.toMul)) (Additive.ofMul (g • y.toMul)) =
      intrinsicElementaryForm X x y :=
  elementaryForm_normalizer X innerRelated_symm g x y

end Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
