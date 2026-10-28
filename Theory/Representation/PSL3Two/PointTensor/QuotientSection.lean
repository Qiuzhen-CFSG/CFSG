module

public import Theory.Representation.PSL3Two.PointTensor

/-!
# Surjections from the Fano point tensor

An equivariant surjection from an external tensor with the binary natural
S₃-module induces a surjection on the inverter-fixed multiplicity modules.
This follows from the explicit two-coordinate inverted-cubic decomposition,
and does not require exactness of fixed points in characteristic two.

For the actual seven-point permutation representation, every SL₃(2)
displacement has augmentation zero. Thus a quotient with nontrivial SL₃(2)
action has a nonzero image of the point-core tensor. These two facts let the
point core's natural simple head identify a chief quotient of that image.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.21(1), printed p.957, and the point-core structure in H.5–H.6.
-/

public section

open Representation InvertedCubicTensor
open scoped TensorProduct
namespace BinaryLinearThree.PointTensor.QuotientSection

abbrev Natural := BinaryPermutation.core (Fin 3)
abbrev naturalAction := BinaryPermutation.coreRepresentation (Fin 3)

@[expose] noncomputable def tensor {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    (α : Representation (ZMod 2) Group A) :=
  Representation.tprod (α.comp (MonoidHom.fst Group S₃))
    (naturalAction.comp (MonoidHom.snd Group S₃))

private def n0 : Natural := ⟨![1,1,0], by
  rw [BinaryPermutation.mem_core, Fin.sum_univ_three]
  decide⟩

private theorem n0_fixed : naturalAction inverter n0 = n0 := by decide +kernel

private theorem natural_decompose (n : Natural) :
    n = n.val 0 • n0 + n.val 2 • naturalAction cubic n0 := by
  have hn := n.property
  rw [BinaryPermutation.mem_core, Fin.sum_univ_three] at hn
  have hmid : n.val 1 = n.val 0 + n.val 2 := by
    have hdouble (a : ZMod 2) : a + a = 0 := by
      have h : (2 : ZMod 2) = 0 := rfl
      simpa only [two_mul, h, zero_mul] using (two_mul a).symm
    have h := congrArg (fun a : ZMod 2 => a + (n.val 0 + n.val 2)) hn
    have he : n.val 0 + n.val 1 + n.val 2 + (n.val 0 + n.val 2) = n.val 1 := by
      calc
        _ = n.val 1 + (n.val 0 + n.val 0) + (n.val 2 + n.val 2) := by abel
        _ = _ := by rw [hdouble, hdouble, add_zero, add_zero]
    simpa only [he, zero_add] using h
  apply Subtype.ext
  funext i
  fin_cases i
  · change n.val 0 = n.val 0 * 1 + n.val 2 * 0
    simp
  · change n.val 1 = n.val 0 * 1 + n.val 2 * 1
    simpa using hmid
  · change n.val 2 = n.val 0 * 0 + n.val 2 * 1
    simp

private theorem natural_norm (n : Natural) :
    n + naturalAction cubic n + naturalAction cubic (naturalAction cubic n) = 0 := by
  have hn := n.property
  rw [BinaryPermutation.mem_core, Fin.sum_univ_three] at hn
  apply Subtype.ext
  funext i
  fin_cases i
  · change n.val 0 + n.val 2 + n.val 1 = 0
    calc
      _ = n.val 0 + n.val 1 + n.val 2 := by abel
      _ = 0 := hn
  · change n.val 1 + n.val 0 + n.val 2 = 0
    calc
      _ = n.val 0 + n.val 1 + n.val 2 := by abel
      _ = 0 := hn
  · change n.val 2 + n.val 1 + n.val 0 = 0
    calc
      _ = n.val 0 + n.val 1 + n.val 2 := by abel
      _ = 0 := hn

variable {A U : Type*} [AddCommGroup A] [Module (ZMod 2) A]
  [AddCommGroup U] [Module (ZMod 2) U]
  (α : Representation (ZMod 2) Group A)

private theorem tensor_decompose (z : A ⊗[ZMod 2] Natural) :
    ∃ a b : A, z = a ⊗ₜ[ZMod 2] n0 + b ⊗ₜ[ZMod 2] naturalAction cubic n0 := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a n =>
    refine ⟨n.val 0 • a, n.val 2 • a, ?_⟩
    conv_lhs => rw [natural_decompose n]
    simp only [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.smul_tmul]
  | add z w hz hw =>
    obtain ⟨a,b,rfl⟩ := hz
    obtain ⟨c,d,rfl⟩ := hw
    exact ⟨a+c,b+d, by simp only [TensorProduct.add_tmul]; abel⟩

/-- The cubic factor has no fixed vectors on any external tensor with its natural module. -/
theorem tensor_fixedFree : ∀ z, rightAction (tensor α) cubic z = z → z = 0 := by
  have hn (z : A ⊗[ZMod 2] Natural) :
      z + tensor α (1,cubic) z + tensor α (1,cubic) (tensor α (1,cubic) z) = 0 := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a n =>
      change a ⊗ₜ n + α 1 a ⊗ₜ naturalAction cubic n +
        α 1 (α 1 a) ⊗ₜ naturalAction cubic (naturalAction cubic n) = 0
      simp only [map_one, Module.End.one_apply, ← TensorProduct.tmul_add, natural_norm,
        TensorProduct.tmul_zero]
    | add z w hz hw =>
      simp only [map_add]
      calc
        _ = (z + tensor α (1,cubic) z + tensor α (1,cubic) (tensor α (1,cubic) z)) +
          (w + tensor α (1,cubic) w + tensor α (1,cubic) (tensor α (1,cubic) w)) := by abel
        _ = 0 := by rw [hz, hw, add_zero]
  intro z hz
  have h := hn z
  change tensor α (1,cubic) z = z at hz
  rw [hz, hz] at h
  have hd : z + z = 0 := by
    simpa only [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul, one_smul] using
      (add_smul (1 : ZMod 2) 1 z).symm
  simpa only [hd, zero_add] using h

variable (ρ : Representation (ZMod 2) Actor U)
  (q : (tensor α).IntertwiningMap ρ)

/-- A tensor map induces the component map on transposition-fixed multiplicities. -/
noncomputable def onMultiplicity : α.IntertwiningMap (productMultiplicity ρ) where
  toLinearMap := (q.toLinearMap.comp ((TensorProduct.mk (ZMod 2) A Natural).flip n0)).codRestrict
    (multiplicitySpace (rightAction ρ)) (by
      intro a
      rw [mem_multiplicitySpace]
      change ρ (1,inverter) (q (a ⊗ₜ n0)) = q (a ⊗ₜ n0)
      rw [← q.isIntertwining]
      change q (α 1 a ⊗ₜ naturalAction inverter n0) = _
      rw [map_one, Module.End.one_apply, n0_fixed])
  isIntertwining' g := by
    ext a
    change q (α g a ⊗ₜ n0) = ρ (g,1) (q (a ⊗ₜ n0))
    rw [← q.isIntertwining]
    change _ = q (α g a ⊗ₜ naturalAction 1 n0)
    rw [map_one, Module.End.one_apply]

/-- A surjective tensor map is surjective on multiplicities. The two coordinates
in the inverted-cubic decomposition prove this even in characteristic two. -/
theorem onMultiplicity_surjective (hq : Function.Surjective q) :
    Function.Surjective (onMultiplicity α ρ q) := by
  have hf : ∀ v, rightAction ρ cubic v = v → v = 0 :=
    fixedFree_of_surjective (rightAction (tensor α)) (rightAction ρ) q.toLinearMap hq
      (fun z => LinearMap.congr_fun (q.isIntertwining' (1,cubic)) z) (tensor_fixedFree α)
  let e := pairEquiv (rightAction ρ) hf
  intro v
  obtain ⟨z, hz⟩ := hq v.val
  obtain ⟨a,b,rfl⟩ := tensor_decompose z
  have he : e (onMultiplicity α ρ q a, onMultiplicity α ρ q b) = e (v,0) := by
    rw [pairEquiv_apply, pairEquiv_apply]
    simp only [ZeroMemClass.coe_zero, map_zero, add_zero]
    change q (a ⊗ₜ n0) + ρ (1,cubic) (q (b ⊗ₜ n0)) = v.val
    rw [← q.isIntertwining]
    change q (a ⊗ₜ n0) + q (α 1 b ⊗ₜ naturalAction cubic n0) = v.val
    rw [map_one, Module.End.one_apply, ← map_add]
    exact hz
  exact ⟨a, congrArg Prod.fst (e.injective he)⟩


open BinaryLinearThree.FanoDecomposition

/-- The actual inclusion of the point core, tensored with the identity on the S₃ module. -/
noncomputable def coreInclusion : (tensor U₂).IntertwiningMap pointTensor :=
  (show Representation.IntertwiningMap (U₂.comp (MonoidHom.fst Group S₃))
      (FanoCoreStructure.pointRepresentation.comp (MonoidHom.fst Group S₃)) from
    ⟨(BinaryPermutation.core Point).subtype, fun _ => rfl⟩).tensor
      (IntertwiningMap.id (naturalAction.comp (MonoidHom.snd Group S₃)))

/-- Component nontriviality forces the image of the point-core tensor to survive.
Every component displacement in the point permutation module has augmentation zero. -/
theorem core_map_ne_zero (q : pointTensor.IntertwiningMap ρ)
    (hq : Function.Surjective q) (hn : ∃ k : Group, ∃ v, ρ (k,1) v ≠ v) :
    q.comp coreInclusion ≠ 0 := by
  intro hz
  obtain ⟨k,v,hv⟩ := hn
  obtain ⟨z,rfl⟩ := hq v
  apply hv
  have h (z : BinaryPermutation.Full Point ⊗[ZMod 2] Natural) :
      ρ (k,1) (q z) = q z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a n =>
      let d : Core := ⟨FanoCoreStructure.pointRepresentation k a - a, by
        change BinaryPermutation.augmentation Point _ = 0
        rw [map_sub]
        exact sub_eq_zero.mpr (BinaryPermutation.augmentation_permute Point (pointPerm k) a)⟩
      have hd := congrArg (fun f : (tensor U₂).IntertwiningMap ρ => f (d ⊗ₜ n)) hz
      change q ((FanoCoreStructure.pointRepresentation k a - a) ⊗ₜ n) = 0 at hd
      rw [TensorProduct.sub_tmul, map_sub, sub_eq_zero] at hd
      rw [← q.isIntertwining]
      change q (FanoCoreStructure.pointRepresentation k a ⊗ₜ naturalAction 1 n) = _
      rw [map_one, Module.End.one_apply]
      exact hd
    | add x y hx hy => simp only [map_add, hx, hy]
  exact h z

end BinaryLinearThree.PointTensor.QuotientSection
