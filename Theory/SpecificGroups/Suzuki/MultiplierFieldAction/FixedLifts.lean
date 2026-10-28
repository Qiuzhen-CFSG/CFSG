module

public import Theory.SpecificGroups.Suzuki.MultiplierFieldAction.LocalCover
public import Theory.SpecificGroups.Suzuki.FieldAutomorphism
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Fixed fibers of the canonical lifted Sz(8) field automorphism

The unique universal lift has cube one and preserves the full standard
root preimage. If it fixes the four-element covering kernel pointwise,
every element above a field-fixed element is fixed: its displacement is
a fixed kernel element with both cube and fourth power one.

This supplies the coprime fixed-point lifting step of GLS3 section 6.3,
printed p.337, using the literal canonical lift. Trivial kernel action is
explicit here; deriving a contradiction from it is the remaining source
argument, not an assumption of a completed multiplier-action theorem.
-/

namespace BenderSuzuki.MatrixGroups.MultiplierFieldAction
open Subgroup Theory.GroupTheory PFAppendixIII

universe u
variable {S U : Type u}
variable [Group S] [Finite S] [IsQuasisimple S]
variable [Group U] [Finite U] [IsQuasisimple U]

/-- The unique lift of the actual entrywise Frobenius, transported by e. -/
@[expose] public noncomputable def liftedField
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hf : Covering.IsUniversal.{u,u,u} f) : MulAut U :=
  hf.liftMulAut (MulAut.congr e.symm (suzukiFieldAutomorphism 1))

/-- Transport and the homomorphism of unique lifts preserve the cubic relation. -/
public theorem liftedField_cube
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hf : Covering.IsUniversal.{u,u,u} f) : liftedField e f hf ^ 3 = 1 := by
  have hbase : MulAut.congr e.symm (suzukiFieldAutomorphism 1) ^ 3 = 1 := by
    rw [← map_pow, suzukiFieldAutomorphism_one_cube, map_one]
  have h := congrArg (fun a : Covering.kernelStabilizer f => a.val)
    (show hf.liftMulAutToStabilizer
      (MulAut.congr e.symm (suzukiFieldAutomorphism 1)) ^ 3 = 1 by
        rw [← map_pow, hbase, map_one])
  exact h

/-- The original matrix projection intertwines the lifted and actual field maps. -/
@[simp] public theorem matrixProjection_liftedField
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hf : Covering.IsUniversal.{u,u,u} f) (x : U) :
    matrixProjection e f (liftedField e f hf x) =
      suzukiFieldAutomorphism 1 (matrixProjection e f x) := by
  have h := congrArg (fun q : Covering U S => q x)
    (hf.liftMulAut_fac (MulAut.congr e.symm (suzukiFieldAutomorphism 1)))
  change f (liftedField e f hf x) = e.symm (suzukiFieldAutomorphism 1 (e (f x))) at h
  change e (f (liftedField e f hf x)) = suzukiFieldAutomorphism 1 (e (f x))
  rw [h, e.apply_symm_apply]

private theorem field_mem_root {x : SuzukiMatrixGroup 1}
    (hx : x ∈ SuzukiRootSubgroup 1) :
    suzukiFieldAutomorphism 1 x ∈ SuzukiRootSubgroup 1 := by
  obtain ⟨a, b, hab⟩ := (mem_suzukiRootSubgroup_iff 1 x).mp hx
  apply (mem_suzukiRootSubgroup_iff 1 _).mpr
  let σ := frobenius (BinaryGaloisField 3) 2
  refine ⟨σ a, σ b, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [suzukiFieldAutomorphism_entry]
  rw [hab]
  exact congrArg (fun z : GL (Fin 4) (BinaryGaloisField 3) =>
    (z : Matrix (Fin 4) (Fin 4) (BinaryGaloisField 3)) i j)
      (map_suzukiRootGL (d := 1) (n := 1) (dvd_refl _) σ a b)

/-- The standard root group is invariant under the specified field automorphism. -/
public theorem field_mem_root_iff (x : SuzukiMatrixGroup 1) :
    suzukiFieldAutomorphism 1 x ∈ SuzukiRootSubgroup 1 ↔ x ∈ SuzukiRootSubgroup 1 := by
  refine ⟨fun hx => ?_, field_mem_root⟩
  have h3 := congrArg (fun a : MulAut (SuzukiMatrixGroup 1) => a x)
    suzukiFieldAutomorphism_one_cube
  change suzukiFieldAutomorphism 1 (suzukiFieldAutomorphism 1
    (suzukiFieldAutomorphism 1 x)) = x at h3
  exact h3 ▸ field_mem_root (field_mem_root hx)

/-- Full preimage gives an invariant Sylow without an extra choice of conjugate. -/
public theorem liftedField_mem_rootPreimage_iff
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hf : Covering.IsUniversal.{u,u,u} f) (x : U) :
    liftedField e f hf x ∈ rootPreimage e f ↔ x ∈ rootPreimage e f := by
  change matrixProjection e f (liftedField e f hf x) ∈ SuzukiRootSubgroup 1 ↔ _
  rw [matrixProjection_liftedField, field_mem_root_iff]
  rfl

private theorem fixed_of_cube_of_kernel_four
    {E B : Type*} [Group E] [Group B] [Finite E]
    (q : E →* B) (a : MulAut E) (ha : a ^ 3 = 1)
    (hfour : Nat.card q.ker = 4)
    (hfixed : ∀ k : q.ker, a k = (k : E))
    (x : E) (hx : q (a x) = q x) : a x = x := by
  let d := a x * x⁻¹
  have hd : d ∈ q.ker := by simp [d, MonoidHom.mem_ker, hx]
  have had : a d = d := hfixed ⟨d, hd⟩
  have hax : a x = d * x := by simp [d]
  have h3x : a (a (a x)) = x := congrArg (fun b : MulAut E => b x) ha
  have hd3 : d ^ 3 = 1 := by
    have hh : d ^ 3 * x = 1 * x := by
      calc
        d ^ 3 * x = a (a (a x)) := by
          simp only [map_mul, had, hax]
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 * x := by rw [h3x, one_mul]
    exact mul_right_cancel hh
  have hd4 : d ^ 4 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨d, hd⟩ : q.ker))
    rw [hfour] at hh
    exact congrArg Subtype.val hh
  have hd1 : d = 1 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hd3, one_mul] at hd4
    exact hd4
  rw [hax, hd1, one_mul]

/-- Under the contradiction assumption of trivial kernel action, fixed points
lift along the original matrix projection, and every lift is fixed. -/
public theorem liftedField_fixed_iff
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hf : Covering.IsUniversal.{u,u,u} f)
    (hfour : Nat.card f.toMonoidHom.ker = 4)
    (hfixed : ∀ k : f.toMonoidHom.ker, liftedField e f hf k = (k : U)) (x : U) :
    liftedField e f hf x = x ↔
      suzukiFieldAutomorphism 1 (matrixProjection e f x) = matrixProjection e f x := by
  constructor
  · intro hx
    rw [← matrixProjection_liftedField e f hf, hx]
  · intro hx
    apply fixed_of_cube_of_kernel_four (matrixProjection e f) (liftedField e f hf)
      (liftedField_cube e f hf) (by rwa [matrixProjection_ker])
    · intro k
      exact hfixed ⟨k, matrixProjection_ker e f ▸ k.property⟩
    · rwa [matrixProjection_liftedField]

/-- The pointwise fixed subgroup is exactly the full preimage of the actual
Frobenius fixed subgroup when the covering kernel is fixed pointwise. -/
public theorem liftedField_fixedSubgroup
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hf : Covering.IsUniversal.{u,u,u} f)
    (hfour : Nat.card f.toMonoidHom.ker = 4)
    (hfixed : ∀ k : f.toMonoidHom.ker, liftedField e f hf k = (k : U)) :
    (liftedField e f hf).fixedSubgroup =
      (suzukiFieldAutomorphism 1).fixedSubgroup.comap (matrixProjection e f) := by
  ext x
  simpa only [MulAut.mem_fixedSubgroup, Subgroup.mem_comap] using
    liftedField_fixed_iff e f hf hfour hfixed x

end BenderSuzuki.MatrixGroups.MultiplierFieldAction
