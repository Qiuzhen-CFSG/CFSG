module
public import Theory.Representation.ScalarMultiplicity.Kernel
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Displacement on a scalar multiplicity space

For a homogeneous sum of natural planes over an extension field, exchanging
the copy and plane coordinates writes every scalar multiplicity operator as
two equal operators. Its displacement over the base field is therefore twice
the extension degree times its displacement over the scalar field. The proof
uses the actual pure-tensor action equation and retains the full action.

Source application: Aschbacher–Smith 8.2.9, printed p.721,
refs/quasithin.pdf. The original Hermitian chief action consumes this identity
in Chapter8.Section02.HermitianSourceFieldFourChiefMultiplicity.
-/

public noncomputable section
namespace Representation.ScalarMultiplicity
open Module BinaryOffender.NaturalTensor
variable {k F C I : Type*} [Field k] [Field F] [Algebra k F]
  [FiniteDimensional k F] [Group C] [Fintype I] [DecidableEq I]

/-- On copies of a natural plane, scalar multiplicity displacement is multiplied
by twice the scalar-field degree when measured over the original field. -/
theorem natural_plane_displacement
    (ρ : Representation k C (I → (Fin 2 → F)))
    (μ : Representation F C (I → F))
    (he : ∀ a c v, ρ a (fun i => c i • v) = fun i => μ a c i • v)
    (a : C) :
    finrank k (LinearMap.range (ρ a - 1)) =
      2 * finrank k F * finrank F (LinearMap.range (μ a - 1)) := by
  let e : (I → (Fin 2 → F)) ≃ₗ[k] (I → F) × (I → F) := {
    toFun x := (fun i => x i 0, fun i => x i 1)
    invFun x i := ![x.1 i, x.2 i]
    left_inv x := by funext i j; fin_cases j <;> rfl
    right_inv x := rfl
    map_add' x y := rfl
    map_smul' c x := rfl }
  let A := (μ a).restrictScalars k
  have hdiag (x : I → (Fin 2 → F)) : e (ρ a x) = A.prodMap A (e x) := by
    have hx : x = (fun i => x i 0 • ![(1 : F),0]) +
        (fun i => x i 1 • ![(0 : F),1]) := by
      funext i j
      fin_cases j <;> simp
    conv_lhs => rw [hx,map_add,he,he]
    apply Prod.ext
    · funext i
      change μ a (fun i => x i 0) i * 1 + μ a (fun i => x i 1) i * 0 = _
      simp only [mul_one,mul_zero,add_zero]
      rfl
    · funext i
      change μ a (fun i => x i 0) i * 0 + μ a (fun i => x i 1) i * 1 = _
      simp only [mul_one,mul_zero,zero_add]
      rfl
  have hd := operatorFixedCodim_eq_of_equiv (ρ a) (A.prodMap A) e hdiag
  let P := LinearMap.range (A - 1)
  have hi : Function.Injective (P.subtype.prodMap P.subtype) := by
    rintro ⟨x,y⟩ ⟨x',y'⟩ h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  have hprod := LinearMap.finrank_range_of_inj (f := P.subtype.prodMap P.subtype) hi
  rw [LinearMap.range_prodMap,Submodule.range_subtype,Module.finrank_prod] at hprod
  have ha : A.prodMap A - 1 = (A - 1).prodMap (A - 1) := by ext x <;> rfl
  change finrank k (LinearMap.range (ρ a - 1)) =
    finrank k (LinearMap.range (A.prodMap A - 1)) at hd
  rw [ha,LinearMap.range_prodMap,hprod] at hd
  let b : P ≃ₗ[k] LinearMap.range (μ a - 1) := {
    toFun x := ⟨x,x.property⟩
    invFun x := ⟨x,x.property⟩
    left_inv x := rfl
    right_inv x := rfl
    map_add' x y := rfl
    map_smul' c x := rfl }
  have hfield := Module.finrank_mul_finrank k F (LinearMap.range (μ a - 1))
  rw [←b.finrank_eq] at hfield
  change finrank k (LinearMap.range (ρ a - 1)) = finrank k P + finrank k P at hd
  rw [←hfield] at hd
  nlinarith [hd]
end Representation.ScalarMultiplicity
