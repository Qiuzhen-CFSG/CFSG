module
public import Theory.Representation.BinaryEndpointInduction.QuotientRecognition
public import Theory.Representation.BinaryEndpointInduction.CosetLift

/-!
# Whole-group action on the recognized endpoint survivor

The equivalence supplied by the exact invariant-kernel calculation is
composed with the checked survivor basis change. Surjectivity of the
original induced map gives the two generator equations. The literal shear
and cycle generate the whole group, so the equation holds for every actual
component element, with the inverse required by the right-row convention.
-/
public noncomputable section
open Matrix Representation
open scoped MatrixGroups
namespace BinaryEndpointInduction
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

private def rowEquiv {n : ℕ} (A B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hAB : A*B=1) (hBA : B*A=1) :
    (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
  LinearEquiv.ofLinearMap A.vecMulLinear B.vecMulLinear
    (by apply LinearMap.ext; intro x; change (x ᵥ* B) ᵥ* A=x; rw [vecMul_vecMul,hBA,vecMul_one])
    (by apply LinearMap.ext; intro x; change (x ᵥ* A) ᵥ* B=x; rw [vecMul_vecMul,hAB,vecMul_one])

private def rowRepresentation (dual : Bool) :
    Representation (ZMod 2) SL(4,ZMod 2) (Fin (if dual then 4 else 6) → ZMod 2) where
  toFun g := (survivorModel dual g⁻¹).vecMulLinear
  map_one' := by apply LinearMap.ext; intro x; simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    change x ᵥ* survivorModel dual ((g*h)⁻¹)=
      (x ᵥ* survivorModel dual h⁻¹) ᵥ* survivorModel dual g⁻¹
    rw [_root_.mul_inv_rev,map_mul,vecMul_vecMul]

private theorem generator_equation
    (dual : Bool) (τ : Representation (ZMod 2) SL(4,ZMod 2) W)
    (F : (Fin 45 → ZMod 2) →ₗ[ZMod 2] W)
    (hF : Function.Surjective F)
    (hact : ∀ (a : Fin 6) (x : Fin 45 → ZMod 2),
      F (x ᵥ* inducedCosetMatrix dual a)=τ ((cosetActor a)⁻¹) (F x))
    (E : W ≃ₗ[ZMod 2] (Fin (if dual then 4 else 6) → ZMod 2))
    (hE : ∀ x, E (F (x ᵥ* changeMatrix dual))=survivorProjection dual x)
    (k : Fin 2) (w : W) :
    E (τ ((survivorActor k)⁻¹) w)=E w ᵥ* survivorGenerator dual k := by
  obtain ⟨v,rfl⟩ := hF w
  let x := v ᵥ* inverseChangeMatrix dual
  have hx : x ᵥ* changeMatrix dual=v := by
    dsimp only [x]
    rw [vecMul_vecMul,(change_inverse dual).2,vecMul_one]
  have hk : cosetActor ⟨k.val,by omega⟩=survivorActor k := by fin_cases k <;> rfl
  rw [←hx,←hk,←hact,inducedCosetMatrix_generators]
  rw [vecMul_vecMul,generator_intertwine,←vecMul_vecMul,hE,hE]
  exact survivorProjection_intertwine dual k x

/-- The survivor equivalence can be chosen to intertwine the whole actual
component with its natural-four or exterior-six model. -/
theorem exists_standard_survivor_equivalence
    (dual : Bool) (τ : Representation (ZMod 2) SL(4,ZMod 2) W)
    (F : (Fin 45 → ZMod 2) →ₗ[ZMod 2] W)
    (hF : Function.Surjective F)
    (hact : ∀ (a : Fin 6) (x : Fin 45 → ZMod 2),
      F (x ᵥ* inducedCosetMatrix dual a)=τ ((cosetActor a)⁻¹) (F x))
    (E : W ≃ₗ[ZMod 2] (Fin (if dual then 4 else 6) → ZMod 2))
    (hE : ∀ x, E (F (x ᵥ* changeMatrix dual))=survivorProjection dual x) :
    ∃ J : W ≃ₗ[ZMod 2] (Fin (if dual then 4 else 6) → ZMod 2),
      (∀ w, J w=E w ᵥ* survivorChange dual) ∧
      ∀ (g : SL(4,ZMod 2)) (w : W),
        J (τ g w)=J w ᵥ* survivorModelMatrix dual g⁻¹ := by
  let J := E.trans (rowEquiv (survivorChange dual) (survivorChangeInverse dual)
    (survivorChange_inverse dual).1 (survivorChange_inverse dual).2)
  have hJ (w : W) : J w=E w ᵥ* survivorChange dual := rfl
  have hgen (k : Fin 2) (w : W) :
      J (τ ((survivorActor k)⁻¹) w)=J w ᵥ* survivorModelMatrix dual (survivorActor k) := by
    rw [hJ,generator_equation dual τ F hF hact E hE,hJ,vecMul_vecMul,
      survivorGenerator_intertwine,vecMul_vecMul]
  let ρ := (J.conjAlgEquiv (ZMod 2)).toMonoidHom.comp τ
  have hi (k : Fin 2) : ρ ((survivorActor k)⁻¹)=rowRepresentation dual ((survivorActor k)⁻¹) := by
    apply LinearMap.ext
    intro x
    change J (τ ((survivorActor k)⁻¹) (J.symm x))=
      x ᵥ* survivorModel dual (((survivorActor k)⁻¹)⁻¹)
    rw [hgen,J.apply_symm_apply,inv_inv]
    rfl
  have he (k : Fin 2) : ρ (survivorActor k)=rowRepresentation dual (survivorActor k) := by
    have h1 := congrArg (fun f => ρ (survivorActor k)*f) (hi k)
    rw [←map_mul,mul_inv_cancel,map_one] at h1
    have h2 := congrArg (fun f => f*rowRepresentation dual (survivorActor k)) h1
    simpa only [one_mul,mul_assoc,←map_mul,inv_mul_cancel,map_one,mul_one] using h2.symm
  have hall : ρ=rowRepresentation dual := MonoidHom.eq_of_eqOn_dense generator_closure (by
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact he 0
    · have hh : a=cycleGenerator := Set.mem_singleton_iff.mp ha
      subst a
      exact he 1)
  refine ⟨J,hJ,?_⟩
  intro g w
  have hh := LinearMap.congr_fun (DFunLike.congr_fun hall g) (J w)
  change J (τ g (J.symm (J w)))=J w ᵥ* survivorModel dual g⁻¹ at hh
  rwa [J.symm_apply_apply] at hh

end BinaryEndpointInduction
