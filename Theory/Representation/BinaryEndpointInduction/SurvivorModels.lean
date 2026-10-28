module
public import Theory.Representation.BinaryEndpointInduction.MaskCoordinates
public import Theory.Representation.BinaryEndpointInduction.GeneratorClosure
public import Theory.Representation.BinaryFourExteriorCoordinates

/-!
# Exact models of the surviving endpoint quotients

Coordinate projection selects the four surviving coordinates in orientation
true and the six surviving coordinates in orientation false. Explicit
invertible matrices intertwine their two marked actors with, respectively,
the right contragredient four-space and the genuine compound-matrix exterior
square for the original shear and cycle.
-/
@[expose] public section
namespace BinaryEndpointInduction
open Matrix Thompson.BinaryMatrix
open scoped MatrixGroups

/-- Index of a surviving coordinate in the original forty-five-space. -/
def survivorIndex (dual : Bool) (j : Fin (if dual then 4 else 6)) : Fin 45 :=
  ⟨(if dual then 1 else 5)+j.val,by cases dual <;> simp_all <;> omega⟩

/-- Projection onto the literal surviving coordinate block. -/
def survivorProjection (dual : Bool) : (Fin 45 → ZMod 2) →ₗ[ZMod 2]
    (Fin (if dual then 4 else 6) → ZMod 2) where
  toFun x j := x (survivorIndex dual j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem survivorIndex_injective (dual : Bool) : Function.Injective (survivorIndex dual) := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val h
  simp only [survivorIndex] at hh
  omega

/-- Every vector in the surviving block is attained by the coordinate projection. -/
theorem survivorProjection_surjective (dual : Bool) : Function.Surjective (survivorProjection dual) := by
  classical
  intro x
  refine ⟨Function.extend (survivorIndex dual) x 0,?_⟩
  funext j
  exact (survivorIndex_injective dual).extend_apply x 0 j

private theorem survivor_coordinate_check : ∀ (dual : Bool) (j : Fin 45),
    (if dual then 29 else 27 : ℕ).testBit (coordinateBlock j).val=false ↔
      ∃ r : Fin (if dual then 4 else 6), survivorIndex dual r=j := by decide +kernel

/-- Its kernel is exactly the surviving mask from the exhaustive certificate. -/
theorem survivorProjection_ker (dual : Bool) :
    (survivorProjection dual).ker=maskSubspace ⟨if dual then 29 else 27,by cases dual <;> decide⟩ := by
  ext x
  rw [LinearMap.mem_ker,funext_iff]
  change (∀ r, x (survivorIndex dual r)=0) ↔ _
  constructor
  · intro hx j hj
    obtain ⟨r,rfl⟩ := (survivor_coordinate_check dual j).mp hj
    exact hx r
  · intro hx r
    exact hx _ ((survivor_coordinate_check dual _).mpr ⟨r,rfl⟩)

/-- The two actual adapted matrices restricted to the surviving quotient. -/
def survivorGenerator (dual : Bool) (k : Fin 2) :
    Matrix (Fin (if dual then 4 else 6)) (Fin (if dual then 4 else 6)) (ZMod 2) :=
  (adaptedGenerator dual k).submatrix (survivorIndex dual) (survivorIndex dual)

private theorem projection_generator_check : ∀ (dual : Bool) (k : Fin 2) (j : Fin 45),
    survivorProjection dual ((Pi.single j 1) ᵥ* adaptedGenerator dual k)=
      (survivorProjection dual (Pi.single j 1)) ᵥ* survivorGenerator dual k := by
  decide +kernel

/-- The coordinate projection intertwines the literal row actions. -/
theorem survivorProjection_intertwine (dual : Bool) (k : Fin 2) (x : Fin 45 → ZMod 2) :
    survivorProjection dual (x ᵥ* adaptedGenerator dual k)=
      (survivorProjection dual x) ᵥ* survivorGenerator dual k := by
  have h : (survivorProjection dual).comp (adaptedGenerator dual k).vecMulLinear=
      (survivorGenerator dual k).vecMulLinear.comp (survivorProjection dual) := by
    apply (Pi.basisFun (ZMod 2) (Fin 45)).ext
    intro j
    change survivorProjection dual ((Pi.basisFun (ZMod 2) (Fin 45) j) ᵥ* adaptedGenerator dual k)=_
    rw [Pi.basisFun_apply]
    exact projection_generator_check dual k j
  exact LinearMap.congr_fun h x

/-- The exact shear and cycle used in the coordinate tables. -/
def survivorActor : Fin 2 → SL(4,ZMod 2) := ![transvectionGenerator,cycleGenerator]

/-- Standard right-action model: inverse transpose in dimension four,
and genuine two-by-two minors in dimension six. -/
noncomputable def survivorModelMatrix (dual : Bool) (g : SL(4,ZMod 2)) :
    Matrix (Fin (if dual then 4 else 6)) (Fin (if dual then 4 else 6)) (ZMod 2) :=
  match dual with
  | true => (g⁻¹.val).transpose
  | false => Atlas.Order20160A8.Bivectors.compound g.val

/-- Explicit change from surviving spectral coordinates to the standard model. -/
def survivorChange : (dual : Bool) →
    Matrix (Fin (if dual then 4 else 6)) (Fin (if dual then 4 else 6)) (ZMod 2)
  | true => !![0,1,1,1; 1,1,1,1; 1,0,1,0; 0,0,0,1]
  | false => !![1,0,1,0,1,0; 0,0,0,0,1,1; 1,1,1,1,1,0;
      1,1,0,1,1,0; 1,1,1,1,1,1; 1,1,0,0,0,0]

/-- The displayed inverse change of coordinates. -/
def survivorChangeInverse : (dual : Bool) →
    Matrix (Fin (if dual then 4 else 6)) (Fin (if dual then 4 else 6)) (ZMod 2)
  | true => !![1,1,0,0; 0,1,1,1; 1,1,1,0; 0,0,0,1]
  | false => !![1,1,0,1,1,0; 1,1,0,1,1,1; 0,0,1,1,0,0;
      0,1,1,1,1,1; 0,1,1,0,1,0; 0,0,1,0,1,0]

/-- Kernel-checked two-sided inverses for both coordinate changes. -/
theorem survivorChange_inverse (dual : Bool) :
    survivorChange dual * survivorChangeInverse dual=1 ∧
      survivorChangeInverse dual * survivorChange dual=1 := by
  exact (by decide +kernel : ∀ d : Bool, survivorChange d * survivorChangeInverse d=1 ∧
    survivorChangeInverse d * survivorChange d=1) dual

/-- Both exact marked generators agree with the claimed standard models. -/
theorem survivorGenerator_intertwine (dual : Bool) (k : Fin 2) :
    survivorGenerator dual k * survivorChange dual=
      survivorChange dual * survivorModelMatrix dual (survivorActor k) := by
  exact (by decide +kernel : ∀ (d : Bool) (i : Fin 2),
    survivorGenerator d i * survivorChange d=
      survivorChange d * survivorModelMatrix d (survivorActor i)) dual k

private theorem compound_one : Atlas.Order20160A8.Bivectors.compound
    (1 : Matrix (Fin 4) (Fin 4) (ZMod 2))=1 := by
  apply Matrix.toLinAlgEquiv'.injective
  rw [map_one]
  exact Atlas.Order20160A8.Bivectors.exteriorMap_one (F := ZMod 2)

private theorem compound_mul (A B : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    Atlas.Order20160A8.Bivectors.compound (A*B)=
      Atlas.Order20160A8.Bivectors.compound A * Atlas.Order20160A8.Bivectors.compound B := by
  apply Matrix.toLinAlgEquiv'.injective
  rw [map_mul]
  exact Atlas.Order20160A8.Bivectors.exteriorMap_mul A B

/-- The standard survivor matrices form genuine marked group actions. -/
noncomputable def survivorModel (dual : Bool) : SL(4,ZMod 2) →*
    Matrix (Fin (if dual then 4 else 6)) (Fin (if dual then 4 else 6)) (ZMod 2) where
  toFun := survivorModelMatrix dual
  map_one' := by
    cases dual
    · exact compound_one
    · change ((1 : SL(4,ZMod 2))⁻¹.val).transpose=1
      simp
  map_mul' g h := by
    cases dual
    · exact compound_mul g.val h.val
    · change ((g*h)⁻¹.val).transpose=(g⁻¹.val).transpose*(h⁻¹.val).transpose
      rw [_root_.mul_inv_rev]
      change ((h⁻¹).val * (g⁻¹).val).transpose=(g⁻¹).val.transpose*(h⁻¹).val.transpose
      exact transpose_mul _ _

/-- The same coordinate change determines the action of every group element
from agreement on the exact original shear and cycle. -/
theorem survivorGenerator_intertwine_all (dual : Bool)
    (ρ : SL(4,ZMod 2) →* Matrix (Fin (if dual then 4 else 6)) (Fin (if dual then 4 else 6)) (ZMod 2))
    (hρ : ∀ k : Fin 2, ρ (survivorActor k)=survivorGenerator dual k)
    (g : SL(4,ZMod 2)) :
    ρ g * survivorChange dual=survivorChange dual * survivorModelMatrix dual g := by
  let σ : SL(4,ZMod 2) →* Matrix (Fin (if dual then 4 else 6))
      (Fin (if dual then 4 else 6)) (ZMod 2) := {
    toFun g := survivorChangeInverse dual * ρ g * survivorChange dual
    map_one' := by simp only [map_one,mul_one,(survivorChange_inverse dual).2]
    map_mul' g h := by
      rw [map_mul]
      simp only [mul_assoc,←mul_assoc (survivorChange dual) (survivorChangeInverse dual),
        (survivorChange_inverse dual).1,one_mul] }
  have he (k : Fin 2) : σ (survivorActor k)=survivorModel dual (survivorActor k) := by
    change survivorChangeInverse dual * ρ (survivorActor k) * survivorChange dual=_
    rw [hρ,mul_assoc,survivorGenerator_intertwine,←mul_assoc,
      (survivorChange_inverse dual).2,one_mul]
    rfl
  have hall : σ=survivorModel dual := MonoidHom.eq_of_eqOn_dense generator_closure (by
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact he 0
    · have h : a=cycleGenerator := Set.mem_singleton_iff.mp ha
      subst a
      exact he 1)
  have hh := congrArg (fun A => survivorChange dual*A) (DFunLike.congr_fun hall g)
  change survivorChange dual * (survivorChangeInverse dual * ρ g * survivorChange dual)=
    survivorChange dual * survivorModelMatrix dual g at hh
  simpa only [←mul_assoc,(survivorChange_inverse dual).1,one_mul] using hh

end BinaryEndpointInduction
