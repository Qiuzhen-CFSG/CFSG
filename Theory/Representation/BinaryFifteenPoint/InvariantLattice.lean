module
public import Theory.Representation.BinaryFifteenPoint.BlockLattice
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# All invariant subspaces of the literal fifteen-point permutation module

The actual shear and cycle reduce the 32 primary-block masks to exactly
eight. This is a complete lattice certificate for arbitrary invariant
subspaces, including reducible kernels and extensions. Every row is retained.
-/
@[expose] public noncomputable section
namespace BinaryFifteenPoint
open Matrix

/-- The eight and only eight invariant masks, in increasing dimension. -/
def invariantMask : Fin 8 → Fin 32 := ![0,1,4,5,22,23,30,31]

/-- The dimension of each invariant row. -/
def rowDimension : Fin 8 → ℕ := ![0,1,4,5,10,11,14,15]

/-- The actual invariant row in the original fifteen coset coordinates. -/
def invariantSubspace (r : Fin 8) : Submodule (ZMod 2) (Fin 15 → ZMod 2) :=
  (maskSubspace (invariantMask r)).map changeMatrix.vecMulLinear

private theorem generator_mask_bits : ∀ m : Fin 32,
    (∀ (k : Fin 2) (i j : Fin 15),
      m.val.testBit (coordinateBlock i).val=true →
      m.val.testBit (coordinateBlock j).val=false →
      (adaptedRows[k.val]!)[i.val]!.testBit j.val=false) ↔
        ∃ r : Fin 8, invariantMask r=m := by decide +kernel

private theorem all_actor_mask_bits : ∀ (r : Fin 8) (a : Fin 6) (i j : Fin 15),
    (invariantMask r).val.testBit (coordinateBlock i).val=true →
    (invariantMask r).val.testBit (coordinateBlock j).val=false →
    (adaptedRows[a.val]!)[i.val]!.testBit j.val=false := by decide +kernel

private theorem all_actor_mask_check (r : Fin 8) (a : Fin 6) (i j : Fin 15)
    (hi : (invariantMask r).val.testBit (coordinateBlock i).val=true)
    (hj : (invariantMask r).val.testBit (coordinateBlock j).val=false) :
    adaptedActor a i j=0 := by
  change (if (adaptedRows[a.val]!)[i.val]!.testBit j.val then (1 : ZMod 2) else 0)=0
  rw [all_actor_mask_bits r a i j hi hj]
  rfl

private theorem row_stable_of_entries (m : Fin 32)
    (M : Matrix (Fin 15) (Fin 15) (ZMod 2))
    (hM : ∀ i j, m.val.testBit (coordinateBlock i).val=true →
      m.val.testBit (coordinateBlock j).val=false → M i j=0)
    (x : Fin 15 → ZMod 2) (hx : x ∈ maskSubspace m) : x ᵥ* M ∈ maskSubspace m := by
  intro j hj
  change (∑ i : Fin 15, x i*M i j)=0
  apply Finset.sum_eq_zero
  intro i _
  cases he : m.val.testBit (coordinateBlock i).val with
  | false => rw [hx i he,zero_mul]
  | true => rw [hM i j he hj,mul_zero]

private theorem mask_of_stable (m : Fin 32)
    (h : ∀ (k : Fin 2) x, x ∈ maskSubspace m →
      x ᵥ* adaptedActor ⟨k.val,by omega⟩ ∈ maskSubspace m) :
    ∃ r : Fin 8, invariantMask r=m := by
  apply (generator_mask_bits m).mp
  intro k i j hi hj
  have hx : Pi.single i (1 : ZMod 2) ∈ maskSubspace m := by
    intro a ha
    by_cases hai : a=i
    · subst a
      rw [hi] at ha
      contradiction
    · simp [hai]
  have hh := h k _ hx
  have hz := hh j hj
  rw [Matrix.single_one_vecMul] at hz
  change (if (adaptedRows[k.val]!)[i.val]!.testBit j.val then (1 : ZMod 2) else 0)=0 at hz
  cases hb : (adaptedRows[k.val]!)[i.val]!.testBit j.val
  · rfl
  · simp [hb] at hz

private theorem changed_stable
    (U : Submodule (ZMod 2) (Fin 15 → ZMod 2))
    (a : Fin 6) (h : ∀ x, x ∈ U → x ᵥ* permutationActor a ∈ U) :
    ∀ x, x ∈ U.comap changeMatrix.vecMulLinear →
      x ᵥ* adaptedActor a ∈ U.comap changeMatrix.vecMulLinear := by
  intro x hx
  change (x ᵥ* adaptedActor a) ᵥ* changeMatrix ∈ U
  rw [vecMul_vecMul,←actor_intertwine,←vecMul_vecMul]
  exact h _ hx

private theorem change_injective : Function.Injective changeMatrix.vecMulLinear := by
  intro x y h
  have hh := congrArg (fun v => v ᵥ* inverseChangeMatrix) h
  change (x ᵥ* changeMatrix) ᵥ* inverseChangeMatrix=
    (y ᵥ* changeMatrix) ᵥ* inverseChangeMatrix at hh
  simpa only [vecMul_vecMul,change_inverse.1,vecMul_one] using hh

private theorem change_surjective : Function.Surjective changeMatrix.vecMulLinear := by
  intro x
  refine ⟨x ᵥ* inverseChangeMatrix,?_⟩
  change (x ᵥ* inverseChangeMatrix) ᵥ* changeMatrix=x
  rw [vecMul_vecMul,change_inverse.2,vecMul_one]

/-- Each of the eight displayed rows is invariant under all six literal actors. -/
theorem invariantSubspace_stable (r : Fin 8) (a : Fin 6)
    (x : Fin 15 → ZMod 2) (hx : x ∈ invariantSubspace r) :
    x ᵥ* permutationActor a ∈ invariantSubspace r := by
  obtain ⟨y,hy,rfl⟩ := hx
  refine ⟨y ᵥ* adaptedActor a,
    row_stable_of_entries _ _ (all_actor_mask_check r a) y hy,?_⟩
  change (y ᵥ* adaptedActor a) ᵥ* changeMatrix=
    (y ᵥ* changeMatrix) ᵥ* permutationActor a
  rw [vecMul_vecMul,vecMul_vecMul,actor_intertwine]

/-- Every invariant subspace is one of the eight exact rows, with no
simplicity or semisimplicity hypothesis. The converse retains all rows. -/
theorem invariant_iff (U : Submodule (ZMod 2) (Fin 15 → ZMod 2)) :
    (∀ (k : Fin 2) x, x ∈ U → x ᵥ* permutationActor ⟨k.val,by omega⟩ ∈ U) ↔
      ∃ r : Fin 8, U=invariantSubspace r := by
  constructor
  · intro hU
    let T := U.comap changeMatrix.vecMulLinear
    have hT : ∀ x, x ∈ T → x ᵥ* companion ∈ T := by
      intro x hx
      change (x ᵥ* companion) ᵥ* changeMatrix ∈ U
      rw [vecMul_vecMul,←spectral_intertwine,←vecMul_vecMul,←vecMul_vecMul]
      exact hU 1 _ (hU 0 _ hx)
    obtain ⟨m,hm⟩ := invariant_subspace_eq_maskSubspace T hT
    obtain ⟨r,hr⟩ := mask_of_stable m (by
      intro k x hx
      rw [←hm] at hx ⊢
      exact changed_stable U ⟨k.val,by omega⟩ (hU k) x hx)
    refine ⟨r,?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨y,rfl⟩ := change_surjective x
      refine ⟨y,?_,rfl⟩
      rw [hr,←hm]
      exact hx
    · rintro ⟨y,hy,rfl⟩
      rw [hr,←hm] at hy
      exact hy
  · rintro ⟨r,rfl⟩ k x hx
    exact invariantSubspace_stable r ⟨k.val,by omega⟩ x hx

private def maskInsert (m : Fin 32) :
    ({j : Fin 15 // m.val.testBit (coordinateBlock j).val=true} → ZMod 2) →ₗ[ZMod 2]
      (Fin 15 → ZMod 2) where
  toFun x j := if hj : m.val.testBit (coordinateBlock j).val=true then x ⟨j,hj⟩ else 0
  map_add' := by intro x y; ext j; by_cases h : m.val.testBit (coordinateBlock j).val=true <;> simp [h]
  map_smul' := by intro c x; ext j; by_cases h : m.val.testBit (coordinateBlock j).val=true <;> simp [h]

private theorem maskInsert_injective (m : Fin 32) : Function.Injective (maskInsert m) := by
  intro x y h
  funext j
  have hh := congrFun h j.val
  simpa only [maskInsert,LinearMap.coe_mk,AddHom.coe_mk,dif_pos j.property] using hh

private theorem maskInsert_range (m : Fin 32) : (maskInsert m).range=maskSubspace m := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩ j hj
    simp [maskInsert,hj]
  · intro hx
    refine ⟨fun j => x j.val,?_⟩
    funext j
    by_cases hj : m.val.testBit (coordinateBlock j).val=true
    · simp [maskInsert,hj]
    · have hh : m.val.testBit (coordinateBlock j).val=false := by simpa using hj
      simpa [maskInsert,hj] using (hx j hh).symm

private theorem mask_finrank (m : Fin 32) : Module.finrank (ZMod 2) (maskSubspace m)=
    Fintype.card {j : Fin 15 // m.val.testBit (coordinateBlock j).val=true} := by
  rw [←maskInsert_range,LinearMap.finrank_range_of_inj (maskInsert_injective m)]
  exact Module.finrank_fintype_fun_eq_card (ZMod 2)

private theorem row_dimension_check : ∀ r : Fin 8,
    Fintype.card {j : Fin 15 // (invariantMask r).val.testBit (coordinateBlock j).val=true}=
      rowDimension r := by decide +kernel

/-- The eight rows have dimensions 0,1,4,5,10,11,14,15 in the stated order. -/
theorem invariantSubspace_finrank (r : Fin 8) :
    Module.finrank (ZMod 2) (invariantSubspace r)=rowDimension r := by
  let e := LinearEquiv.ofBijective changeMatrix.vecMulLinear ⟨change_injective,change_surjective⟩
  change Module.finrank (ZMod 2) ((maskSubspace (invariantMask r)).map e.toLinearMap)=_
  rw [e.finrank_map_eq,mask_finrank,row_dimension_check]

/-- Distinct rows are distinct actual invariant subspaces. -/
theorem invariantSubspace_injective : Function.Injective invariantSubspace := by
  intro r s h
  have hd := congrArg (fun (U : Submodule (ZMod 2) (Fin 15 → ZMod 2)) => Module.finrank (ZMod 2) U) h
  rw [invariantSubspace_finrank,invariantSubspace_finrank] at hd
  exact (by decide +kernel : Function.Injective rowDimension) hd

/-- Every invariant kernel of a literal fifteen-point quotient is one of
the eight original rows, retaining the given quotient map. -/
theorem quotient_kernel {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (f : (Fin 15 → ZMod 2) →ₗ[ZMod 2] W)
    (h : ∀ (k : Fin 2) x, x ∈ f.ker →
      x ᵥ* permutationActor ⟨k.val,by omega⟩ ∈ f.ker) :
    ∃ r : Fin 8, f.ker=invariantSubspace r := (invariant_iff f.ker).mp h

end BinaryFifteenPoint
