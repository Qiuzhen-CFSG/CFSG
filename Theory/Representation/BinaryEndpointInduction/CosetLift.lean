module
public import Theory.Representation.BinaryEndpointInduction.CosetTransitions
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RepresentationTheory.Basic

/-!
# Lifting the literal endpoint coordinates to the original module

A locally equivariant map from the marked three-space extends to the
forty-five coordinates by summing its translates along the original coset
representatives. The checked coset transitions prove equivariance for all
six actual actors. If the original module is spanned by the translates of
the seed, the generating pair makes this exact linear map surjective.
Neither irreducibility of the target nor surjectivity of the seed is needed.

Source context: Aschbacher--Smith 15.3.23, binary-four carrier.
-/
public noncomputable section
open Matrix Representation
open scoped MatrixGroups
namespace BinaryEndpointInduction

/-- The original block index: (i,u) has coordinate u+3*i. -/
@[expose] def cosetCoordinateEquiv : Fin 15 × Fin 3 ≃ Fin 45 :=
  finProdFinEquiv

/-- Embed a three-vector into its original block among the forty-five coordinates. -/
@[expose] def cosetBlockInclusion (i : Fin 15) :
    (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 45 → ZMod 2) where
  toFun v n := if (cosetCoordinateEquiv.symm n).1 = i then v (cosetCoordinateEquiv.symm n).2 else 0
  map_add' v w := by
    funext n
    by_cases h : (cosetCoordinateEquiv.symm n).1 = i <;> simp [h]
  map_smul' c v := by
    funext n
    by_cases h : (cosetCoordinateEquiv.symm n).1 = i <;> simp [h]

private theorem block_apply (i j : Fin 15) (u : Fin 3) (v : Fin 3 → ZMod 2) :
    cosetBlockInclusion i v (cosetCoordinateEquiv (j,u)) = if j = i then v u else 0 := by
  change (if (cosetCoordinateEquiv.symm (cosetCoordinateEquiv (j,u))).1 = i then
    v (cosetCoordinateEquiv.symm (cosetCoordinateEquiv (j,u))).2 else 0) = _
  rw [Equiv.symm_apply_apply]

private theorem block_decomposition (x : Fin 45 → ZMod 2) :
    ∑ i : Fin 15, cosetBlockInclusion i (fun u => x (cosetCoordinateEquiv (i,u))) = x := by
  ext n
  obtain ⟨⟨i,u⟩,rfl⟩ := cosetCoordinateEquiv.surjective n
  simp only [Finset.sum_apply,block_apply]
  simp

private theorem sum_coordinates {A : Type*} [AddCommMonoid A] (f : Fin 45 → A) :
    ∑ n : Fin 45, f n = ∑ i : Fin 15, ∑ u : Fin 3, f (cosetCoordinateEquiv (i,u)) := by
  calc
    ∑ n : Fin 45, f n = ∑ p : Fin 15 × Fin 3, f (cosetCoordinateEquiv p) :=
      (Equiv.sum_comp cosetCoordinateEquiv f).symm
    _ = _ := Fintype.sum_prod_type _

private theorem matrix_entry (dual : Bool) (a : Fin 6) (i j : Fin 15) (u v : Fin 3) :
    inducedCosetMatrix dual a (cosetCoordinateEquiv (i,u)) (cosetCoordinateEquiv (j,v)) =
      if transitionIndex a i = j then transitionBlock dual a i u v else 0 := by
  change inducedCosetMatrix dual a ⟨u.val + 3 * i.val, _⟩ ⟨v.val + 3 * j.val, _⟩ = _
  simpa only [Nat.add_comm] using inducedCosetMatrix_entry dual a i j u v

private theorem block_vecMul (dual : Bool) (a : Fin 6) (i : Fin 15)
    (v : Fin 3 → ZMod 2) :
    (cosetBlockInclusion i v) ᵥ* inducedCosetMatrix dual a =
      cosetBlockInclusion (transitionIndex a i) (v ᵥ* transitionBlock dual a i) := by
  ext n
  obtain ⟨⟨j,u⟩,rfl⟩ := cosetCoordinateEquiv.surjective n
  change (∑ k : Fin 45, cosetBlockInclusion i v k *
    inducedCosetMatrix dual a k (cosetCoordinateEquiv (j,u))) = _
  rw [sum_coordinates]
  simp_rw [block_apply,ite_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ,ite_true,matrix_entry]
  by_cases h : transitionIndex a i = j
  · simp [h,Matrix.vecMul,dotProduct]
  · simp [h,Ne.symm h]

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- Sum the original seed map over its fifteen literal coset translates. -/
@[expose] def cosetLift (τ : Representation (ZMod 2) SL(4,ZMod 2) W)
    (j : (Fin 3 → ZMod 2) →ₗ[ZMod 2] W) : (Fin 45 → ZMod 2) →ₗ[ZMod 2] W where
  toFun x := ∑ i : Fin 15, τ (cosetRepresentative i)⁻¹
    (j (fun u => x (cosetCoordinateEquiv (i,u))))
  map_add' x y := by
    change (∑ i : Fin 15, τ (cosetRepresentative i)⁻¹
      (j ((fun u => x (cosetCoordinateEquiv (i,u))) +
        (fun u => y (cosetCoordinateEquiv (i,u)))))) = _
    simp only [map_add, Finset.sum_add_distrib]
  map_smul' c x := by
    change (∑ i : Fin 15, τ (cosetRepresentative i)⁻¹
      (j (c • (fun u => x (cosetCoordinateEquiv (i,u)))))) = _
    simp only [map_smul, Finset.smul_sum, RingHom.id_apply]

/-- The lift retains each seed block and its exact representative. -/
theorem cosetLift_block (τ : Representation (ZMod 2) SL(4,ZMod 2) W)
    (j : (Fin 3 → ZMod 2) →ₗ[ZMod 2] W) (i : Fin 15) (v : Fin 3 → ZMod 2) :
    cosetLift τ j (cosetBlockInclusion i v) = τ (cosetRepresentative i)⁻¹ (j v) := by
  change (∑ k : Fin 15, τ (cosetRepresentative k)⁻¹
    (j (fun u => cosetBlockInclusion i v (cosetCoordinateEquiv (k,u))))) = _
  simp_rw [block_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    simp only [hki,ite_false]
    change τ (cosetRepresentative k)⁻¹ (j 0) = 0
    simp
  · simp

/-- The identity-coset block recovers the original map j exactly. -/
theorem cosetLift_seed (τ : Representation (ZMod 2) SL(4,ZMod 2) W)
    (j : (Fin 3 → ZMod 2) →ₗ[ZMod 2] W) (v : Fin 3 → ZMod 2) :
    cosetLift τ j (cosetBlockInclusion 0 v) = j v := by
  rw [cosetLift_block,cosetRepresentative_zero,inv_one,map_one]
  rfl

variable (dual : Bool) (τ : Representation (ZMod 2) SL(4,ZMod 2) W)
  (j : (Fin 3 → ZMod 2) →ₗ[ZMod 2] W)
  (hlocal : ∀ (a : Fin 6) (i : Fin 15) (v : Fin 3 → ZMod 2),
    j (v ᵥ* transitionBlock dual a i) = τ (transitionCorrection a i)⁻¹ (j v))

include hlocal

private theorem lift_block_intertwine (a : Fin 6) (i : Fin 15) (v : Fin 3 → ZMod 2) :
    cosetLift τ j ((cosetBlockInclusion i v) ᵥ* inducedCosetMatrix dual a) =
      τ (cosetActor a)⁻¹ (cosetLift τ j (cosetBlockInclusion i v)) := by
  rw [block_vecMul,cosetLift_block,hlocal,cosetLift_block]
  rw [← Module.End.mul_apply,← τ.map_mul,← Module.End.mul_apply,← τ.map_mul]
  have he := congrArg (fun g : SL(4,ZMod 2) => g⁻¹) (coset_transition a i)
  simp only [_root_.mul_inv_rev] at he
  exact congrArg (fun g => τ g (j v)) he.symm

/-- All six original right-row actors intertwine with their inverse left
actors on the same target W. The map and its kernel are unchanged. -/
theorem cosetLift_intertwine (a : Fin 6) (x : Fin 45 → ZMod 2) :
    cosetLift τ j (x ᵥ* inducedCosetMatrix dual a) =
      τ (cosetActor a)⁻¹ (cosetLift τ j x) := by
  have hx := block_decomposition x
  conv_lhs => rw [← hx]
  change cosetLift τ j ((inducedCosetMatrix dual a).vecMulLinear
    (∑ i : Fin 15, cosetBlockInclusion i (fun u => x (cosetCoordinateEquiv (i,u))))) = _
  rw [map_sum,map_sum]
  simp_rw [Matrix.vecMulLinear_apply,lift_block_intertwine dual τ j hlocal]
  rw [← map_sum,← map_sum,hx]

/-- The original orbit-span hypothesis makes the literal lift onto. Neither
the seed map nor the target representation is assumed to be simple. -/
theorem cosetLift_surjective
    (hspan : Submodule.span (ZMod 2)
      (Set.range (fun gv : SL(4,ZMod 2) × (Fin 3 → ZMod 2) => τ gv.1 (j gv.2))) = ⊤) :
    Function.Surjective (cosetLift τ j) := by
  let F := cosetLift τ j
  let R := F.range
  let : Finite R := Finite.of_surjective F.rangeRestrict F.surjective_rangeRestrict
  have hstable (a : Fin 6) (w : W) (hw : w ∈ R) : τ (cosetActor a)⁻¹ w ∈ R := by
    obtain ⟨x,rfl⟩ := hw
    exact ⟨x ᵥ* inducedCosetMatrix dual a,cosetLift_intertwine dual τ j hlocal a x⟩
  have hiff (a : Fin 6) (w : W) : w ∈ R ↔ τ (cosetActor a)⁻¹ w ∈ R := by
    refine ⟨hstable a w,?_⟩
    let f : R → R := fun x => ⟨τ (cosetActor a)⁻¹ x,hstable a x x.property⟩
    have hfi : Function.Injective f := by
      intro x y he
      exact Subtype.ext ((τ.apply_bijective _).injective (congrArg Subtype.val he))
    intro hw
    obtain ⟨x,hx⟩ := Finite.surjective_of_injective hfi ⟨τ (cosetActor a)⁻¹ w,hw⟩
    have he : (x : W) = w := (τ.apply_bijective _).injective (congrArg Subtype.val hx)
    exact he ▸ x.property
  let H : Subgroup SL(4,ZMod 2) := {
    carrier := {g | ∀ w : W, w ∈ R ↔ τ g w ∈ R}
    one_mem' := by intro w; simp
    mul_mem' := by
      intro g h hg hh w
      simpa only [τ.map_mul,Module.End.mul_apply] using (hh w).trans (hg (τ h w))
    inv_mem' := by
      intro g hg w
      simpa only [τ.self_inv_apply] using (hg (τ g⁻¹ w)).symm }
  have hactors (a : Fin 6) : cosetActor a ∈ H := by
    have hi : (cosetActor a)⁻¹ ∈ H := hiff a
    simpa only [inv_inv] using H.inv_mem hi
  have htop : H = ⊤ := by
    apply top_unique
    rw [← generator_closure]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact cosetActor_generators.1 ▸ hactors 0
    · have he : g = cycleGenerator := Set.mem_singleton_iff.mp hg
      subst g
      exact cosetActor_generators.2 ▸ hactors 1
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g,v⟩,rfl⟩
  have hg : g ∈ H := htop ▸ Subgroup.mem_top g
  apply (hg (j v)).mp
  exact ⟨cosetBlockInclusion 0 v,cosetLift_seed τ j v⟩

end BinaryEndpointInduction
