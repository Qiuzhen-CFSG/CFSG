module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.Coordinates
public import Theory.Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.CycleSimplicity.Data
public import Theory.Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.CycleSimplicity.Arithmetic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Realizing the checked cycle matrices on the literal flag quotient

An explicit 52-by-27 matrix lies in the incidence kernel and has a checked
left inverse. Its first column is the constant cycle. The remaining columns
map injectively into the quotient, hence bijectively by its known dimension.
The native flag permutations intertwine this map with the two checked
26-dimensional matrices. All identities survive coefficient casting.

This identifies the geometric witness used for the PSL₃(3) principal degrees
in Guralnick--Malle, Classification of 2F-modules I, Proposition 4.2.
-/

@[expose] public section

open scoped BigOperators Matrix
open Thompson.BinaryMatrix CycleCertificate
namespace Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.CycleSimplicity
open Coordinates

abbrev B := rectangular 52 27 Data.cycleRows
abbrev E := rectangular 27 52 Data.cycleLeftRows
abbrev D := rectangular 26 52 Data.boundaryRows
abbrev C (a : Fin 2) := decode 27 (Data.cycleActionRows a)
abbrev PB (a : Fin 2) := rectangular 52 27 (Data.cycleImageRows a)

private theorem left_inverse_binary : E * B = 1 := by
  ext i j
  change (∑ t : Fin 52, bit Data.cycleLeftRows[i.val]! t.val *
    bit Data.cycleRows[t.val]! j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun t => bit Data.cycleLeftRows[i.val]! t *
    bit Data.cycleRows[t]! j.val), ← bit_rowProduct]
  have h : ∀ i : Fin 27, rowProduct Data.cycleLeftRows[i.val]! Data.cycleRows 52 =
      2 ^ i.val := by decide +kernel
  rw [h i]
  simp [bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

private theorem boundary_binary : D * B = 0 := by
  ext i j
  change (∑ t : Fin 52, bit Data.boundaryRows[i.val]! t.val *
    bit Data.cycleRows[t.val]! j.val) = 0
  rw [Fin.sum_univ_eq_sum_range (fun t => bit Data.boundaryRows[i.val]! t *
    bit Data.cycleRows[t]! j.val), ← bit_rowProduct]
  have h : ∀ i : Fin 26, rowProduct Data.boundaryRows[i.val]! Data.cycleRows 52 = 0 :=
    by decide +kernel
  rw [h i]
  simp [bit]

private theorem action_binary (a : Fin 2) : B * C a = PB a :=
  rectangular_mul 52 27 27 Data.cycleRows (Data.cycleActionRows a) (Data.cycleImageRows a)
    (by revert a; decide +kernel)

private theorem constant_binary : ∀ i : Fin 52, B i 0 = 1 := by decide +kernel
private theorem permuted_binary : ∀ (a : Fin 2) (i : Fin 52) (j : Fin 27),
    PB a (flagImage a i) j = B i j := by
  unfold PB B rectangular
  decide +kernel
private theorem tail_binary : ∀ (a : Fin 2) (i j : Fin 26),
    C a i.succ j.succ = Data.actorMatrix a i j := by
  unfold C Data.actorMatrix decode
  decide +kernel
private theorem boundary_point_binary : ∀ (i : Fin 13) (k : Fin 52),
    D (Fin.castAdd 13 i) k = if (flagPair k).1 = i then 1 else 0 := by decide +kernel
private theorem boundary_line_binary : ∀ (i : Fin 13) (k : Fin 52),
    D (Fin.natAdd 13 i) k = if (flagPair k).2 = i then 1 else 0 := by decide +kernel

variable (F : Type*) [Field F] [CharP F 2]

abbrev scalar := ZMod.castHom (dvd_refl 2) F
abbrev basisMatrix : Matrix (Fin 52) (Fin 27) F := B.map (scalar F)
abbrev leftMatrix : Matrix (Fin 27) (Fin 52) F := E.map (scalar F)
abbrev boundaryMatrix : Matrix (Fin 26) (Fin 52) F := D.map (scalar F)
abbrev cycleMatrix (a : Fin 2) : Matrix (Fin 27) (Fin 27) F := (C a).map (scalar F)
abbrev quotientMatrix (a : Fin 2) : Matrix (Fin 26) (Fin 26) F :=
  castMatrix F (Data.actorMatrix a)

private theorem left_inverse : leftMatrix F * basisMatrix F = 1 := by
  rw [leftMatrix, basisMatrix, ← Matrix.map_mul, left_inverse_binary]
  exact map_one ((scalar F).mapMatrix)

private theorem boundary_zero : boundaryMatrix F * basisMatrix F = 0 := by
  rw [boundaryMatrix, basisMatrix, ← Matrix.map_mul, boundary_binary]
  ext i j
  exact map_zero (scalar F)

noncomputable def flagCoordinates : (Fin 52 → F) ≃ₗ[F] (PrincipalModels.Flag → F) :=
  LinearEquiv.funCongrLeft F F flagEquiv.symm

omit [CharP F 2] in
@[simp] theorem flagCoordinates_at (v : Fin 52 → F) (i : Fin 52) :
    flagCoordinates F v (flagAt i) = v i := by
  change v (flagEquiv.symm (flagEquiv i)) = _
  rw [_root_.Equiv.symm_apply_apply]

noncomputable def flagLift : (Fin 27 → F) →ₗ[F] (PrincipalModels.Flag → F) :=
  (flagCoordinates F).toLinearMap.comp (basisMatrix F).mulVecLin

@[simp] theorem flagLift_at (v : Fin 27 → F) (i : Fin 52) :
    flagLift F v (flagAt i) = (basisMatrix F *ᵥ v) i :=
  by
    change flagCoordinates F (basisMatrix F *ᵥ v) (flagAt i) = _
    exact flagCoordinates_at F _ i

private theorem boundary_point (v : PrincipalModels.Flag → F) (i : Fin 13) :
    (boundary F v).1 (pointAt i) =
      (boundaryMatrix F *ᵥ (fun k => v (flagAt k))) (Fin.castAdd 13 i) := by
  classical
  change (∑ f : PrincipalModels.Flag, v f • endpoint F f.val.1 f.val.2).1 (pointAt i) = _
  rw [← _root_.Equiv.sum_comp flagEquiv]
  simp only [Prod.fst_sum, Prod.smul_fst, endpoint, flagEquiv_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ k : Fin 52, v (flagAt k) * (Pi.single (pointAt (flagPair k).1) (1 : F) : PrincipalModels.PG → F)
    (pointAt i)) = _
  simp only [Matrix.mulVec, dotProduct, boundaryMatrix, Matrix.map_apply, boundary_point_binary]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : (flagPair k).1 = i
  · simp [h]
  · simp [pointAt_injective.eq_iff, h, Ne.symm h]

private theorem boundary_line (v : PrincipalModels.Flag → F) (i : Fin 13) :
    (boundary F v).2 (pointAt i) =
      (boundaryMatrix F *ᵥ (fun k => v (flagAt k))) (Fin.natAdd 13 i) := by
  classical
  change (∑ f : PrincipalModels.Flag, v f • endpoint F f.val.1 f.val.2).2 (pointAt i) = _
  rw [← _root_.Equiv.sum_comp flagEquiv]
  simp only [Prod.snd_sum, Prod.smul_snd, endpoint, flagEquiv_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ k : Fin 52, v (flagAt k) * (Pi.single (pointAt (flagPair k).2) (1 : F) : PrincipalModels.PG → F)
    (pointAt i)) = _
  simp only [Matrix.mulVec, dotProduct, boundaryMatrix, Matrix.map_apply, boundary_line_binary]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : (flagPair k).2 = i
  · simp [h]
  · simp [pointAt_injective.eq_iff, h, Ne.symm h]

private theorem flagLift_mem (v : Fin 27 → F) : flagLift F v ∈ (cycleSpace F).toSubmodule := by
  have h : boundaryMatrix F *ᵥ (basisMatrix F *ᵥ v) = 0 := by
    rw [Matrix.mulVec_mulVec, boundary_zero, Matrix.zero_mulVec]
  change boundary F (flagLift F v) = 0
  apply Prod.ext
  · funext p
    obtain ⟨i, rfl⟩ := pointEquiv.surjective p
    rw [pointEquiv_apply, boundary_point]
    simpa only [flagLift_at, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply] using congrFun h (Fin.castAdd 13 i)
  · funext p
    obtain ⟨i, rfl⟩ := pointEquiv.surjective p
    rw [pointEquiv_apply, boundary_line]
    simpa only [flagLift_at, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply] using congrFun h (Fin.natAdd 13 i)

/-- The checked 27-cycle inclusion, with the constant cycle in its first column. -/
noncomputable def cycleLift : (Fin 27 → F) →ₗ[F] (cycleSpace F).toSubmodule :=
  (flagLift F).codRestrict (cycleSpace F).toSubmodule (by exact flagLift_mem F)

private theorem cycleLift_injective : Function.Injective (cycleLift F) := by
  intro x y h
  have hv : basisMatrix F *ᵥ x = basisMatrix F *ᵥ y := by
    funext i
    have hh := congrArg (fun z : (cycleSpace F).toSubmodule => z.val (flagAt i)) h
    change flagLift F x (flagAt i) = flagLift F y (flagAt i) at hh
    simpa only [flagLift_at] using hh
  have he := congrArg (fun z => leftMatrix F *ᵥ z) hv
  simpa only [Matrix.mulVec_mulVec, left_inverse, Matrix.one_mulVec] using he

private theorem cycleLift_constant : cycleLift F (Pi.single 0 1) = constantCycle F := by
  apply Subtype.ext
  funext f
  obtain ⟨i, rfl⟩ := flagEquiv.surjective f
  change flagLift F (Pi.single 0 1) (flagAt i) = 1
  rw [flagLift_at]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, basisMatrix, constant_binary]

/-- Insert a zero constant coordinate. -/
def tailInclusion : (Fin 26 → F) →ₗ[F] (Fin 27 → F) where
  toFun x := Fin.cons (α := fun _ : Fin 27 => F) 0 x
  map_add' x y := by ext i; cases i using Fin.cases <;> simp
  map_smul' a x := by ext i; cases i using Fin.cases <;> simp

/-- The literal quotient map applied to the last 26 checked cycles. -/
noncomputable def quotientLift : (Fin 26 → F) →ₗ[F] CycleQuotient F :=
  (constantLine F).toSubmodule.mkQ.comp ((cycleLift F).comp (tailInclusion F))

private theorem quotientLift_injective : Function.Injective (quotientLift F) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hz : (constantLine F).toSubmodule.mkQ
      (cycleLift F (tailInclusion F x)) = 0 := hx
  have hm := (Submodule.Quotient.mk_eq_zero (constantLine F).toSubmodule).mp hz
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
  have he : cycleLift F (a • Pi.single 0 1) = cycleLift F (tailInclusion F x) := by
    rw [map_smul, cycleLift_constant]
    exact ha
  have hi := cycleLift_injective F he
  change x = 0
  funext i
  have h := congrFun hi i.succ
  simpa [tailInclusion, Pi.single_apply] using h.symm

/-- Coordinates identify the concrete 26-dimensional model with the actual cycle quotient. -/
noncomputable def quotientEquiv : (Fin 26 → F) ≃ₗ[F] CycleQuotient F :=
  (quotientLift F).linearEquivOfInjective (by exact quotientLift_injective F)
    (by rw [Module.finrank_fintype_fun_eq_card, finrank_cycleQuotient]; rfl)

private theorem constant_quotient_zero :
    (constantLine F).toSubmodule.mkQ (constantCycle F) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span (Set.mem_singleton _))

private theorem mkQ_cycleLift (z : Fin 27 → F) :
    (constantLine F).toSubmodule.mkQ (cycleLift F z) = quotientLift F (Fin.tail z) := by
  have hz : z = z 0 • Pi.single 0 1 + tailInclusion F (Fin.tail z) := by
    funext i
    cases i using Fin.cases <;> simp [tailInclusion, Fin.tail]
  conv_lhs => rw [hz]
  rw [map_add, map_smul, cycleLift_constant, map_add, map_smul,
    constant_quotient_zero, smul_zero, zero_add]
  rfl

private theorem cycleLift_actor (a : Fin 2) (z : Fin 27 → F) :
    (cycleSpace F).toRepresentation (actor a) (cycleLift F z) =
      cycleLift F (cycleMatrix F a *ᵥ z) := by
  apply Subtype.ext
  change permutation F flagPerm (actor a) (flagLift F z) =
    flagLift F (cycleMatrix F a *ᵥ z)
  funext f
  obtain ⟨f, rfl⟩ := (flagPerm (actor a)).surjective f
  obtain ⟨i, rfl⟩ := flagEquiv.surjective f
  change permutation F flagPerm (actor a) (flagLift F z)
    (flagPerm (actor a) (flagAt i)) = _
  rw [permutation_apply, _root_.Equiv.symm_apply_apply, flagLift_at, flagEquiv_apply, flagPerm_actor, flagLift_at]
  have hact : basisMatrix F * cycleMatrix F a = (PB a).map (scalar F) := by
    rw [basisMatrix, cycleMatrix, ← Matrix.map_mul, action_binary]
  rw [Matrix.mulVec_mulVec, hact]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, permuted_binary]

private theorem tail_actor (a : Fin 2) (x : Fin 26 → F) :
    Fin.tail (cycleMatrix F a *ᵥ tailInclusion F x) = quotientMatrix F a *ᵥ x := by
  funext i
  change (∑ j : Fin 27, scalar F (C a i.succ j) * (Fin.cons (α := fun _ : Fin 27 => F) 0 x) j) = _
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, mul_zero, Fin.cons_succ, zero_add, tail_binary]
  rfl

/-- The two literal projected SL₃(3) actors have the checked quotient matrices. -/
theorem actor_quotientLift (a : Fin 2) (x : Fin 26 → F) :
    (constantLine F).quotientRepresentation (actor a) (quotientLift F x) =
      quotientLift F (quotientMatrix F a *ᵥ x) := by
  change (constantLine F).quotientRepresentation (actor a)
    ((constantLine F).toSubmodule.mkQ (cycleLift F (tailInclusion F x))) = _
  rw [Subrepresentation.quotientRepresentation_mk, cycleLift_actor, mkQ_cycleLift, tail_actor]

end Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.CycleSimplicity
