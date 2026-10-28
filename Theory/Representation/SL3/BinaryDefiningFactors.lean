module

public import Theory.Representation.SpecialLinearNatural
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Data.List.Rotate
import Mathlib.Tactic.DeriveFintype

/-!
# Concrete binary defining factors and tensor words for SL₃

The four labels retain the distinction between the natural representation and
its dual. Their carriers have dimensions 1, 3, 3 and 8; the last is the kernel
of the trace on endomorphisms of the natural space, acted on by conjugation.
A word denotes an actual tensor representation, with successive factors using
successive squares of the coefficient embedding. Its dimension is the product
of the factor dimensions. Repeating a block gives the corresponding power.

These constructions and dimension calculations do not assert irreducibility,
exhaustiveness, or uniqueness of tensor words. Those are separate representation
theorems. In particular equal dimensions do not identify the natural and dual
labels or their representations.

Source: GLS III, 2.8.6(a) and 2.8.10(c). The trace-kernel calculation generalizes
Theory.Representation.PSL3Two.SmallModules and SmallModuleProperties.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section

open scoped MatrixGroups TensorProduct
namespace Representation.SL3.BinaryDefiningFactors

/-- The four distinct binary restricted-weight labels. -/
inductive Factor
  | trivial | natural | dual | adjoint
  deriving DecidableEq, Fintype

/-- The dimension associated with each concrete factor. -/
def Factor.dimension : Factor → ℕ
  | .trivial => 1
  | .natural => 3
  | .dual => 3
  | .adjoint => 8

variable (K : Type*) [Field K]

/-- Trace-zero endomorphisms of the three-dimensional natural space. -/
abbrev AdjointSpace := (LinearMap.trace K (Fin 3 → K)).ker

/-- The actual carrier of each factor. -/
def Space : Factor → Type _
  | .trivial => K
  | .natural => Fin 3 → K
  | .dual => Module.Dual K (Fin 3 → K)
  | .adjoint => AdjointSpace K

instance spaceAddCommGroup (a : Factor) : AddCommGroup (Space K a) := by
  cases a <;> unfold Space <;> infer_instance
instance spaceModule (a : Factor) : Module K (Space K a) := by
  cases a <;> unfold Space <;> infer_instance
instance spaceFiniteDimensional (a : Factor) : FiniteDimensional K (Space K a) := by
  cases a <;> unfold Space <;> infer_instance

theorem finrank_adjointSpace : Module.finrank K (AdjointSpace K) = 8 := by
  have hsurj : Function.Surjective (LinearMap.trace K (Fin 3 → K)) := by
    intro c
    refine ⟨(LinearMap.proj (0 : Fin 3)).smulRight (Pi.single 0 c), ?_⟩
    simp [LinearMap.trace_smulRight]
  have h := (LinearMap.trace K (Fin 3 → K)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top,
    Module.finrank_self, Module.finrank_linearMap] at h
  have hv : Module.finrank K (Fin 3 → K) = 3 := by simp
  rw [hv] at h
  change 1 + Module.finrank K (AdjointSpace K) = 3 * 3 at h
  omega

theorem finrank_space (a : Factor) : Module.finrank K (Space K a) = a.dimension := by
  cases a <;> simp [Space, Factor.dimension, finrank_adjointSpace]

variable {F : Type*} [Field F] {K}

/-- The natural action through the chosen coefficient embedding. -/
def natural (ι : F →+* K) : Representation K SL(3,F) (Fin 3 → K) :=
  (specialLinearNatural 3).comp (Matrix.SpecialLinearGroup.map ι)

/-- The conjugation-stable trace kernel. -/
noncomputable def traceZero (ι : F →+* K) :
    Subrepresentation ((natural ι).linHom (natural ι)) where
  toSubmodule := LinearMap.ker (LinearMap.trace K (Fin 3 → K))
  apply_mem_toSubmodule g f hf := by
    change LinearMap.trace K (Fin 3 → K)
      (natural ι g ∘ₗ f ∘ₗ natural ι g⁻¹) = 0
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
    have hh : natural ι g⁻¹ ∘ₗ natural ι g = LinearMap.id := by
      rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [hh, LinearMap.comp_id]
    exact hf

/-- The actual trivial, natural, dual, or adjoint representation. -/
noncomputable def factorRep (ι : F →+* K) : (a : Factor) →
    Representation K SL(3,F) (Space K a)
  | .trivial => Representation.trivial K SL(3,F) K
  | .natural => natural ι
  | .dual => (natural ι).dual
  | .adjoint => (traceZero ι).toRepresentation

/-- Bundling the iterated tensor carrier also retains its module instances. -/
def WordModule (K : Type*) [Field K] : List Factor → ModuleCat K
  | [] => ModuleCat.of K K
  | a :: w => ModuleCat.of K (Space K a ⊗[K] WordModule K w)

/-- The carrier of an iterated tensor product, with the empty product equal to K. -/
abbrev WordSpace (K : Type*) [Field K] (w : List Factor) : Type _ := WordModule K w

instance wordSpaceFiniteDimensional (w : List Factor) :
    FiniteDimensional K (WordSpace K w) := by
  induction w with
  | nil => change FiniteDimensional K K; infer_instance
  | cons a w ih =>
    change FiniteDimensional K (Space K a ⊗[K] WordSpace K w)
    infer_instance

/-- Tensor factors in increasing Frobenius order, starting at the given embedding. -/
noncomputable def wordRep [CharP K 2] (ι : F →+* K) : (w : List Factor) →
    Representation K SL(3,F) (WordSpace K w)
  | [] => Representation.trivial K SL(3,F) K
  | a :: w => (factorRep ι a).tprod (wordRep ((frobenius K 2).comp ι) w)

/-- Product of the dimensions of the factors in a word. -/
def wordDegree (w : List Factor) : ℕ := (w.map Factor.dimension).prod

variable (K) in
theorem finrank_wordSpace (w : List Factor) :
    Module.finrank K (WordSpace K w) = wordDegree w := by
  induction w with
  | nil => simp [WordSpace, WordModule, wordDegree]
  | cons a w ih =>
    change Module.finrank K (Space K a ⊗[K] WordSpace K w) = _
    rw [Module.finrank_tensorProduct, finrank_space, ih]
    simp [wordDegree]

/-- Number of natural and dual factors, keeping their labels distinct. -/
def naturalCount (w : List Factor) : ℕ :=
  w.countP (fun a => a == .natural || a == .dual)

/-- Number of adjoint factors. -/
def adjointCount (w : List Factor) : ℕ := w.count .adjoint

theorem wordDegree_eq (w : List Factor) :
    wordDegree w = 3 ^ naturalCount w * 8 ^ adjointCount w := by
  induction w with
  | nil => simp [wordDegree, naturalCount, adjointCount]
  | cons a w ih =>
    cases a <;>
      simp [wordDegree, naturalCount, adjointCount, Factor.dimension,
        pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] at ih ⊢ <;>
      omega

theorem wordDegree_append (u v : List Factor) :
    wordDegree (u ++ v) = wordDegree u * wordDegree v := by
  simp [wordDegree]

theorem wordDegree_repeat (w : List Factor) (t : ℕ) :
    wordDegree (List.replicate t w).flatten = (3 ^ naturalCount w * 8 ^ adjointCount w) ^ t := by
  rw [← wordDegree_eq]
  induction t with
  | zero => simp [wordDegree]
  | succ t ih => simp [List.replicate_succ, wordDegree_append, ih, pow_succ, Nat.mul_comm]

theorem naturalCount_repeat (w : List Factor) (t : ℕ) :
    naturalCount (List.replicate t w).flatten = t * naturalCount w := by
  induction t with
  | zero => simp [naturalCount]
  | succ t ih =>
    simp [List.replicate_succ, naturalCount, List.countP_append, Nat.succ_mul] at ih ⊢
    omega

theorem adjointCount_repeat (w : List Factor) (t : ℕ) :
    adjointCount (List.replicate t w).flatten = t * adjointCount w := by
  induction t with
  | zero => simp [adjointCount]
  | succ t ih =>
    simp [List.replicate_succ, adjointCount, Nat.succ_mul] at ih ⊢
    omega

theorem wordRep_eq_one_of_counts_zero [CharP K 2] (ι : F →+* K)
    (w : List Factor) (ha : naturalCount w = 0) (hb : adjointCount w = 0)
    (g : SL(3,F)) : wordRep ι w g = 1 := by
  induction w generalizing ι with
  | nil => rfl
  | cons a w ih =>
    cases a with
    | trivial =>
      have ha' : naturalCount w = 0 := by simpa [naturalCount] using ha
      have hb' : adjointCount w = 0 := by simpa [adjointCount] using hb
      change TensorProduct.map (factorRep ι .trivial g)
        (wordRep ((frobenius K 2).comp ι) w g) = 1
      rw [ih _ ha' hb']
      change TensorProduct.map 1 1 = 1
      exact TensorProduct.map_one
    | natural => simp [naturalCount] at ha
    | dual => simp [naturalCount] at ha
    | adjoint => simp [adjointCount] at hb

end Representation.SL3.BinaryDefiningFactors
