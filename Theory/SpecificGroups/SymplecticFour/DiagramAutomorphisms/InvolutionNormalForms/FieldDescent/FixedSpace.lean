module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Fixed spaces of semilinear involutions

For a nontrivial coefficient automorphism σ and a σ-semilinear involution T,
the vectors v + T(v) span over the full field: combine the traces of v and
av for any scalar a moved by σ. A basis extracted from the fixed vectors
has fixed coordinates precisely on the fixed space. Thus descent preserves
dimension, and a compatible nondegenerate alternating form descends to a
nondegenerate alternating form over the actual fixed subfield.

These are the linear-algebra inputs to symplectic field-cocycle elimination
in `FieldDescent.lean`, used for Aschbacher–Smith, Lemma 16.1.4(4), printed
p.1171 of `refs/quasithin.pdf`. No averaging by the group order is used.
-/

@[expose] public section

open Module
noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.FieldDescent
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Fixed vectors span over the full coefficient field, even in characteristic two. -/
theorem span_fixed (σ : F ≃+* F) (hσ : σ ≠ 1) (T : V →+ V)
    (hT : ∀ a v, T (a • v) = σ a • T v) (hTT : ∀ v, T (T v) = v) :
    Submodule.span F {v : V | T v = v} = ⊤ := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra! h
    apply hσ
    ext a
    exact h a
  let W := Submodule.span F {v : V | T v = v}
  have hsum (v : V) : v + T v ∈ W := by
    apply Submodule.subset_span
    simp only [Set.mem_ofPred_eq, map_add, hTT, add_comm]
  apply top_unique
  intro v _
  have hm : (a - σ a) • v ∈ W := by
    have h := W.sub_mem (hsum (a • v)) (W.smul_mem (σ a) (hsum v))
    simpa only [hT, smul_add, sub_smul, add_sub_add_right_eq_sub] using h
  have ha0 : a - σ a ≠ 0 := sub_ne_zero.mpr ha.symm
  simpa only [smul_smul, inv_mul_cancel₀ ha0, one_smul] using W.smul_mem (a - σ a)⁻¹ hm

/-- Extract a basis of fixed vectors from the spanning assertion. -/
theorem exists_fixed_basis (σ : F ≃+* F) (hσ : σ ≠ 1) (T : V →+ V)
    (hT : ∀ a v, T (a • v) = σ a • T v) (hTT : ∀ v, T (T v) = v) :
    ∃ (s : Set V) (b : Basis s F V), ∀ i, T (b i) = b i := by
  let s : Set V := {v | T v = v}
  have hs : ⊤ ≤ Submodule.span F s := le_of_eq (span_fixed σ hσ T hT hTT).symm
  refine ⟨_, Basis.ofSpan hs, ?_⟩
  intro i
  exact Basis.extendLe_subset (linearIndependent_empty F V) (Set.empty_subset s) hs
    (Set.mem_range_self i)

/-- The actual subfield fixed by the coefficient automorphism. -/
def fixedField (σ : F ≃+* F) : Subfield F :=
  σ.toRingHom.eqLocusField (RingHom.id F)

/-- Fixed vectors form a vector space over the fixed subfield. -/
def fixedSpace (σ : F ≃+* F) (T : V →+ V)
    (hT : ∀ a v, T (a • v) = σ a • T v) : Submodule (fixedField σ) V where
  carrier := {v | T v = v}
  zero_mem' := map_zero T
  add_mem' hx hy := by
    change T (_ + _) = _
    rw [map_add, hx, hy]
  smul_mem' a v hv := by
    change T ((a : F) • v) = (a : F) • v
    rw [hT, show σ (a : F) = a from a.property, hv]

/-- Fixed coordinates identify the descended dimension with the original dimension. -/
theorem fixedSpace_finrank [FiniteDimensional F V]
    (σ : F ≃+* F) (hσ : σ ≠ 1) (T : V →+ V)
    (hT : ∀ a v, T (a • v) = σ a • T v) (hTT : ∀ v, T (T v) = v) :
    Module.finrank (fixedField σ) (fixedSpace σ T hT) = Module.finrank F V := by
  classical
  obtain ⟨s, b, hb⟩ := exists_fixed_basis σ hσ T hT hTT
  let : Finite s := Module.Finite.finite_basis b
  let : Fintype s := Fintype.ofFinite s
  have hact (c : s → F) :
      T (b.equivFun.symm c) = b.equivFun.symm (fun i => σ (c i)) := by
    simp only [b.equivFun_symm_apply, map_sum, hT, hb]
  have hcoord (v : V) (i : s) : b.equivFun (T v) i = σ (b.equivFun v i) := by
    have h := congrArg (fun w => b.equivFun w i) (hact (b.equivFun v))
    simpa only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply] using h
  let f : fixedSpace σ T hT →ₗ[fixedField σ] (s → fixedField σ) :=
    { toFun := fun v i => ⟨b.equivFun v i, by
        change σ (b.equivFun v i) = b.equivFun v i
        rw [← hcoord, show T (v : V) = v from v.property]⟩
      map_add' := fun v w => by ext i; simp
      map_smul' := fun a v => by
        ext i
        exact congrFun (b.equivFun.toLinearMap.restrictScalars (fixedField σ)
          |>.map_smul a (v : V)) i }
  have hf : Function.Bijective f := by
    constructor
    · intro v w h
      apply Subtype.ext
      apply b.equivFun.injective
      ext i
      exact congrArg Subtype.val (congrFun h i)
    · intro c
      refine ⟨⟨b.equivFun.symm (fun i => (c i : F)), ?_⟩, ?_⟩
      · change T _ = _
        rw [hact]
        congr 1
        funext i
        exact (c i).property
      · ext i
        exact congrFun (b.equivFun.apply_symm_apply (fun i => (c i : F))) i
  rw [(LinearEquiv.ofBijective f hf).finrank_eq, Module.finrank_eq_card_basis b]
  simp

/-- A compatible bilinear form takes fixed-field values on the fixed space. -/
def fixedForm (σ : F ≃+* F) (T : V →+ V)
    (hT : ∀ a v, T (a • v) = σ a • T v)
    (B : LinearMap.BilinForm F V) (hB : ∀ x y, B (T x) (T y) = σ (B x y)) :
    LinearMap.BilinForm (fixedField σ) (fixedSpace σ T hT) :=
  LinearMap.mk₂ (fixedField σ)
    (fun x y => ⟨B x y, by
      change σ (B x y) = B x y
      rw [← hB, show T (x : V) = x from x.property,
        show T (y : V) = y from y.property]⟩)
    (fun x y z => Subtype.ext (B.map_add₂ x y z))
    (fun a x y => Subtype.ext (by
      change B ((a : F) • (x : V)) (y : V) = (a : F) * B x y
      simp))
    (fun x y z => Subtype.ext (map_add (B (x : V)) (y : V) (z : V)))
    (fun a x y => Subtype.ext (by
      change B (x : V) ((a : F) • (y : V)) = (a : F) * B x y
      simp))

/-- The descended form remains alternating. -/
theorem fixedForm_alt (σ : F ≃+* F) (T : V →+ V)
    (hT : ∀ a v, T (a • v) = σ a • T v)
    (B : LinearMap.BilinForm F V) (hB : ∀ x y, B (T x) (T y) = σ (B x y))
    (hA : B.IsAlt) : (fixedForm σ T hT B hB).IsAlt := by
  intro x
  exact Subtype.ext (hA x)

/-- Full-field spanning prevents the descended form from acquiring a radical. -/
theorem fixedForm_nondegenerate (σ : F ≃+* F) (hσ : σ ≠ 1) (T : V →+ V)
    (hT : ∀ a v, T (a • v) = σ a • T v) (hTT : ∀ v, T (T v) = v)
    (B : LinearMap.BilinForm F V) (hB : ∀ x y, B (T x) (T y) = σ (B x y))
    (hA : B.IsAlt) (hN : B.Nondegenerate) :
    (fixedForm σ T hT B hB).Nondegenerate := by
  have hl : (fixedForm σ T hT B hB).SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    apply hN.1 x.val
    have hker : Submodule.span F {v : V | T v = v} ≤ (B x.val).ker := by
      apply Submodule.span_le.mpr
      intro y hy
      exact congrArg Subtype.val (hx ⟨y, hy⟩)
    rw [span_fixed σ hσ T hT hTT] at hker
    intro y
    exact hker (Submodule.mem_top : y ∈ (⊤ : Submodule F V))
  refine ⟨hl, ?_⟩
  intro x hx
  exact hl x (fun y => (fixedForm_alt σ T hT B hB hA).eq_iff.mpr (hx y))
end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.FieldDescent

