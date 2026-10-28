module

public import Theory.Representation.BinaryOffender.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Fixed codimension under scalar twists, sections, and subgroup inclusion

The fixed codimension of an operator is the rank of its displacement. Equivariant
injections and surjections therefore compare fixed codimensions; composing these
comparisons gives transfer from an invariant section to the ambient module.

If an operator is semilinear for a nonidentity field endomorphism, multiplication
by a moved scalar embeds its fixed space into its displacement space. Consequently
its fixed codimension is at least half the ambient dimension. This argument allows
arbitrary mixing of isomorphic summands. A subspace disjoint from its image also
embeds in the displacement space, giving the bound needed for permuted summands.

These are local linear-algebra ingredients for GLS, *The Classification of the
Finite Simple Groups*, vol. 2, Theorem 26.24, final paragraph (ChapterG.tex,
line 1248). They neither construct natural sections nor classify intertwiners.
-/

@[expose] public section

open Module

namespace Representation.BinaryOffender.NaturalTensor

variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- The codimension of the fixed space, expressed as displacement rank. -/
noncomputable def operatorFixedCodim (T : Module.End k V) : ℕ :=
  finrank k (LinearMap.range (T - 1))

/-- Rank-nullity for an operator and its fixed space. -/
theorem operatorFixedCodim_add_finrank [FiniteDimensional k V] (T : Module.End k V) :
    operatorFixedCodim T + finrank k (LinearMap.ker (T - 1)) = finrank k V :=
  (T - 1).finrank_range_add_finrank_ker

/-- Displacement rank is the dimension of the quotient by fixed vectors. -/
theorem operatorFixedCodim_eq_finrank_quotient (T : Module.End k V) :
    operatorFixedCodim T = finrank k (V ⧸ LinearMap.ker (T - 1)) :=
  (LinearMap.quotKerEquivRange (T - 1)).finrank_eq.symm

private def displacementMap (T : Module.End k V) (S : Module.End k W) (f : V →ₗ[k] W)
    (h : ∀ v, f (T v) = S (f v)) :
    LinearMap.range (T - 1) →ₗ[k] LinearMap.range (S - 1) :=
  (f.comp (LinearMap.range (T - 1)).subtype).codRestrict _ (by
    rintro ⟨x, v, rfl⟩
    refine ⟨f v, ?_⟩
    change S (f v) - f v = f (T v - v)
    rw [map_sub, h])

/-- Equivariant embeddings do not increase fixed codimension. -/
theorem operatorFixedCodim_le_of_injective [FiniteDimensional k W]
    (T : Module.End k V) (S : Module.End k W) (f : V →ₗ[k] W)
    (hf : Function.Injective f) (h : ∀ v, f (T v) = S (f v)) :
    operatorFixedCodim T ≤ operatorFixedCodim S := by
  apply LinearMap.finrank_le_finrank_of_injective (f := displacementMap T S f h)
  intro x y hxy
  exact Subtype.ext (hf (congrArg Subtype.val hxy))

/-- Equivariant quotients do not increase fixed codimension. -/
theorem operatorFixedCodim_le_of_surjective [FiniteDimensional k V]
    (T : Module.End k V) (S : Module.End k W) (f : V →ₗ[k] W)
    (hf : Function.Surjective f) (h : ∀ v, f (T v) = S (f v)) :
    operatorFixedCodim S ≤ operatorFixedCodim T := by
  apply LinearMap.finrank_le_finrank_of_surjective (f := displacementMap T S f h)
  rintro ⟨y, w, rfl⟩
  obtain ⟨v, rfl⟩ := hf w
  refine ⟨⟨(T - 1) v, v, rfl⟩, ?_⟩
  apply Subtype.ext
  change f (T v - v) = S (f v) - f v
  rw [map_sub, h]

/-- Fixed codimension is independent of equivariant coordinates. -/
theorem operatorFixedCodim_eq_of_equiv [FiniteDimensional k V] [FiniteDimensional k W]
    (T : Module.End k V) (S : Module.End k W) (e : V ≃ₗ[k] W)
    (h : ∀ v, e (T v) = S (e v)) : operatorFixedCodim T = operatorFixedCodim S :=
  le_antisymm (operatorFixedCodim_le_of_injective T S e.toLinearMap e.injective h)
    (operatorFixedCodim_le_of_surjective T S e.toLinearMap e.surjective h)

/-- Transfer from an actual equivariant quotient of an invariant subspace. -/
theorem operatorFixedCodim_le_of_section [FiniteDimensional k V]
    (T : Module.End k V) (U : Submodule k V) (R : Module.End k U)
    (S : Module.End k W) (q : U →ₗ[k] W) (hq : Function.Surjective q)
    (hi : ∀ u : U, (R u : V) = T u) (he : ∀ u, q (R u) = S (q u)) :
    operatorFixedCodim S ≤ operatorFixedCodim T :=
  (operatorFixedCodim_le_of_surjective R S q hq he).trans
    (operatorFixedCodim_le_of_injective R T U.subtype Subtype.val_injective hi)

section Semilinear
variable {F : Type*} [Field F] [Algebra k F] [Module F V] [IsScalarTower k F V]

/-- Multiplication by a moved scalar embeds fixed vectors in displacement vectors. -/
theorem fixed_finrank_le_operatorFixedCodim [FiniteDimensional k V]
    (T : Module.End k V) (σ : F →+* F)
    (hσ : ∃ a, σ a ≠ a) (hT : ∀ a v, T (a • v) = σ a • T v) :
    finrank k (LinearMap.ker (T - 1)) ≤ operatorFixedCodim T := by
  obtain ⟨a, ha⟩ := hσ
  let K := LinearMap.ker (T - 1)
  let f : K →ₗ[k] LinearMap.range (T - 1) :=
    ((T - 1).comp (((LinearMap.lsmul F V a).restrictScalars k).comp K.subtype)).codRestrict _
      (fun v => ⟨a • (v : V), rfl⟩)
  have hf (v : K) : (f v : V) = (σ a - a) • (v : V) := by
    have hv : T (v : V) = v := sub_eq_zero.mp v.property
    change T (a • (v : V)) - a • (v : V) = _
    rw [hT, hv, sub_smul]
  apply LinearMap.finrank_le_finrank_of_injective (f := f)
  intro x y hxy
  apply Subtype.ext
  apply smul_right_injective V (sub_ne_zero.mpr ha)
  simpa only [hf] using congrArg Subtype.val hxy

/-- A nontrivial scalar twist moves at least half the ambient dimension. -/
theorem finrank_le_twice_operatorFixedCodim [FiniteDimensional k V]
    (T : Module.End k V) (σ : F →+* F)
    (hσ : ∃ a, σ a ≠ a) (hT : ∀ a v, T (a • v) = σ a • T v) :
    finrank k V ≤ 2 * operatorFixedCodim T := by
  have h := fixed_finrank_le_operatorFixedCodim T σ hσ hT
  have hd := operatorFixedCodim_add_finrank T
  omega

end Semilinear

/-- A summand moved to a disjoint summand contributes its full dimension. -/
theorem finrank_le_operatorFixedCodim_of_disjoint [FiniteDimensional k V]
    (T : Module.End k V) (U : Submodule k V) (hU : Disjoint U (U.map T)) :
    finrank k U ≤ operatorFixedCodim T := by
  let f : U →ₗ[k] LinearMap.range (T - 1) :=
    ((T - 1).comp U.subtype).codRestrict _ (fun u => ⟨u, rfl⟩)
  apply LinearMap.finrank_le_finrank_of_injective (f := f)
  apply (LinearMap.ker_eq_bot).mp
  apply (Submodule.eq_bot_iff _).mpr
  intro u hu
  have hfix : T (u : V) = u := by
    have h := congrArg Subtype.val (show f u = 0 from hu)
    exact sub_eq_zero.mp h
  apply Subtype.ext
  exact (Submodule.disjoint_def.mp hU) u u.property ⟨u, u.property, hfix⟩

section Actor
variable {G : Type*} [Group G] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- An element's fixed-codimension bound passes to every subgroup containing it. -/
theorem operatorFixedCodim_le_fixedCodim (ρ : Representation (ZMod 2) G V)
    (A : Subgroup G) {a : G} (ha : a ∈ A) :
    operatorFixedCodim (ρ a) ≤ fixedCodim ρ A := by
  have hle : fixedSpace ρ A ≤ LinearMap.ker (ρ a - 1) := by
    intro v hv
    exact sub_eq_zero.mpr (hv ⟨a, ha⟩)
  have hd := operatorFixedCodim_add_finrank (ρ a)
  have hA := fixedCodim_add_finrank ρ A
  have hdim := Submodule.finrank_mono hle
  omega

/-- Enlarging the actor increases fixed codimension. -/
theorem fixedCodim_mono (ρ : Representation (ZMod 2) G V)
    {A B : Subgroup G} (hAB : A ≤ B) : fixedCodim ρ A ≤ fixedCodim ρ B := by
  have hle : fixedSpace ρ B ≤ fixedSpace ρ A := by
    intro v hv a
    exact hv ⟨a, hAB a.property⟩
  have hA := fixedCodim_add_finrank ρ A
  have hB := fixedCodim_add_finrank ρ B
  have hdim := Submodule.finrank_mono hle
  omega

/-- Combined transfer from a cyclic actor on an invariant section to an ambient overgroup. -/
theorem section_operatorFixedCodim_le_fixedCodim
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G) {a : G} (ha : a ∈ A)
    [Module (ZMod 2) W] (U : Submodule (ZMod 2) V) (R : Module.End (ZMod 2) U)
    (S : Module.End (ZMod 2) W) (q : U →ₗ[ZMod 2] W) (hq : Function.Surjective q)
    (hi : ∀ u : U, (R u : V) = ρ a u) (he : ∀ u, q (R u) = S (q u)) :
    operatorFixedCodim S ≤ fixedCodim ρ A :=
  (operatorFixedCodim_le_of_section (ρ a) U R S q hq hi he).trans
    (operatorFixedCodim_le_fixedCodim ρ A ha)

end Actor

end Representation.BinaryOffender.NaturalTensor
