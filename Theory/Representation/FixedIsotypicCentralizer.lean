module
public import Theory.Representation.NormalSpanConstituents
public import Theory.Representation.NormalInvariants
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Theory.Representation.ExtendScalars
/-!
# Actors fixing a full isotypic part centralize the complementary action

If a normal subgroup's trivial type and one other type span the full module,
an actor fixing that entire second span commutes with the normal subgroup.
Faithfulness of the full action therefore puts the original actor inside its
centralizer. No faithfulness of either summand is needed. Scalar extension and
an original quotient map are retained in the quotient version.

The type-span comparison with the canonical isotypic component allows the
actual multiplicity-space fixation theorem to supply the input. Equivalent
markings and surjective actor maps preserve those spans.

Source application: Aschbacher--Smith, original terminal Suzuki argument in
§13.6, printed p.935.
-/

public section
open Subgroup Representation
open scoped TensorProduct MonoidAlgebra
namespace Representation
variable {k G V W : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Images of the trivial line consist of fixed vectors. -/
theorem typeSpan_trivial_le_invariants (ρ : Representation k G V) :
    (typeSpan ρ (trivial k G k)).toSubmodule ≤ invariants ρ := by
  let I : Subrepresentation ρ := {
    toSubmodule := invariants ρ
    apply_mem_toSubmodule := by
      intro g v hv
      simpa only [hv g] using hv }
  change typeSpan ρ (trivial k G k) ≤ I
  apply iSup_le
  intro f v hv
  obtain ⟨x,rfl⟩ := hv
  intro g
  have hh := DFunLike.congr_fun (f.isIntertwining' g) x
  exact hh.symm

/-- Fixing the entire nontrivial type span makes the actor commute with the
normal subgroup on the full representation. -/
theorem commute_of_fixed_typeSpan
    (ρ : Representation k G V) (D : Subgroup G) [D.Normal]
    (τ : Representation k D W)
    (hspan : typeSpan (ρ.comp D.subtype) (trivial k D k) ⊔
      typeSpan (ρ.comp D.subtype) τ = ⊤)
    (a : G) (ha : ∀ v ∈ typeSpan (ρ.comp D.subtype) τ, ρ a v = v)
    (d : D) : ρ (a * d.val) = ρ (d.val * a) := by
  ext v
  have hv : v ∈ (typeSpan (ρ.comp D.subtype) (trivial k D k) ⊔
      typeSpan (ρ.comp D.subtype) τ).toSubmodule := by rw [hspan]; trivial
  obtain ⟨v₀,hv₀,v₁,hv₁,rfl⟩ := Submodule.mem_sup.mp hv
  have hfix : ρ d.val v₀ = v₀ := typeSpan_trivial_le_invariants _ hv₀ d
  have hfixa : ρ d.val (ρ a v₀) = ρ a v₀ :=
    typeSpan_trivial_le_invariants _
      (typeSpan_normal_stable ρ D (trivial k D k) (conjugate_trivial_equiv D) a v₀ hv₀) d
  have hfixd : ρ a (ρ d.val v₁) = ρ d.val v₁ :=
    ha _ ((typeSpan (ρ.comp D.subtype) τ).apply_mem_toSubmodule d hv₁)
  simp only [map_mul, Module.End.mul_apply, map_add, hfix, hfixa, ha v₁ hv₁, hfixd]

/-- The original actor embeds in the centralizer when its faithful action
fixes the full nontrivial type span. -/
theorem le_centralizer_of_fixed_typeSpan
    (ρ : Representation k G V) (hf : Function.Injective ρ)
    (D : Subgroup G) [D.Normal] (τ : Representation k D W)
    (hspan : typeSpan (ρ.comp D.subtype) (trivial k D k) ⊔
      typeSpan (ρ.comp D.subtype) τ = ⊤)
    (A : Subgroup G)
    (hfix : ∀ a ∈ A, ∀ v ∈ typeSpan (ρ.comp D.subtype) τ, ρ a v = v) :
    A ≤ centralizer (D : Set G) := by
  intro a ha
  apply mem_centralizer_iff.mpr
  intro d hd
  exact (hf (commute_of_fixed_typeSpan ρ D τ hspan a (hfix a ha) ⟨d,hd⟩)).symm
/-- Every intertwiner image of an irreducible type belongs to its canonical
isotypic component. No constituent is selected. -/
theorem typeSpan_le_isotypicComponent
    (ρ : Representation k G V) (τ : Representation k G W) [τ.IsIrreducible] :
    typeSpan ρ τ ≤ Subrepresentation.ofSubmodule' (isotypicComponent k[G] ρ.asModule τ.asModule) := by
  apply iSup_le
  intro f
  let l := IntertwiningMap.equivLinearMapAsModule τ ρ f
  have hl : l.range ≤ isotypicComponent k[G] ρ.asModule τ.asModule := by
    obtain hi | hz := l.injective_or_eq_zero
    · exact le_sSup ⟨(LinearEquiv.ofInjective l hi).symm⟩
    · rw [hz, LinearMap.range_zero]
      exact bot_le
  intro v hv
  exact hl hv

/-- Equivalent model types have the same span of intertwiner images. -/
theorem typeSpan_eq_of_equiv
    {E : Type*} [AddCommGroup E] [Module k E]
    (ρ : Representation k G V) {τ : Representation k G W} {υ : Representation k G E}
    (e : τ.Equiv υ) : typeSpan ρ τ = typeSpan ρ υ := by
  apply le_antisymm
  · apply iSup_le
    intro f
    let f' := f.comp e.symm.toIntertwiningMap
    intro v hv
    obtain ⟨w,rfl⟩ := hv
    apply (show f'.range ≤ typeSpan ρ υ from le_iSup _ f')
    refine ⟨e w, ?_⟩
    change f (e.symm (e w)) = f w
    rw [e.symm_apply_apply]
  · apply iSup_le
    intro f
    let f' := f.comp e.toIntertwiningMap
    intro v hv
    obtain ⟨w,rfl⟩ := hv
    apply (show f'.range ≤ typeSpan ρ τ from le_iSup _ f')
    refine ⟨e.symm w, ?_⟩
    change f (e (e.symm w)) = f w
    rw [e.apply_symm_apply]

/-- Pulling back through a surjection does not change a model type span. -/
theorem typeSpan_comp_surjective
    {X : Type*} [Group X] (p : X →* G) (hp : Function.Surjective p)
    (ρ : Representation k G V) (τ : Representation k G W) :
    typeSpan (ρ.comp p) (τ.comp p) = (typeSpan ρ τ).compActors p := by
  apply le_antisymm
  · apply iSup_le
    intro f
    let f' : τ.IntertwiningMap ρ := {
      toLinearMap := f.toLinearMap
      isIntertwining' g := by obtain ⟨x,rfl⟩ := hp g; exact f.isIntertwining' x }
    intro v hv
    exact (show f'.range ≤ typeSpan ρ τ from le_iSup _ f') hv
  · let R := typeSpan (ρ.comp p) (τ.comp p)
    let S : Subrepresentation ρ := {
      toSubmodule := R.toSubmodule
      apply_mem_toSubmodule g v hv := by
        obtain ⟨x,rfl⟩ := hp g
        exact R.apply_mem_toSubmodule x hv }
    have he : typeSpan ρ τ ≤ S := by
      apply iSup_le
      intro f
      exact (show (f.compActors τ ρ p).range ≤ R from le_iSup _ (f.compActors τ ρ p))
    exact he

section Quotient
variable {F X U : Type*} [Field F] [Group X] [AddCommGroup U] [Module F U]
  [Algebra F k]

/-- A constituent decomposition before a quotient still controls the same
actor after quotienting, provided its full action there is faithful. -/
theorem le_centralizer_image_of_fixed_typeSpan
    (q : G →* X) (hq : Function.Surjective q)
    (σ : Representation F X U) (hf : Function.Injective σ)
    (D : Subgroup G) [D.Normal] (τ : Representation k D W)
    (hspan : typeSpan ((extendScalars k (σ.comp q)).comp D.subtype) (trivial k D k) ⊔
      typeSpan ((extendScalars k (σ.comp q)).comp D.subtype) τ = ⊤)
    (A : Subgroup X)
    (hfix : ∀ a : G, q a ∈ A →
      ∀ v ∈ typeSpan ((extendScalars k (σ.comp q)).comp D.subtype) τ,
        extendScalars k (σ.comp q) a v = v) :
    A ≤ centralizer (D.map q : Set X) := by
  intro a ha
  obtain ⟨x,rfl⟩ := hq a
  apply mem_centralizer_iff.mpr
  rintro d ⟨y,hy,rfl⟩
  have hh := commute_of_fixed_typeSpan (extendScalars k (σ.comp q)) D τ hspan
    x (hfix x ha) ⟨y,hy⟩
  apply ((extendScalars_faithful_iff k σ).mp hf)
  simpa only [extendScalars_apply, MonoidHom.comp_apply, map_mul] using hh.symm
end Quotient
end Representation
