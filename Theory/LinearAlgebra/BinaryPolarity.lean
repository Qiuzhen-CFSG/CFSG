module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.FinCases

/-!
# A binary polarity is an alternating form

Every hyperplane over F₂ has a unique nonzero defining functional. Extending
these functionals by zero at the zero vector gives a symmetric pairing from
symmetric incidence, hence a bilinear form. Self-incidence makes it alternating,
and proper hyperplanes make it nondegenerate. Equivariance of the hyperplanes
then gives actual form invariance. The construction needs no enumeration of
linear groups and retains each original hyperplane as the exact kernel.

Source application: Aschbacher, Sporadic Groups, Exercise 15.1 and Lemma45.6,
printed p.244 (the symplectic recognition in the U₄(3) configuration).
-/

public section

namespace BinaryPolarity
open LinearMap
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem bit_eq_of_zero_iff {x y : ZMod 2} (h : x=0 ↔ y=0) : x=y := by
  revert x y
  decide

variable (f : {x : V // x ≠ 0} → V →ₗ[ZMod 2] ZMod 2)

noncomputable def pairing (x : V) : V →ₗ[ZMod 2] ZMod 2 := by
  classical
  exact if h : x=0 then 0 else f ⟨x,h⟩

theorem pairing_nonzero {x : V} (h : x≠0) : pairing f x = f ⟨x,h⟩ := dif_neg h

theorem pairing_zero : pairing f 0 = 0 := dif_pos rfl

theorem pairing_symm
    (hs : ∀ (x y : {x : V // x≠0}), f x y = 0 ↔ f y x = 0) (x y : V) :
    pairing f x y = pairing f y x := by
  by_cases hx : x=0
  · subst x; simp [pairing_zero]
  by_cases hy : y=0
  · subst y; simp [pairing_zero]
  rw [pairing_nonzero f hx, pairing_nonzero f hy]
  exact bit_eq_of_zero_iff (hs ⟨x,hx⟩ ⟨y,hy⟩)

noncomputable def form (hs : ∀ (x y : {x : V // x≠0}), f x y=0 ↔ f y x=0) : LinearMap.BilinForm (ZMod 2) V where
  toFun := pairing f
  map_add' x y := by
    ext z
    rw [pairing_symm f hs (x+y) z, map_add]
    exact congrArg₂ (·+·) (pairing_symm f hs z x) (pairing_symm f hs z y)
  map_smul' r x := by
    ext z
    rw [pairing_symm f hs (r • x) z, map_smul]
    exact congrArg (r • ·) (pairing_symm f hs z x)

theorem form_nondegenerate (hs : ∀ (x y : {x : V // x≠0}), f x y=0 ↔ f y x=0)
    (hf : ∀ x, f x ≠ 0) : (form f hs).Nondegenerate := by
  have hleft : (form f hs).SeparatingLeft := by
    intro x hx
    by_contra hn
    apply hf ⟨x,hn⟩
    ext y
    have hz := hx y
    change pairing f x y = 0 at hz
    rwa [pairing_nonzero f hn] at hz
  refine ⟨hleft,?_⟩
  intro x hx
  apply hleft x
  intro y
  exact (pairing_symm f hs x y).trans (hx y)

theorem form_alternating (hs : ∀ (x y : {x : V // x≠0}), f x y=0 ↔ f y x=0)
    (ha : ∀ x, f x x=0) : (form f hs).IsAlt := by
  intro x
  by_cases hx : x=0
  · subst x; change pairing f 0 0=0; rw [pairing_zero]; rfl
  change pairing f x x=0
  rw [pairing_nonzero f hx]
  exact ha ⟨x,hx⟩

theorem exists_nonzero_functional (W : Submodule (ZMod 2) V) (hW : IsCoatom W) :
    ∃ f : V →ₗ[ZMod 2] ZMod 2, f≠0 ∧ f.ker=W := by
  obtain ⟨f,hf,hWf⟩ := W.exists_le_ker_of_lt_top hW.lt_top
  exact ⟨f,hf,(hW.le_iff_eq (fun ht => hf (LinearMap.ker_eq_top.mp ht))).mp hWf⟩

noncomputable def hyperplaneFunctional
    (P : {x : V // x≠0} → {W : Submodule (ZMod 2) V // IsCoatom W})
    (x : {x : V // x≠0}) : V →ₗ[ZMod 2] ZMod 2 :=
  (exists_nonzero_functional (P x).val (P x).property).choose

theorem hyperplaneFunctional_ne_zero
    (P : {x : V // x≠0} → {W : Submodule (ZMod 2) V // IsCoatom W})
    (x : {x : V // x≠0}) : hyperplaneFunctional P x ≠ 0 :=
  (exists_nonzero_functional (P x).val (P x).property).choose_spec.1

theorem hyperplaneFunctional_ker
    (P : {x : V // x≠0} → {W : Submodule (ZMod 2) V // IsCoatom W})
    (x : {x : V // x≠0}) : (hyperplaneFunctional P x).ker = (P x).val :=
  (exists_nonzero_functional (P x).val (P x).property).choose_spec.2

theorem exists_form_of_hyperplanes
    (P : {x : V // x≠0} → {W : Submodule (ZMod 2) V // IsCoatom W})
    (hs : ∀ x y : {x : V // x≠0}, x.val ∈ (P y).val ↔ y.val ∈ (P x).val)
    (ha : ∀ x, x.val ∈ (P x).val) :
    ∃ B : LinearMap.BilinForm (ZMod 2) V, B.IsAlt ∧ B.Nondegenerate ∧
      ∀ (x : {x : V // x≠0}) (y : V), B x y=0 ↔ y∈(P x).val := by
  let f := hyperplaneFunctional P
  have hk (x : {x : V // x≠0}) (y : V) : f x y=0 ↔ y∈(P x).val := by
    change y∈(f x).ker ↔ _
    rw [hyperplaneFunctional_ker]
  have hsym : ∀ x y : {x : V // x≠0}, f x y=0 ↔ f y x=0 :=
    fun x y => (hk x y).trans ((hs y x).trans (hk y x).symm)
  refine ⟨form f hsym, form_alternating f hsym (fun x => (hk x x).mpr (ha x)),
    form_nondegenerate f hsym (hyperplaneFunctional_ne_zero P), ?_⟩
  intro x y
  change pairing f x y=0 ↔ _
  rw [pairing_nonzero f x.property]
  exact hk x y

theorem invariant_of_hyperplane_equivariance
    (P : {x : V // x≠0} → {W : Submodule (ZMod 2) V // IsCoatom W})
    (B : LinearMap.BilinForm (ZMod 2) V)
    (hB : ∀ (x : {x : V // x≠0}) (y : V), B x y=0 ↔ y∈(P x).val)
    (g : V ≃ₗ[ZMod 2] V)
    (hP : ∀ x : {x : V // x≠0}, (P ⟨g x,fun hz => x.property (g.map_eq_zero_iff.mp hz)⟩).val =
      (P x).val.map g.toLinearMap) (x y : V) : B (g x) (g y)=B x y := by
  by_cases hx : x=0
  · subst x; simp
  apply bit_eq_of_zero_iff
  rw [hB ⟨g x,fun hz => hx (g.map_eq_zero_iff.mp hz)⟩ (g y),hP ⟨x,hx⟩,hB ⟨x,hx⟩ y]
  constructor
  · rintro ⟨z,hz,he⟩
    exact g.injective he ▸ hz
  · exact fun hy => ⟨y,hy,rfl⟩
end BinaryPolarity
