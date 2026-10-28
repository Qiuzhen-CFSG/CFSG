module
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.Action
public import Mathlib.LinearAlgebra.Projection
/-!
# Two-type homogeneous orbit coordinates

Homogeneity fixes every constituent under its type inertia subgroup. Therefore
an orbit with at most two simple types consists of at most two actual subspaces,
without multiplicities. Distinct members are disjoint, and when they span the
whole module the sum map is an equivariant equivalence with their product.

Source: Aschbacher–Smith A.1.42 and D.3.5, printed pp.32 and195–196.
The moved A5 product branch uses this to transport model bounds to the original
local quotient rather than lifting elementary actors through a quotient.
-/

public section
namespace Representation.BinaryOffender.Homogeneous.TypeAction
variable {E W P : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) E W} [Group P]
  (c : TypeAction σ P) (A : Subrepresentation σ)
  (hA : IsIrreducible A.toRepresentation)
  (hh : homogeneousPart A (c.span A).toSubmodule = A.toSubmodule)

include hA hh

/-- Homogeneity turns equality of two orbit types into equality of their
actual subspaces. -/
theorem conjugate_eq_of_sameModule (s t : P)
    (he : SameModule (c.conjugate s A) (c.conjugate t A)) :
    c.conjugate s A = c.conjugate t A := by
  let B : c.orbit A := ⟨_,s,rfl⟩
  let C : c.orbit A := ⟨_,t,rfl⟩
  by_contra hn
  exact c.orbit_not_sameModule A ((c.homogeneous_iff_inertia_fixes A hA).mp hh)
    B C (fun h => hn (congrArg Subtype.val h)) he

/-- A homogeneous orbit with at most two simple types is the sum of those
two actual orbit subspaces; no multiplicity bound is assumed. -/
theorem span_eq_sup_of_two_types (t : P)
    (htypes : ∀ s : P, SameModule A (c.conjugate s A) ∨
      SameModule (c.conjugate t A) (c.conjugate s A)) :
    c.span A = A ⊔ c.conjugate t A := by
  apply le_antisymm
  · apply iSup_le
    intro s
    rcases htypes s with hs | hs
    · have he := c.conjugate_eq_of_sameModule A hA hh 1 s (by simpa only [c.one] using hs)
      rw [c.one] at he
      exact he ▸ le_sup_left
    · rw [←c.conjugate_eq_of_sameModule A hA hh t s hs]
      exact le_sup_right
  · exact sup_le (c.le_span A) (le_iSup (fun s => c.conjugate s A) t)

/-- Distinct members of the homogeneous simple orbit are disjoint. -/
theorem disjoint_conjugate_of_ne (t : P) (hne : A ≠ c.conjugate t A) :
    Disjoint A.toSubmodule (c.conjugate t A).toSubmodule := by
  let B : c.orbit A := ⟨A,1,c.one A⟩
  let C : c.orbit A := ⟨_,t,rfl⟩
  have hn : B ≠ C := fun he => hne (congrArg Subtype.val he)
  exact (c.orbit_independent A hA hh).pairwiseDisjoint hn

/-- When the orbit spans the whole module, two different types give the
literal complementary subspaces needed for a direct-product model. -/
theorem isCompl_of_two_types (t : P) (hne : A ≠ c.conjugate t A)
    (htypes : ∀ s : P, SameModule A (c.conjugate s A) ∨
      SameModule (c.conjugate t A) (c.conjugate s A))
    (hspan : c.span A = ⊤) :
    IsCompl A.toSubmodule (c.conjugate t A).toSubmodule := by
  refine ⟨c.disjoint_conjugate_of_ne A hA hh t hne, ?_⟩
  apply codisjoint_iff.mpr
  have hs := (c.span_eq_sup_of_two_types A hA hh t htypes).symm.trans hspan
  exact congrArg Subrepresentation.toSubmodule hs

/-- The sum of the two literal orbit inclusions intertwines the full actor
restriction with the direct product of the two constituent actions. -/
noncomputable def twoTypeEquiv (t : P) (hne : A ≠ c.conjugate t A)
    (htypes : ∀ s : P, SameModule A (c.conjugate s A) ∨
      SameModule (c.conjugate t A) (c.conjugate s A))
    (hspan : c.span A = ⊤) :
    Representation.Equiv σ (A.toRepresentation.prod (c.conjugate t A).toRepresentation) := by
  let e := Submodule.prodEquivOfIsCompl A.toSubmodule (c.conjugate t A).toSubmodule
    (c.isCompl_of_two_types A hA hh t hne htypes hspan)
  refine (Representation.Equiv.mk e ?_).symm
  intro g
  apply LinearMap.ext
  intro v
  change σ g v.1.val + σ g v.2.val = σ g (v.1.val + v.2.val)
  exact (map_add (σ g) _ _).symm

/-- Coordinates for the actual orbit span inside a possibly larger module.
The equivalence is inverse to adding the original two constituent inclusions. -/
noncomputable def twoTypeSpanEquiv (t : P) (hne : A ≠ c.conjugate t A)
    (htypes : ∀ s : P, SameModule A (c.conjugate s A) ∨
      SameModule (c.conjugate t A) (c.conjugate s A)) :
    Representation.Equiv (c.span A).toRepresentation
      (A.toRepresentation.prod (c.conjugate t A).toRepresentation) := by
  let B := c.conjugate t A
  let f : A.toSubmodule × B.toSubmodule →ₗ[ZMod 2] W :=
    A.toSubmodule.subtype.coprod B.toSubmodule.subtype
  have hs : (c.span A).toSubmodule = A.toSubmodule ⊔ B.toSubmodule :=
    congrArg Subrepresentation.toSubmodule (c.span_eq_sup_of_two_types A hA hh t htypes)
  let g := f.codRestrict (c.span A).toSubmodule (fun v => by
    rw [hs]
    exact Submodule.add_mem_sup v.1.property v.2.property)
  have hi : Function.Injective g := by
    apply (injective_iff_map_eq_zero g).mpr
    intro v hv
    have hz : v.1.val + v.2.val = 0 := congrArg Subtype.val hv
    have he : v.1.val = -v.2.val := eq_neg_of_add_eq_zero_left hz
    have h0 : v.1.val = 0 := (Submodule.disjoint_def.mp
      (c.disjoint_conjugate_of_ne A hA hh t hne))
      v.1.val v.1.property (he ▸ B.toSubmodule.neg_mem v.2.property)
    have h1 : v.2.val = 0 := by simpa only [h0,zero_add] using hz
    exact Prod.ext (Subtype.ext h0) (Subtype.ext h1)
  have hsurj : Function.Surjective g := by
    intro v
    have hv : v.val ∈ A.toSubmodule ⊔ B.toSubmodule := hs ▸ v.property
    obtain ⟨a,ha,b,hb,he⟩ := Submodule.mem_sup.mp hv
    exact ⟨(⟨a,ha⟩,⟨b,hb⟩),Subtype.ext he⟩
  let e := LinearEquiv.ofBijective g ⟨hi,hsurj⟩
  refine (Representation.Equiv.mk e ?_).symm
  intro x
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change σ x v.1.val + σ x v.2.val = σ x (v.1.val + v.2.val)
  exact (map_add (σ x) _ _).symm

/-- A moved homogeneous orbit whose constituents have two specified literal
models is their product, with no assumed multiplicity or direct-sum marking. -/
theorem nonempty_span_equiv_prod_of_two_models
    {V₀ V₁ : Type*} [AddCommGroup V₀] [Module (ZMod 2) V₀]
    [AddCommGroup V₁] [Module (ZMod 2) V₁]
    (τ₀ : Representation (ZMod 2) E V₀) (τ₁ : Representation (ZMod 2) E V₁)
    (e₀ : A.toRepresentation.Equiv τ₀)
    (hmoved : c.span A ≠ A)
    (hmodels : ∀ s : P,
      Nonempty ((c.conjugate s A).toRepresentation.Equiv τ₀) ∨
      Nonempty ((c.conjugate s A).toRepresentation.Equiv τ₁)) :
    Nonempty ((c.span A).toRepresentation.Equiv (τ₀.prod τ₁)) := by
  have hsome : ∃ t : P, A ≠ c.conjugate t A := by
    by_contra! h
    exact hmoved (le_antisymm (iSup_le fun t => (h t).symm.le) (c.le_span A))
  obtain ⟨t,ht⟩ := hsome
  have hnot : ¬ SameModule A (c.conjugate t A) := by
    intro he
    exact ht ((c.one A).symm.trans
      (c.conjugate_eq_of_sameModule A hA hh 1 t (by simpa only [c.one] using he)))
  obtain ⟨e₁⟩ : Nonempty ((c.conjugate t A).toRepresentation.Equiv τ₁) := by
    rcases hmodels t with h | h
    · obtain ⟨a⟩ := h
      let e := e₀.trans a.symm
      exact (hnot ⟨e.toLinearEquiv, fun x v =>
        Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap x v⟩).elim
    · exact h
  have htypes : ∀ s : P, SameModule A (c.conjugate s A) ∨
      SameModule (c.conjugate t A) (c.conjugate s A) := by
    intro s
    rcases hmodels s with h | h
    · obtain ⟨a⟩ := h
      let e := e₀.trans a.symm
      exact Or.inl ⟨e.toLinearEquiv, fun x v =>
        Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap x v⟩
    · obtain ⟨b⟩ := h
      let e := e₁.trans b.symm
      exact Or.inr ⟨e.toLinearEquiv, fun x v =>
        Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap x v⟩
  let e := c.twoTypeSpanEquiv A hA hh t ht htypes
  let p : Representation.Equiv
      (A.toRepresentation.prod (c.conjugate t A).toRepresentation) (τ₀.prod τ₁) :=
    Representation.Equiv.mk (e₀.toLinearEquiv.prodCongr e₁.toLinearEquiv) (by
      intro x
      apply LinearMap.ext
      intro v
      apply Prod.ext
      · exact Representation.IntertwiningMap.isIntertwining _ _ e₀.toIntertwiningMap x v.1
      · exact Representation.IntertwiningMap.isIntertwining _ _ e₁.toIntertwiningMap x v.2)
  exact ⟨e.trans p⟩
end Representation.BinaryOffender.Homogeneous.TypeAction
