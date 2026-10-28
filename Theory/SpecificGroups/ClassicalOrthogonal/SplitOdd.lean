module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Geometry
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Elementary
public import Mathlib.Algebra.IsPrimePow

/-!
# Finite split and odd projective orthogonal models

The carriers below are the scalar quotients of the elementary orthogonal
subgroups of the explicit forms `∑ xᵢ yᵢ` and `∑ xᵢ yᵢ + z²`.
Their generators are the actual Siegel isometries, with preservation and inverse
proved in the imported construction. This is the elementary construction of
Omega, not a definition using the whole special orthogonal group. In particular,
projectivization is the quotient by scalar transformations, with an exact
kernel theorem; no identification with a full center is required.

The geometry certifies the hyperbolic coordinates and nonsingularity in all
characteristics. In characteristic two the odd polarization has a radical line
on which the quadratic form is a nonzero square. Finiteness follows from the
finite coordinate space, then passes to the subgroup and scalar quotient.

The simple parameter ranges retain `PΩ₆⁺(q)` and `PΩ₃(q)` as direct models,
so the usual low-rank aliases require no omissions from the catalogue.
Simplicity and order are not hypotheses of the model construction.

Sources: GLS3, Theorem 2.2.7, Definition 2.2.8 and §2.7
(`refs/KGroup/GLS3/chapter2.tex`); Aschbacher–Smith, §A.2
(`refs/quasithin.pdf`). The construction closure is adapted from Gerald Höhn's
ATLAS; see the attribution and license notices in the imported descendants.
-/

@[expose] public section

namespace ClassicalOrthogonal

/-- The elementary split orthogonal group on `2r` hyperbolic coordinates. -/
abbrev OmegaPlus (r : ℕ) (F : Type*) [Field F] := elementarySubgroup (formD r F)

/-- The elementary odd orthogonal group on `2r+1` coordinates. -/
abbrev OmegaOdd (r : ℕ) (F : Type*) [Field F] := elementarySubgroup (formB r F)

/-- The scalar quotient `PΩ⁺_{2r}(F)`, retaining rank three. -/
abbrev POmegaPlus (r : ℕ) (F : Type*) [Field F] := ProjectiveElementary (formD r F)

/-- The scalar quotient `PΩ_{2r+1}(F)`, retaining rank one and characteristic two. -/
abbrev POmegaOdd (r : ℕ) (F : Type*) [Field F] := ProjectiveElementary (formB r F)

/-- The split projective map kills exactly the scalar transformations.
The positive rank hypothesis is discharged throughout the simple range. -/
theorem projectivePlus_scalar_kernel {r : ℕ} {F : Type*} [Field F]
    (hr : 0 < r) (g : OmegaPlus r F) :
    projectiveElementaryMap (formD r F) g = 1 ↔
      ∃ c : F, ∀ x, g.val.val x = c • x :=
  projectiveElementaryMap_eq_one_iff_scalar (formD r F)
    ⟨e ⟨0, hr⟩ + f ⟨0, hr⟩, formD_e_add_f _⟩ g

/-- The odd projective map kills exactly the scalar transformations,
including when the polar form has a radical. -/
theorem projectiveOdd_scalar_kernel {r : ℕ} {F : Type*} [Field F]
    (g : OmegaOdd r F) :
    projectiveElementaryMap (formB r F) g = 1 ↔
      ∃ c : F, ∀ x, g.val.val x = c • x :=
  projectiveElementaryMap_eq_one_iff_scalar (formB r F) ⟨z, formB_z⟩ g

/-- The full simple split range, including the rank-three linear alias. -/
def PlusParameters (r q : ℕ) : Prop := IsPrimePow q ∧ 3 ≤ r

/-- The full simple odd range, including the rank-one linear alias.
The exclusions are exactly `(1,2)`, `(1,3)` and `(2,2)`. -/
def OddParameters (r q : ℕ) : Prop :=
  IsPrimePow q ∧ 1 ≤ r ∧ (r = 1 → 4 ≤ q) ∧ (r = 2 → q ≠ 2)

variable (r : ℕ) (F : Type*) [Field F] [Finite F]

/-- Finiteness is derived from the explicit quadratic-space carrier. -/
theorem finite_POmegaPlus : Finite (POmegaPlus r F) := inferInstance

/-- Finiteness also holds for the odd carrier in characteristic two. -/
theorem finite_POmegaOdd : Finite (POmegaOdd r F) := inferInstance

end ClassicalOrthogonal

namespace ClassicalGroup

universe u v

/-- Isomorphism with the independent split projective orthogonal carrier. -/
def IsPOmegaPlus (G : Type u) [Group G] (r q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
    Nonempty (G ≃* ClassicalOrthogonal.POmegaPlus r F)

/-- Isomorphism with the independent odd projective orthogonal carrier. -/
def IsPOmegaOdd (G : Type u) [Group G] (r q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
    Nonempty (G ≃* ClassicalOrthogonal.POmegaOdd r F)

variable {G : Type u} {H : Type v} [Group G] [Group H] {r q : ℕ}

theorem IsPOmegaPlus.of_mulEquiv (h : IsPOmegaPlus G r q) (e : H ≃* G) :
    IsPOmegaPlus H r q := by
  rcases h with ⟨F, hF, hfin, hq, ⟨f⟩⟩
  exact ⟨F, hF, hfin, hq, ⟨e.trans f⟩⟩

theorem IsPOmegaOdd.of_mulEquiv (h : IsPOmegaOdd G r q) (e : H ≃* G) :
    IsPOmegaOdd H r q := by
  rcases h with ⟨F, hF, hfin, hq, ⟨f⟩⟩
  exact ⟨F, hF, hfin, hq, ⟨e.trans f⟩⟩

theorem IsPOmegaPlus.finite (h : IsPOmegaPlus G r q) : Finite G := by
  rcases h with ⟨F, hF, hfin, _, ⟨e⟩⟩
  exact Finite.of_injective e e.injective

theorem IsPOmegaOdd.finite (h : IsPOmegaOdd G r q) : Finite G := by
  rcases h with ⟨F, hF, hfin, _, ⟨e⟩⟩
  exact Finite.of_injective e e.injective

/-- Every finite coefficient field supplies its split model directly. -/
theorem isPOmegaPlus_model (r : ℕ) (F : Type) [Field F] [Finite F] :
    IsPOmegaPlus (ClassicalOrthogonal.POmegaPlus r F) r (Nat.card F) :=
  ⟨F, inferInstance, inferInstance, rfl, ⟨MulEquiv.refl _⟩⟩

/-- Every finite coefficient field supplies its odd model directly. -/
theorem isPOmegaOdd_model (r : ℕ) (F : Type) [Field F] [Finite F] :
    IsPOmegaOdd (ClassicalOrthogonal.POmegaOdd r F) r (Nat.card F) :=
  ⟨F, inferInstance, inferInstance, rfl, ⟨MulEquiv.refl _⟩⟩

end ClassicalGroup
