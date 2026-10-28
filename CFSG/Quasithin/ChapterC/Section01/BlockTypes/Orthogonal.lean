module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.Representation.OrthogonalNatural

/-!
# Orthogonal natural blocks (C.1.30)

An `Ω_m^ε(2^n)` block identifies both the actual quotient by `O₂` and
literal conjugation on `Ũ` with Omega and its natural quadratic module.
Here `ε` is plus or minus, `m = 2r` is the dimension (not the Lie rank),
and `n ≥ 1` is the field exponent. There are no simple-catalogue exclusions:
in particular dimension four and exponent one are retained. Dimension two
is the orthogonal torus convention, also retained since C.1.30 imposes no
lower dimension bound; in that dimension the split model uses the
orthogonal commutator subgroup rather than the Siegel-generated subgroup.

The split form is the sum of `r` hyperbolic planes. The minus form is the
sum of `r-1` hyperbolic planes and the constructed anisotropic plane.
The characteristic-two scalar-kernel theorem identifies Omega with its
projective scalar quotient; it does not identify Omega with the full
orthogonal group. The action preserves the quadratic form, not just its polar.

Sources: Aschbacher--Smith, Definition C.1.30, printed p.135, and §H.1,
printed p.378 (signs, dimension four, and the exponent-one minus case);
GLS3 §2.7, printed pp.87–88 (even-dimensional and torus conventions).
-/

@[expose] public noncomputable section

namespace CFSG.Quasithin.ChapterC

open Theory.GroupTheory ClassicalOrthogonal

universe u

variable {L : Type*} [Group L]

/-- For quadratic-isometry subgroups the model action can always be chosen
as the concrete natural action. No arbitrary representation remains. -/
theorem IsLinearBlockModel.orthogonal_model {F V : Type u} [Field F]
    [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
    {H : Subgroup (Theory.AlgebraicGroup.quadraticIsometrySubgroup Q)}
    (h : IsLinearBlockModel L (subgroupNatural H)) :
    Nonempty (BlockModuleModel L (subgroupNaturalAction H)) := by
  obtain ⟨rho, hm, he⟩ := h
  have hr : rho = subgroupNaturalAction H := by
    ext g v
    exact he g v
  rwa [hr] at hm

/-- Conversely a concrete equivariant natural model supplies the linear interface. -/
theorem isLinearBlockModel_of_orthogonal_model {F V : Type u} [Field F]
    [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
    {H : Subgroup (Theory.AlgebraicGroup.quadraticIsometrySubgroup Q)}
    (h : Nonempty (BlockModuleModel L (subgroupNaturalAction H))) :
    IsLinearBlockModel L (subgroupNatural H) :=
  ⟨subgroupNaturalAction H, h, fun _ _ => rfl⟩

/-- Literal conjugation, after identifying the module, is the specified
linear isometry in the actual quotient-isomorphism image. -/
theorem BlockModuleModel.orthogonal_intertwining {F V : Type u} [Field F]
    [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
    {H : Subgroup (Theory.AlgebraicGroup.quadraticIsometrySubgroup Q)}
    (model : BlockModuleModel L (subgroupNaturalAction H)) (l : L) (v : blockU L) :
    Multiplicative.toAdd
      (model.moduleIso (QuotientGroup.mk' (blockFixed L) (blockConjugate L l v))) =
    (model.quotientIso (QuotientGroup.mk' (pCore 2 L) l)).val.val
      (Multiplicative.toAdd (model.moduleIso (QuotientGroup.mk' (blockFixed L) v))) :=
  congrArg Multiplicative.toAdd (model.intertwining l v)

/-- The quadratic value transported to Ũ is invariant under actual conjugation. -/
theorem BlockModuleModel.orthogonal_quadratic_invariant {F V : Type u} [Field F]
    [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
    {H : Subgroup (Theory.AlgebraicGroup.quadraticIsometrySubgroup Q)}
    (model : BlockModuleModel L (subgroupNaturalAction H)) (l : L) (v : blockU L) :
    Q (Multiplicative.toAdd
      (model.moduleIso (QuotientGroup.mk' (blockFixed L) (blockConjugate L l v)))) =
    Q (Multiplicative.toAdd (model.moduleIso (QuotientGroup.mk' (blockFixed L) v))) := by
  rw [model.orthogonal_intertwining]
  exact subgroupNatural_preserves H _ _

variable (L)

/-- Plus-type orthogonal natural block, with `m` the dimension over `F_{2^n}`. -/
def IsOmegaPlusEvenBlock (m n : ℕ) : Prop :=
  1 ≤ n ∧ IsShort L ∧ ∃ r, 1 ≤ r ∧ m = 2 * r ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      IsLinearBlockModel L (subgroupNatural (omegaPlusWithTorus r F))

/-- Minus-type orthogonal natural block, including the four-dimensional
`Ω₄⁻(2)` case and the dimension-two anisotropic torus convention. -/
def IsOmegaMinusEvenBlock (m n : ℕ) : Prop :=
  1 ≤ n ∧ IsShort L ∧ ∃ r, 1 ≤ r ∧ m = 2 * r ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      IsLinearBlockModel L (subgroupNatural
        (Minus.Omega F (Minus.Space F (r - 1)) (Minus.quadraticForm F r)))

/-- The signs in C.1.30 and H.1 are `+1` and `-1`; odd dimension is not
an additional signed case. -/
inductive OrthogonalBlockSign where
  | plus
  | minus
  deriving DecidableEq

/-- The signed intrinsic orthogonal block type of C.1.30. -/
def IsOmegaEvenBlock (sign : OrthogonalBlockSign) (m n : ℕ) : Prop :=
  match sign with
  | .plus => IsOmegaPlusEvenBlock L m n
  | .minus => IsOmegaMinusEvenBlock L m n

variable {L} {m n : ℕ}

theorem IsOmegaPlusEvenBlock.short (h : IsOmegaPlusEvenBlock L m n) : IsShort L := h.2.1

theorem IsOmegaMinusEvenBlock.short (h : IsOmegaMinusEvenBlock L m n) : IsShort L := h.2.1

/-- The source parameters are dimension, sign, and positive field exponent. -/
theorem IsOmegaPlusEvenBlock.parameters (h : IsOmegaPlusEvenBlock L m n) :
    2 ≤ m ∧ Even m ∧ 1 ≤ n := by
  obtain ⟨hn, _, r, hr, rfl, _⟩ := h
  exact ⟨by omega, ⟨r, by omega⟩, hn⟩

theorem IsOmegaMinusEvenBlock.parameters (h : IsOmegaMinusEvenBlock L m n) :
    2 ≤ m ∧ Even m ∧ 1 ≤ n := by
  obtain ⟨hn, _, r, hr, rfl, _⟩ := h
  exact ⟨by omega, ⟨r, by omega⟩, hn⟩

/-- Binary module size uses the dimension `m`, not the half-dimension `r`. -/
theorem IsOmegaPlusEvenBlock.module_card (h : IsOmegaPlusEvenBlock L m n) :
    Nat.card (BlockModule L) = 2 ^ (n * m) := by
  obtain ⟨_, _, r, _, rfl, F, _, _, hF, hm⟩ := h
  rw [hm.module_card, Module.natCard_eq_pow_finrank (K := F), vectorD_finrank, hF,
    ← pow_mul]

theorem IsOmegaMinusEvenBlock.module_card (h : IsOmegaMinusEvenBlock L m n) :
    Nat.card (BlockModule L) = 2 ^ (n * m) := by
  obtain ⟨_, _, r, hr, rfl, F, _, _, hF, hm⟩ := h
  rw [hm.module_card, Module.natCard_eq_pow_finrank (K := F), Minus.space_finrank, hF]
  rw [show 2 * (r - 1) + 2 = 2 * r by omega, ← pow_mul]

/-- A concrete natural model, including its quotient equivalence and its
literal conjugation intertwining formula. -/
theorem IsOmegaPlusEvenBlock.natural_model (h : IsOmegaPlusEvenBlock L m n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (BlockModuleModel L (subgroupNaturalAction (omegaPlusWithTorus (m / 2) F))) := by
  obtain ⟨_, _, r, _, rfl, F, _, _, hF, hm⟩ := h
  refine ⟨F, inferInstance, inferInstance, hF, ?_⟩
  rw [show 2 * r / 2 = r by omega]
  exact hm.orthogonal_model

theorem IsOmegaMinusEvenBlock.natural_model (h : IsOmegaMinusEvenBlock L m n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (BlockModuleModel L (subgroupNaturalAction
        (Minus.Omega F (Minus.Space F (m / 2 - 1)) (Minus.quadraticForm F (m / 2))))) := by
  obtain ⟨_, _, r, _, rfl, F, _, _, hF, hm⟩ := h
  refine ⟨F, inferInstance, inferInstance, hF, ?_⟩
  rw [show 2 * r / 2 = r by omega]
  exact hm.orthogonal_model

/-- The actual core quotient is Omega, with its action on the same field. -/
theorem IsOmegaPlusEvenBlock.quotient_iso (h : IsOmegaPlusEvenBlock L m n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* omegaPlusWithTorus (m / 2) F) := by
  obtain ⟨F, _, _, hF, ⟨model⟩⟩ := h.natural_model
  exact ⟨F, inferInstance, inferInstance, hF, ⟨model.quotientIso⟩⟩

theorem IsOmegaMinusEvenBlock.quotient_iso (h : IsOmegaMinusEvenBlock L m n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty ((L ⧸ pCore 2 L) ≃*
        Minus.Omega F (Minus.Space F (m / 2 - 1)) (Minus.quadraticForm F (m / 2))) := by
  obtain ⟨F, _, _, hF, ⟨model⟩⟩ := h.natural_model
  exact ⟨F, inferInstance, inferInstance, hF, ⟨model.quotientIso⟩⟩

/-- Above the torus dimension this also identifies the existing split
projective carrier, by the proved characteristic-two scalar-kernel bridge. -/
theorem IsOmegaPlusEvenBlock.projective_quotient (h : IsOmegaPlusEvenBlock L m n)
    (hm : 4 ≤ m) : ClassicalGroup.IsPOmegaPlus (L ⧸ pCore 2 L) (m / 2) (2 ^ n) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h.quotient_iso
  have : CharP F 2 := charTwo_of_card hF
  rw [omegaPlusWithTorus_eq (m / 2) (by omega)] at e
  exact ⟨F, inferInstance, inferInstance, hF,
    ⟨e.trans (elementaryProjectiveEquiv (formD (m / 2) F))⟩⟩

theorem IsOmegaMinusEvenBlock.projective_quotient (h : IsOmegaMinusEvenBlock L m n) :
    ClassicalGroup.IsPOmegaMinus (L ⧸ pCore 2 L) (m / 2) (2 ^ n) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h.quotient_iso
  have : CharP F 2 := charTwo_of_card hF
  exact ⟨F, inferInstance, inferInstance, hF, ⟨e.trans (Minus.minusProjectiveEquiv (m / 2))⟩⟩

/-- Construct a split block directly from the owning Omega model in
all dimensions at least four, without any simplicity-range condition. -/
theorem IsOmegaPlusEvenBlock.of_model {r : ℕ} (hr : 2 ≤ r) (hn : 1 ≤ n)
    (hshort : IsShort L) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n)
    (hmodel : Nonempty (BlockModuleModel L
      (subgroupNaturalAction (elementarySubgroup (formD r F))))) :
    IsOmegaPlusEvenBlock L (2 * r) n := by
  refine ⟨hn, hshort, r, by omega, rfl, F, inferInstance, inferInstance, hF, ?_⟩
  rw [omegaPlusWithTorus_eq r hr]
  exact isLinearBlockModel_of_orthogonal_model hmodel

/-- Construct a minus block directly from its concrete equivariant natural
model. Rank two and exponent one are permitted. -/
theorem IsOmegaMinusEvenBlock.of_model {r : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n)
    (hshort : IsShort L) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n)
    (hmodel : Nonempty (BlockModuleModel L (subgroupNaturalAction
      (Minus.Omega F (Minus.Space F (r - 1)) (Minus.quadraticForm F r))))) :
    IsOmegaMinusEvenBlock L (2 * r) n :=
  ⟨hn, hshort, r, hr, rfl, F, inferInstance, inferInstance, hF,
    isLinearBlockModel_of_orthogonal_model hmodel⟩

/-- In dimension at least four the natural model is literally the existing
split Omega action, including its concrete quotient equivalence. -/
theorem IsOmegaPlusEvenBlock.split_natural_model (h : IsOmegaPlusEvenBlock L m n)
    (hm : 4 ≤ m) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (BlockModuleModel L
        (subgroupNaturalAction (elementarySubgroup (formD (m / 2) F)))) := by
  obtain ⟨F, _, _, hF, hmodel⟩ := h.natural_model
  rw [omegaPlusWithTorus_eq (m / 2) (by omega)] at hmodel
  exact ⟨F, inferInstance, inferInstance, hF, hmodel⟩

theorem IsOmegaEvenBlock.short {sign : OrthogonalBlockSign}
    (h : IsOmegaEvenBlock L sign m n) : IsShort L := by
  cases sign with
  | plus => exact IsOmegaPlusEvenBlock.short h
  | minus => exact IsOmegaMinusEvenBlock.short h

theorem IsOmegaEvenBlock.parameters {sign : OrthogonalBlockSign}
    (h : IsOmegaEvenBlock L sign m n) : 2 ≤ m ∧ Even m ∧ 1 ≤ n := by
  cases sign with
  | plus => exact IsOmegaPlusEvenBlock.parameters h
  | minus => exact IsOmegaMinusEvenBlock.parameters h

theorem IsOmegaEvenBlock.module_card {sign : OrthogonalBlockSign}
    (h : IsOmegaEvenBlock L sign m n) : Nat.card (BlockModule L) = 2 ^ (n * m) := by
  cases sign with
  | plus => exact IsOmegaPlusEvenBlock.module_card h
  | minus => exact IsOmegaMinusEvenBlock.module_card h

end CFSG.Quasithin.ChapterC
