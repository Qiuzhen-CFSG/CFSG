module

public import Theory.Representation.SpecialLinearNatural
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Field.ZMod

/-!
# The universal projective recognition input for the two G.2.5 layers

The point set consists of actual one-dimensional F-subspaces. A root
has image of g−1 in its center and fixes its axis pointwise. The criterion
records equivariance, both root conditions, disjointness and spanning,
exactly as in G.1.3. Its conclusion is a genuine equivariant binary linear
isomorphism to finitely many copies of the specified natural action.

`RecognitionImplication` is the universally quantified, three-dimensional
instance of the earlier G.1.3 theorem, retained as an explicit input. It
is not proved here. In particular it asserts nothing about the marked
G.2.5 quotients until their point maps and every criterion clause have
been constructed. Dual applications must also construct an actual natural
marking of the dual action through the contragredient SL₃ automorphism.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.1.1, G.1.3–4, printed pp.327–328, PDF pp.338–339.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Projective
universe uF uK uV uM

variable {F : Type uF} [Field F] {K : Type uK} [Group K]
  {V : Type uV} [AddCommGroup V] [Module F V]

/-- Projective F-points, including their dimension proof. -/
def Point (F : Type uF) [Field F] (V : Type uV) [AddCommGroup V] [Module F V] :=
  {A : Submodule F V // Module.finrank F A = 1}

/-- The root subgroup with center A and axis B, described by its actual
linear action. The incident-point/hyperplane restrictions are supplied
when applying the recognition criterion. -/
def rootGroup (γ : Representation F K V) (A B : Submodule F V) : Subgroup K where
  carrier := {g | (∀ v, γ g v - v ∈ A) ∧ (∀ v ∈ B, γ g v = v)}
  one_mem' := by simp
  mul_mem' := by
    rintro g h ⟨hgA, hgB⟩ ⟨hhA, hhB⟩
    constructor
    · intro v
      have he : γ (g * h) v - v = (γ g (γ h v) - γ h v) + (γ h v - v) := by
        simp only [map_mul, Module.End.mul_apply]
        abel
      rw [he]
      exact A.add_mem (hgA (γ h v)) (hhA v)
    · intro v hv
      simp only [map_mul, Module.End.mul_apply, hhB v hv, hgB v hv]
  inv_mem' := by
    rintro g ⟨hgA, hgB⟩
    constructor
    · intro v
      have h := A.neg_mem (hgA (γ g⁻¹ v))
      simpa only [γ.self_inv_apply, neg_sub] using h
    · intro v hv
      exact (γ.inv_apply_eq_iff).mpr (hgB v hv).symm

/-- All clauses of the genuine source criterion on the supplied action.
The target subspaces may be zero, retaining multiplicity zero. -/
structure Criterion (γ : Representation F K V)
    {M : Type uM} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) K M)
    (φ : Point F V → Submodule (ZMod 2) M) : Prop where
  equivariant : ∀ g (A B : Point F V), B.val = A.val.map (γ g) →
    φ B = (φ A).map (ρ g)
  root_moved : ∀ (A : Point F V) (B : Submodule F V),
    Module.finrank F B + 1 = Module.finrank F V → A.val ≤ B →
    ∀ g ∈ rootGroup γ A.val B, ∀ v : M, ρ g v - v ∈ φ A
  root_fixed : ∀ (A : Point F V) (B : Submodule F V),
    Module.finrank F B + 1 = Module.finrank F V → A.val ≤ B →
    ∀ (D : Point F V), D.val ≤ B → ∀ g ∈ rootGroup γ A.val B,
      ∀ v ∈ φ D, ρ g v = v
  disjoint : ∀ A B : Point F V, A ≠ B → Disjoint (φ A) (φ B)
  spanning : (⨆ A : Point F V, φ A) = ⊤

/-- An actual identification of the given action with SL₃(F) on its
natural vector space, not a group-family tag. -/
structure NaturalMarking (γ : Representation F K V) where
  groupEquiv : K ≃* Matrix.SpecialLinearGroup (Fin 3) F
  coordinates : V ≃ₗ[F] (Fin 3 → F)
  equivariant : ∀ g v,
    coordinates (γ g v) = Representation.specialLinearNatural 3 (groupEquiv g) (coordinates v)

/-- A binary linear decomposition into r copies, with its actual action. -/
def Homogeneous [Module (ZMod 2) V] (γ : Representation F K V)
    {M : Type uM} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) K M) (r : ℕ) : Prop :=
  ∃ e : M ≃ₗ[ZMod 2] (Fin r → V), ∀ g v i, e (ρ g v) i = γ g (e v i)

/-- The genuine earlier recognition implication, universally quantified
in the actor, natural realization, binary module and projective-point map.
The source owner `qt-g-01` must discharge this premise. -/
def RecognitionImplication (F : Type uF) [Field F] [Finite F] [CharP F 2] : Prop :=
  ∀ (K : Type uK) [Group K]
    (V : Type uV) [AddCommGroup V] [Module F V] [Module (ZMod 2) V]
    (γ : Representation F K V), NaturalMarking γ →
    ∀ (M : Type uM) [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
      (ρ : Representation (ZMod 2) K M) (φ : Point F V → Submodule (ZMod 2) M),
      Criterion γ ρ φ → ∃ r : ℕ, Homogeneous γ ρ r

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Projective
