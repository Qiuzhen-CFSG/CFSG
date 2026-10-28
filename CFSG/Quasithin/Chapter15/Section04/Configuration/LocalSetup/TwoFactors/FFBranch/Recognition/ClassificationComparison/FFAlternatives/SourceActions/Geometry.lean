module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.NonQuasisimple
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.QuasisimpleModels
public import Theory.ElementaryAbelian.Extraspecial
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Action geometry retained by the source contracts

All occurrences of natural, repeated, and natural-plus-dual modules refer to
actual intertwining linear equivalences. In particular the two summands of a
natural-plus-dual module use one group identification. A full axis group means
the whole pointwise stabilizer of a field hyperplane, not an arbitrary subgroup
of transvections. The four-dimensional contract includes every assertion of
B.4.8(3). The last record expresses B.5.1(6) as an extension, without imposing
a split extension.

Source: Aschbacher–Smith, B.4.8(3), p.91, B.5.1, pp.99–103.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u v w z

/-- The natural module together with its contragredient, under the same actor. -/
noncomputable def naturalPlusDual (d : ℕ) :=
  (linearNatural BinaryField.two d).prod (linearNatural BinaryField.two d).dual

variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

/-- One intertwiner controls both summands, excluding incompatible twists. -/
def IsNaturalPlusDual (d : ℕ) : Prop :=
  Nonempty (ActionEquiv ρ (naturalPlusDual d))

/-- Homogeneity: a nonempty finite sum of copies of one irreducible module,
with the original actor on every summand. -/
def IsHomogeneousAction : Prop :=
  ∃ (r : ℕ) (_ : 0 < r) (W : Subrepresentation ρ), IsIrreducible W.toRepresentation ∧
    ∃ f : V ≃ₗ[ZMod 2] (Fin r → W.toSubmodule),
      ∀ g v, f (ρ g v) = repeated W.toRepresentation r g (f v)

/-- All transvections with a common axis, including the identity. This is
an equality with the entire pointwise hyperplane stabilizer in SL. -/
def IsFullAxisGroup (F : BinaryField) (d : ℕ)
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin d) F.Carrier)) : Prop :=
  ∃ P : Submodule F.Carrier (Fin d → F.Carrier),
    Module.finrank F.Carrier ((Fin d → F.Carrier) ⧸ P) = 1 ∧
    ∀ g, g ∈ A ↔ ∀ v ∈ P, specialLinearNatural d g v = v

/-- The dual description: all transvections with a common center. -/
def IsFullCenterGroup (F : BinaryField) (d : ℕ)
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin d) F.Carrier)) : Prop :=
  ∃ P : Submodule F.Carrier (Fin d → F.Carrier),
    Module.finrank F.Carrier P = 1 ∧
    ∀ g, g ∈ A ↔ ∀ v, specialLinearNatural d g v - v ∈ P

/-- The actual submodule [V,L], and its actual quotient by C_[V,L](L).
The two stability witnesses retain the action of the whole ambient group. -/
structure MovedSection (L : Subgroup D) where
  space : Subrepresentation ρ
  space_eq : space.toSubmodule = moved ρ L
  central : Subrepresentation space.toRepresentation
  central_eq : central.toSubmodule = fixedSpace space.toRepresentation L

/-- The whole ambient group acts on the specified quotient. -/
noncomputable abbrev MovedSection.action {L : Subgroup D} (s : MovedSection ρ L) :=
  s.central.quotientRepresentation

/-- A natural module for an alternating group is the restricted deleted
permutation action, with an actual identification of the actor. -/
def alternatingNatural (n : ℕ) :=
  (BinaryPermutation.naturalRepresentation (Fin n)).comp (alternatingGroup (Fin n)).subtype

def IsAlternatingNatural (n : ℕ) : Prop := Nonempty (ActionEquiv ρ (alternatingNatural n))

/-- B.4.8(3), including the full offender family, q, and involution assertions.
The same natural identification is used in the offender statement. -/
structure FourDimensionalSource where
  dimension : Module.finrank (ZMod 2) V = 4
  indecomposable : IsIndecomposable ρ
  space : Subrepresentation ρ
  space_eq : space.toSubmodule = moved ρ ⊤
  natural : ActionEquiv space.toRepresentation (linearNatural BinaryField.two 3)
  offenders : ∀ A, IsBestOffender ρ A ↔
    IsFullAxisGroup BinaryField.two 3 (A.map natural.groupEquiv.toMonoidHom)
  ratio : quadraticRatio ρ = 1
  involutions : ∀ a : D, orderOf a = 2 →
    moved ρ (zpowers a) = fixedSpace ρ (zpowers a) ∧
    Module.finrank (ZMod 2) (fixedSpace ρ (zpowers a)) = 2 ∧
    fixedSpace ρ (zpowers a) ≤ space.toSubmodule

/-- Forget only the newly retained B.4.8(3) conclusions. -/
theorem FourDimensionalSource.toBasic (h : FourDimensionalSource ρ) :
    IsFourDimensionalExtension ρ := by
  exact ⟨h.dimension, h.indecomposable, h.space, h.space_eq, ⟨h.natural⟩⟩

/-- A marked restriction uses the same group identification as the full action.
This expresses which subgroup of a model is the actual L inside the actual H. -/
structure MarkedActionEquiv (H L : Subgroup D)
    {E : Type w} [Group E] {W : Type z} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) E W) (M : Subgroup E) where
  action : ActionEquiv (ρ.comp H.subtype) σ
  contained : L ≤ H
  subgroupEquiv : L ≃* M
  compatible : ∀ l : L,
    action.groupEquiv ⟨l, contained l.property⟩ = (subgroupEquiv l : E)

/-- A marked full subgroup gives the actual L-to-model isomorphism. -/
noncomputable def MarkedActionEquiv.fullEquiv {H L : Subgroup D}
    {E : Type w} [Group E] {W : Type z} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) E W} (e : MarkedActionEquiv ρ H L σ ⊤) : L ≃* E :=
  e.subgroupEquiv.trans Subgroup.topEquiv

/-- The centralizer extension in B.5.1(6). Slash notation specifies its
normal extraspecial two-core and actual projective quotient. -/
structure SylowFixedCentralizer (L : Subgroup D) (d : ℕ) (T : Sylow 2 D) where
  extraspecial : IsExtraspecial 2 (pCore 2 (subspaceKernel ρ (fixedSpace ρ T) L))
  core_order : Nat.card (pCore 2 (subspaceKernel ρ (fixedSpace ρ T) L)) =
    2 ^ (1 + 2 * (d - 2))
  quotientEquiv :
    ((subspaceKernel ρ (fixedSpace ρ T) L) ⧸
      pCore 2 (subspaceKernel ρ (fixedSpace ρ T) L)) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin (d - 2)) (ZMod 2)
  no_offenders : ∀ A, IsBestOffender ρ A →
    ¬ A ≤ (pCore 2 (subspaceKernel ρ (fixedSpace ρ T) ⊤)).map
      (subspaceKernel ρ (fixedSpace ρ T) ⊤).subtype

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
