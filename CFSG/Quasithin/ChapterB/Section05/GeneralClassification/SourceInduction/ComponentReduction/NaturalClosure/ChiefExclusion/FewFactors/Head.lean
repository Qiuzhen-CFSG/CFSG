module

public import Theory.Representation.SubspaceQuotient
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RingTheory.Jacobson.Radical

/-!
# The canonical head for the small-factor argument

Take the radical of the actual group-algebra module. Every commuting
operator is a module endomorphism, so the radical is invariant under the
second actor. Both groups therefore act on the same literal quotient, and
their quotient actions commute. The pointwise criterion below identifies
triviality on that quotient with displacement into the radical.

These constructions separate two remaining arguments: controlling the
head's multiplicities from the original flag, and detecting a perfect
commuting action on the head. Neither argument is assumed by these definitions.
The actual component application is in `FewFactors.MovedHead`.

Source: Aschbacher–Smith, B.5.9, printed p.108, the centralizer assertion
for c = 2 (1 March 2004 manuscript).
-/

@[expose] public section

open Representation
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure.FewFactors
set_option backward.isDefEq.respectTransparency false

namespace Head
open scoped MonoidAlgebra
variable {F P Q W : Type*} [Field F] [Group P] [Group Q]
  [AddCommGroup W] [Module F W]

/-- The literal intersection of maximal submodules, transported to a subrepresentation. -/
noncomputable def radical (τ : Representation F P W) : Subrepresentation τ :=
  Subrepresentation.ofSubmodule' (Module.jacobson F[P] τ.asModule)

/-- Commutation makes each actor an endomorphism, which preserves the module radical. -/
theorem radical_stable (τ : Representation F P W) (σ : Representation F Q W)
    (hc : ∀ p q, τ p * σ q = σ q * τ p) (q : Q) (w : W)
    (hw : w ∈ radical τ) : σ q w ∈ radical τ := by
  let t : IntertwiningMap τ τ := ⟨σ q, fun p => (hc p q).symm⟩
  let a := IntertwiningMap.equivAlgEnd τ t
  exact Module.le_comap_jacobson a hw

/-- The same subspace, invariant under the commuting actor. -/
noncomputable def actorRadical (τ : Representation F P W) (σ : Representation F Q W)
    (hc : ∀ p q, τ p * σ q = σ q * τ p) : Subrepresentation σ :=
  ⟨(radical τ).toSubmodule, fun q w hw => radical_stable τ σ hc q w hw⟩

/-- The commuting actor on the literal quotient by the first action's radical. -/
noncomputable def action (τ : Representation F P W) (σ : Representation F Q W)
    (hc : ∀ p q, τ p * σ q = σ q * τ p) :
    Representation F Q (W ⧸ (radical τ).toSubmodule) :=
  (actorRadical τ σ hc).quotientRepresentation

/-- Trivial head action means that every displacement lies in the actual radical. -/
theorem action_eq_one_iff (τ : Representation F P W) (σ : Representation F Q W)
    (hc : ∀ p q, τ p * σ q = σ q * τ p) : action τ σ hc = 1 ↔
    ∀ q w, σ q w - w ∈ radical τ := by
  constructor
  · intro h q w
    apply (Submodule.Quotient.mk_eq_zero (radical τ).toSubmodule).mp
    change (radical τ).toSubmodule.mkQ (σ q w - w) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    exact DFunLike.congr_fun (DFunLike.congr_fun h q) ((radical τ).toSubmodule.mkQ w)
  · intro h
    apply MonoidHom.ext
    intro q
    apply LinearMap.ext
    intro w
    induction w using Submodule.Quotient.induction_on with | _ w =>
      exact (Submodule.Quotient.eq (radical τ).toSubmodule).mpr (h q w)
/-- The first group's canonical head representation. -/
noncomputable def representation (τ : Representation F P W) :
    Representation F P (W ⧸ (radical τ).toSubmodule) :=
  (radical τ).quotientRepresentation

/-- The head action uses the original operator on quotient representatives. -/
@[simp] theorem action_mk (τ : Representation F P W) (σ : Representation F Q W)
    (hc : ∀ p q, τ p * σ q = σ q * τ p) (q : Q) (w : W) :
    action τ σ hc q ((radical τ).toSubmodule.mkQ w) =
      (radical τ).toSubmodule.mkQ (σ q w) := rfl

/-- The two literal quotient actions still commute. -/
theorem action_commute (τ : Representation F P W) (σ : Representation F Q W)
    (hc : ∀ p q, τ p * σ q = σ q * τ p) (p : P) (q : Q) :
    representation τ p * action τ σ hc q = action τ σ hc q * representation τ p := by
  ext w
  exact congrArg (radical τ).toSubmodule.mkQ (DFunLike.congr_fun (hc p q) w)
end Head

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure.FewFactors
