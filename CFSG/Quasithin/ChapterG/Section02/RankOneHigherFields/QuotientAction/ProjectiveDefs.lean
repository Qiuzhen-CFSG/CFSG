module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Projective
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The rank-one instance of the genuine projective recognition criterion

The point, root and criterion definitions are the dimension-independent
definitions already used for G.2.5. Here they are specialized to the literal
SL₂(F) natural plane. `RecognitionImplication` quantifies over all finite
binary modules and all projective maps satisfying every G.1.3 clause. Its
conclusion retains a binary linear equivariant decomposition and the G.1.5(2)
fixed-space equality. Multiplicity zero is allowed.

This is an earlier-source input, not a proof of recognition. Its discharge
belongs to G.1 and the G.2 assembly owner. In particular it says nothing
about S/S₂ until an actual projective map has been constructed and checked.

Source: Aschbacher–Smith, G.1.1, G.1.3 and G.1.5(2–3),
printed pp.327–328, PDF pp.338–339.
-/

@[expose] public section
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.QuotientAction.Projective
universe uF uM

variable (F : Type uF) [Field F]

/-- Actual one-dimensional F-subspaces of the specified natural plane. -/
abbrev Point := LinearThree.Recognition.Projective.Point F (Fin 2 → F)

/-- Transvections with center and axis the given line, including the identity. -/
abbrev rootGroup (A : Submodule F (Fin 2 → F)) : Subgroup SL(2, F) :=
  LinearThree.Recognition.Projective.rootGroup (Representation.specialLinearNatural 2) A A

variable {F}

/-- All source hypotheses, including every incident root/axis pair. -/
abbrev Criterion {M : Type uM} [AddCommGroup M] [Module (ZMod 2) M]
    (σ : Representation (ZMod 2) SL(2, F) M)
    (φ : Point F → Submodule (ZMod 2) M) :=
  LinearThree.Recognition.Projective.Criterion (Representation.specialLinearNatural 2) σ φ

/-- The specified binary module really is s copies of the natural plane,
with its actual action. -/
def NaturalCopies [CharP F 2] {M : Type uM} [AddCommGroup M] [Module (ZMod 2) M]
    (σ : Representation (ZMod 2) SL(2, F) M) (s : ℕ) : Prop :=
  letI := ZMod.algebra F 2
  ∃ e : M ≃ₗ[ZMod 2] (Fin s → Fin 2 → F),
    ∀ a v i, e (σ a v) i = Matrix.mulVec a.val (e v i)

/-- The universally quantified G.1.3/G.1.5 implication permitted as an
earlier-source premise. There is no occurrence of any G.2 quotient here. -/
def RecognitionImplication (F : Type uF) [Field F] [Finite F] [CharP F 2] : Prop :=
  ∀ (M : Type uM) [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (σ : Representation (ZMod 2) SL(2, F) M)
    (φ : Point F → Submodule (ZMod 2) M), Criterion σ φ →
      (∃ s : ℕ, NaturalCopies σ s) ∧
      ∀ (A : Point F) (v : M), v ∈ φ A ↔ ∀ a ∈ rootGroup F A.val, σ a v = v

end CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.QuotientAction.Projective
