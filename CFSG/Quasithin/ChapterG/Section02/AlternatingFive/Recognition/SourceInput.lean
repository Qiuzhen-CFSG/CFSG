module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Projective
public import Mathlib.Algebra.Algebra.ZMod

/-!
# The earlier G.1.3 input for the upper A₅ layer

This interface quantifies over arbitrary finite binary SL₂(F)-modules
and actual projective maps. It retains every equivariance, root-action,
disjointness and spanning hypothesis of G.1.3. Its conclusion is an
actual equivariant binary linear decomposition, including multiplicity
zero. It says nothing about the particular G.2.4 quotient.

Only G.1.3 is retained as an earlier-source premise, discharged by the
G.1/G.2 source owners. The fixed-space conclusion of G.1.5(2) is not an
additional assumption of this interface; the G.2.4 assembly must prove it.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.1.1 and G.1.3, printed p.327.
-/

@[expose] public section
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition
universe uF uM

abbrev ProjectivePoint (F : Type uF) [Field F] :=
  LinearThree.Recognition.Projective.Point F (Fin 2 → F)

abbrev RootGroup (F : Type uF) [Field F] (A : Submodule F (Fin 2 → F)) :
    Subgroup SL(2, F) :=
  LinearThree.Recognition.Projective.rootGroup (Representation.specialLinearNatural 2) A A

abbrev ProjectiveCriterion {F : Type uF} [Field F]
    {M : Type uM} [AddCommGroup M] [Module (ZMod 2) M]
    (σ : Representation (ZMod 2) SL(2, F) M)
    (φ : ProjectivePoint F → Submodule (ZMod 2) M) :=
  LinearThree.Recognition.Projective.Criterion (Representation.specialLinearNatural 2) σ φ

/-- The permitted universal earlier-source implication, without an assumed
fixed-space theorem or any occurrence of the upper quotient. -/
def RecognitionInput (F : Type uF) [Field F] [Finite F] [CharP F 2] : Prop :=
  letI := ZMod.algebra F 2
  ∀ (M : Type uM) [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (σ : Representation (ZMod 2) SL(2, F) M)
    (φ : ProjectivePoint F → Submodule (ZMod 2) M), ProjectiveCriterion σ φ →
      ∃ (s : ℕ) (e : M ≃ₗ[ZMod 2] (Fin s → Fin 2 → F)),
        ∀ a v j, e (σ a v) j = Matrix.mulVec a.val (e v j)

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition
