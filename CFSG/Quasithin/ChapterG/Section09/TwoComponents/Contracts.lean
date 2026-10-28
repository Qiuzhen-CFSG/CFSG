module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.TensorData

/-!+# The common-field construction obligation in G.9.3

The source's first paragraph on printed p.356 requires a tensor theorem for
two distinct commuting components, acting irreducibly together, whose binary
restrictions are quasiequivalent up to duality. This contract specifies that
theorem independently of the rank estimates and small-module recognition.

Its result includes the constituent embeddings, full scalar endomorphism
rings and an equivariant tensor isomorphism. The contract is only a theorem
type; no inhabitant or source classification is asserted here. In particular
it requires no quadratic-four-group or offender hypothesis.

Source: Aschbacher--Smith, combined manuscript, G.9.3, printed p.356.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents

universe u v

/-- The construction needed before any tensor-degree argument can be used.
This is an unproved obligation, not an extra source hypothesis. -/
def TensorConstructionTheorem : Prop :=
  ∀ {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L L₂ : Subgroup G),
    Function.Injective ρ →
    Theory.GroupTheory.IsComponent G L →
    Theory.GroupTheory.IsComponent G L₂ → L ≠ L₂ →
    Representation.IsIrreducible (ρ.comp (L ⊔ L₂).subtype) →
    (Quasiequivalent (ρ.comp L.subtype) (ρ.comp L₂.subtype) ∨
      Quasiequivalent (ρ.comp L.subtype) (Representation.dual (ρ.comp L₂.subtype))) →
    Nonempty (TensorData ρ L L₂)

end CFSG.Quasithin.ChapterG.Section09.TwoComponents
