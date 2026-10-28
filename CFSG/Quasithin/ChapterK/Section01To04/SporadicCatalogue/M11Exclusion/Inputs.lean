module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.Source
public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.AugmentationModel

/-!
# Independent inputs to the bounded M11 exclusion

The representation input concerns every faithful irreducible binary M11 module
of degree at most twelve, with no ratio hypothesis. The geometry input concerns
the actual eleven-point module, marked through its equivalent M12 point heart,
inside any faithful ambient action normalizing it. It asks only for the fixed
codimension of a rank-two elementary subgroup contained in that component.
The source actor reduction supplies this containment, including for outer actions.

These are obligations, not a representation catalogue or a fixed-space theorem.
The source assembly keeps their proofs, and the separate trivial-cover input,
explicit until their producers have been completed.
Source: Aschbacher--Smith K.4, printed p.457, citing GM02 Theorem 6.6 and Table 6.7.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.M11Exclusion
open Theory.GroupTheory Subgroup Representation.BinaryOffender
open _root_.Sporadic.Mathieu
open Representation.MathieuSmall.M12Recognition
universe u v

/-- The low-degree recognition problem, independent of cubic actors and covers. -/
def SmallDegreeRecognition : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (σ : Representation (ZMod 2) M11 V),
    Function.Injective σ → σ.IsIrreducible → Module.finrank (ZMod 2) V ≤ 12 →
    Nonempty (σ.Equiv pointRepresentation)

/-- The marked point module has no codimension-four rank-two actor, even in a
larger faithful group normalizing the component. The actor lies in the component;
no small-ratio assumption is made. -/
def RankTwoPointGeometry : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
    (e : L ≃* M11), Function.Injective ρ →
    Nonempty (Representation.Equiv (ρ.comp L.subtype)
      (pointRepresentation.comp e.toMonoidHom)) →
    ∀ A : Subgroup G, IsElementaryTwo A → rank A = 2 → A ≤ L → 5 ≤ fixedCodim ρ A

end CFSG.Quasithin.ChapterK.SporadicCatalogue.M11Exclusion
