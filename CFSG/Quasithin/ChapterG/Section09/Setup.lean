module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.ElementaryAbelian.Basic
public import Mathlib.RepresentationTheory.Irreducible

/-!
# The hypotheses of G.9

Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, G.9.1, G.9.3 and G.9.4, printed pp.351--354.

The actor is an actual elementary abelian subgroup of order `2^m` and the
module is faithful. A quotient presentation includes a finite SQTK cover
and a surjective homomorphism. Equivalence of actions includes both a group
isomorphism and an intertwining linear isomorphism. No classification
conclusion, component-lifting theorem or Fitting-preimage condition is
included in these hypotheses.

The class `K` is explicit to permit independent structural arguments. The
source classification must use the full known-simple class. Nontriviality
of the actor is not included in G.9.1 as printed; the rank-zero issue for
G.9.4 is kept separate.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section09

universe u v w

variable {G : Type u} [Group G] {V : Type v}
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Hypothesis G.9.1, with the order of the elementary abelian actor explicit. -/
structure Setup [Finite G] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G) (m : ℕ) : Prop where
  faithful : Function.Injective ρ
  elementary : IsElementaryAbelian 2 A
  card_actor : Nat.card A = 2 ^ m
  degree_le : Module.finrank (ZMod 2) V ≤ 2 * (m + 1)

/-- A finite SQTK group surjecting onto the group under study. -/
structure SQTKCover (K : GroupClass.{u}) (G : Type u) [Group G] where
  Cover : Type u
  [coverGroup : Group Cover]
  [coverFinite : Finite Cover]
  sqtk : IsSQTK K Cover
  projection : Cover →* G
  surjective : Function.Surjective projection

attribute [instance] SQTKCover.coverGroup SQTKCover.coverFinite

/-- Binary actions are quasiequivalent when an actual group isomorphism
and a linear isomorphism intertwine them. -/
def Quasiequivalent {D : Type*} [Group D] {W : Type w}
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W) : Prop :=
  ∃ e : G ≃* D, ∃ f : V ≃ₗ[ZMod 2] W,
    ∀ g v, f (ρ g v) = σ (e g) (f v)

/-- The extra hypotheses of G.9.3. The group acting irreducibly is `H`;
`L` need not itself be normal in the ambient group. -/
structure ComponentHypothesis [Finite G] [FiniteDimensional (ZMod 2) V]
    (K : GroupClass.{u}) (ρ : Representation (ZMod 2) G V)
    (A L H : Subgroup G) (m : ℕ) : Prop extends Setup ρ A m where
  quotient : Nonempty (SQTKCover K G)
  component : Theory.GroupTheory.IsComponent G L
  noncentral : ⁅L, A⁆ ≠ ⊥
  normal_H : H.Normal
  irreducible : Representation.IsIrreducible (ρ.comp H.subtype)
  components : H = L ∨ ∃ L₂ : Subgroup G,
    Theory.GroupTheory.IsComponent G L₂ ∧ H = L ⊔ L₂ ∧
      (Quasiequivalent (ρ.comp L.subtype) (ρ.comp L₂.subtype) ∨
       Quasiequivalent (ρ.comp L.subtype) (Representation.dual (ρ.comp L₂.subtype)))

/-- The extra hypotheses of G.9.4 as printed. The Fitting subgroup is
characteristic, so the displayed centralizer condition is faithfulness
of its conjugation action by `A`. -/
structure FittingHypothesis [Finite G] [FiniteDimensional (ZMod 2) V]
    (K : GroupClass.{u}) (ρ : Representation (ZMod 2) G V)
    (A : Subgroup G) (m : ℕ) : Prop extends Setup ρ A m where
  quotient : Nonempty (SQTKCover K G)
  irreducible : Representation.IsIrreducible ρ
  faithful_fitting : A ⊓ Subgroup.centralizer
    (fittingSubgroup G : Set G) = ⊥

end CFSG.Quasithin.ChapterG.Section09
