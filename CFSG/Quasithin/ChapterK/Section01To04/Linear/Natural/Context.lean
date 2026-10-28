module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import CFSG.Quasithin.ChapterK.Defs

/-!
# Source inputs for the natural branch of K.3.2

The actual faithful binary representation retains its SQTK ambient group,
quasisimple generalized Fitting subgroup, and one natural-module intertwiner.
The permitted earlier recognition input is semilinearity of the ambient action
in those same coordinates. It contains no actor exclusion or ratio estimate.

The field-actor calculation must derive the involution and elementary-actor
bounds from these inputs; defining this context does not assert that result.
Recognition and its discharge belong to qt-k03-linear-recognition and the
K.3.2 assembly owner qt-k03-linear-modules.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.2(a)
and K.3.2.1, printed pp.454–455.
-/

@[expose] public section
open Representation Representation.BinaryOffender Theory.GroupTheory

namespace CFSG.Quasithin.ChapterK.Linear.Natural
open ChapterB.QuasisimpleSource
universe u v
variable {G : Type u} [Group G] {V : Type v}
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) (F : BinaryField) (n : ℕ)

/-- The exact scalar equation for the ambient action in the recognized coordinates. -/
def IsSemilinearExtension (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F n)) : Prop :=
  ∀ g : G, ∃ τ : F.Carrier ≃+* F.Carrier,
    ∀ (c : F.Carrier) (v : V),
      e.linearEquiv (ρ g (e.linearEquiv.symm (c • e.linearEquiv v))) =
        τ c • e.linearEquiv (ρ g v)

/-- The standing source hypotheses, with recognition and its scalar normalizer
information explicitly separated from the calculations to be proved. -/
structure SourceInput (K : GroupClass.{u}) where
  sqtk : IsSQTK K G
  fitting : L = generalizedFitting G
  quasisimple : IsQuasisimple L
  faithful : Function.Injective ρ
  irreducible : IsIrreducible (ρ.comp L.subtype)
  cubic_bound : cubicRatio ρ ≤ 2
  dimensions : n = 3 ∨ (n = 4 ∨ n = 5) ∧ F.degree = 1
  natural : ActionEquiv (ρ.comp L.subtype) (linearNatural F n)
  semilinear : IsSemilinearExtension ρ L F n natural

end CFSG.Quasithin.ChapterK.Linear.Natural
