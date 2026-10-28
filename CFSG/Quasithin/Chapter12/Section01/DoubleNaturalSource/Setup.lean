module

public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses
public import Theory.Representation.BinaryNaturalDual.Action
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# The doubled branch on the original chosen orbit

The seed V, its T-orbit W, and its full normalizer orbit are different
subgroups. The doubled branch of 3.2.5 identifies the latter two only.
The component marking below uses the literal quotient L/O₂(L) and its
conjugation on W. The full action quotient is the quotient of N_G(L) by
the kernel of its actual conjugation on W, hence by C_{N_G(L)}(W).

These are input model data for the n = 4, 5 slice of 12.1.11, not any of
its centralizer or weak-closure conclusions. Source: Aschbacher--Smith,
combined manuscript, 1 March 2004, 3.2.5 and 12.1.11, pp.580,794--795.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic BinaryNaturalDual
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] (T : Sylow 2 G) (L V : Subgroup G)

/-- Conjugation by the full original normalizer, after the branch equality. -/
def normalizerAction
    (he : componentOrbit V (T : Subgroup G) = componentOrbit V (normalizer (L : Set G))) :
    normalizer (L : Set G) →* MulAut (componentOrbit V (T : Subgroup G)) :=
  (componentOrbit V (T : Subgroup G)).normalizerMonoidHom.comp
    (inclusion (by rw [he]; exact le_normalizer_componentOrbit _ _))

/-- The quotient kernel is the literal relative centralizer. -/
theorem normalizerAction_ker
    (he : componentOrbit V (T : Subgroup G) = componentOrbit V (normalizer (L : Set G))) :
    (normalizerAction T L V he).ker =
      (centralizer (componentOrbit V (T : Subgroup G) : Set G)).subgroupOf
        (normalizer (L : Set G)) := by
  ext x
  change (componentOrbit V (T : Subgroup G)).normalizerMonoidHom _ = 1 ↔ _
  rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
  rfl

/-- The actual n ⊕ n* alternative, retaining both quotient and action maps.
Over F₂ the linear group is the source L_n(2); no abstract family tag is used. -/
structure DoubledBranch (n : ℕ) where
  degree : n = 4 ∨ n = 5
  orbit_eq : componentOrbit V (T : Subgroup G) = componentOrbit V (normalizer (L : Set G))
  component : (L ⧸ pCore 2 L) ≃* LinearGroup n
  coordinates : componentOrbit V (T : Subgroup G) ≃* Multiplicative (CoordinateSpace n)
  component_action : ∀ (l : L) (w : componentOrbit V (T : Subgroup G)),
    ((coordinates.symm (Multiplicative.ofAdd
      (naturalDualRepresentation (component (QuotientGroup.mk' (pCore 2 L) l))
        (coordinates w).toAdd))) : G) = (l : G) * (w : G) * (l : G)⁻¹
  full : (normalizer (L : Set G) ⧸ (normalizerAction T L V orbit_eq).ker) ≃*
    MulAut (LinearGroup n)

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
