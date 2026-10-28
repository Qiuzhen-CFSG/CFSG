module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.LocalAction

/-!
# The intrinsic component calculation for the Bender torus

`ComponentTorus` isolates the calculation inside the rank-one component.
It concerns its actual Sylow omega subgroup and literal conjugation, without
mentioning the external subgroup R or the commuting omega factor. The fixed
subgroup is allowed to contain the component center, as it must in the
exceptional Suzuki cover. Existence of this data is a separate model theorem;
the record itself does not prove a source assertion.

`InvolutionLifting` retains exactly the central involution-lifting input used
in the first paragraph of Proposition 16.5.1. It holds for a trivial center,
and for the elementary Suzuki center with the lifting clause of I.2.2(4).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Proposition
16.5.1, printed p.1194, with 16.1.2 and I.2.2(4).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction
open Subgroup
variable {G : Type*} [Group G]

/-- The genuine cover input; no torus or action conclusion is a premise. -/
def InvolutionLifting (L : Subgroup G) : Prop :=
  IsElementaryAbelian 2 (center L) ∧
    ∀ x : L, (QuotientGroup.mk' (center L) x) ^ 2 = 1 →
      ∃ y : L, y ^ 2 = 1 ∧
        QuotientGroup.mk' (center L) y = QuotientGroup.mk' (center L) x

/-- The outstanding intrinsic model calculation. Its existence must be proved
from an actual rank-one model equivalence and the permitted central cover. -/
structure ComponentTorus (T : Sylow 2 G) (L : Subgroup G) (n : ℕ) where
  actor : Subgroup G
  actor_le : actor ≤ L ⊓ normalizer (componentSylow T L : Set G)
  actor_cyclic : IsCyclic actor
  actor_card : Nat.card actor = 2 ^ n - 1
  elementary : IsElementaryAbelian 2 (omegaOneAmbient (componentSylow T L))
  fixed_le : omegaOneAmbient (componentSylow T L) ⊓ centralizer (actor : Set G) ≤
    centralizer (L : Set G)
  moved_card : Nat.card ↥(⁅omegaOneAmbient (componentSylow T L), actor⁆ : Subgroup G) = 2 ^ n
  regular : ∀ v ∈ ⁅omegaOneAmbient (componentSylow T L), actor⁆, v ≠ 1 →
    ∀ w ∈ ⁅omegaOneAmbient (componentSylow T L), actor⁆, w ≠ 1 →
      ∃! x : actor, MulAut.conj (x : G) v = w
/-- The additional normalizer calculation used only in the third paragraph.
It must be proved separately; the first-paragraph torus calculation does not
imply it for an arbitrary central cover. -/
def OmegaNormalizerAction (T : Sylow 2 G) (L X : Subgroup G) : Prop :=
  ∀ l ∈ L, l ∈ normalizer (omegaOneAmbient (componentSylow T L) : Set G) →
      ∃ x : X, ∀ u ∈ omegaOneAmbient (componentSylow T L),
        MulAut.conj (x : G) u = MulAut.conj l u

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction
