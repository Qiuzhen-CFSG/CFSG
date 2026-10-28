module
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.ModuleFactors.ChiefFactors.Irreducibility
public import Theory.Representation.SubspaceQuotient

/-!
# The point parabolic's chief intervals

The sections V₇/V₁ and V/V₇ are irreducible for the point parabolic.
Consequently an invariant subspace in either interval is an endpoint. This form
is convenient for transporting the chief factor through an exterior marking.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
12.5.2 and the point-core argument in 12.5.8, printed pp. 817 and 820.
-/

public section
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

theorem point_middle_invariant_interval (W : Submodule (ZMod 2) V)
    (h1 : V₁ ≤ W) (h7 : W ≤ V₇)
    (hn : ∀ g : parabolic 2, ∀ v ∈ W, exteriorAction 2 g v ∈ W) :
    W = V₁ ∨ W = V₇ := by
  let S : Subrepresentation seventhSubrepresentation.toRepresentation := {
    toSubmodule := W.comap V₇.subtype
    apply_mem_toSubmodule := fun g v hv => hn g v hv }
  have hNS : firstInsideSeventh ≤ S := fun v hv => h1 hv
  let : IsIrreducible firstInsideSeventh.quotientRepresentation :=
    middleChiefFactor_isIrreducible
  rcases Subrepresentation.le_or_sup_eq_top_of_irreducible_quotient firstInsideSeventh S with he | he
  · left
    apply le_antisymm _ h1
    intro v hv
    exact he (show (⟨v, h7 hv⟩ : V₇) ∈ S.toSubmodule from hv)
  · right
    have hs : S.toSubmodule = ⊤ := by
      simpa only [sup_eq_right.mpr (show firstInsideSeventh.toSubmodule ≤ S.toSubmodule from hNS)] using he
    apply le_antisymm h7
    intro v hv
    have hm : (⟨v, hv⟩ : seventhSubrepresentation.toSubmodule) ∈ S.toSubmodule := by
      rw [hs]
      trivial
    exact hm

theorem point_upper_invariant_interval (W : Submodule (ZMod 2) SL5ExteriorSquare.V)
    (h7 : V₇ ≤ W)
    (hn : ∀ g : parabolic 2, ∀ v ∈ W, exteriorAction 2 g v ∈ W) :
    W = V₇ ∨ W = ⊤ := by
  let S : Subrepresentation firstParabolicRepresentation := {
    toSubmodule := W
    apply_mem_toSubmodule := hn }
  have hNS : seventhSubrepresentation ≤ S := h7
  let : IsIrreducible seventhSubrepresentation.quotientRepresentation :=
    lastChiefFactor_isIrreducible
  rcases Subrepresentation.le_or_sup_eq_top_of_irreducible_quotient seventhSubrepresentation S
    with he | he
  · exact Or.inl (le_antisymm he h7)
  · right
    simpa only [sup_eq_right.mpr
      (show seventhSubrepresentation.toSubmodule ≤ S.toSubmodule from hNS)] using he

end Representation.SL5ExteriorSquare
