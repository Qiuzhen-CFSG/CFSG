module

public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition
public import Theory.PPrimeCore

/-!
# Compatible quotient coordinates for the surviving component

The star quotient is exactly `I/O_{3′}(I)`. This intermediate interface asks
for a realization of that whole quotient as S₆, with the selected component
embedded faithfully as its actual alternating subgroup and with a two-group
kernel. Its construction from the raw mixed configuration and the selected
`L ≃ A₆`, `L*Z* ≃ S₆` remains a separate proof obligation. In particular the
interface does not assume any factor identification or centralizer index.

The elementary transport lemmas retain the actual quotient map. They allow
the local calculations to be proved independently of the construction of
these coordinates. No result here identifies a core with a residual.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of 15.4.18, printed pp.1162–1163.
-/

@[expose] public section

open Subgroup
open Theory.SpecificGroups.SymmetricSix
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals

/-- Derived quotient coordinates, to be constructed from the raw source
setup. This is an intermediate mathematical contract, not a source hypothesis. -/
structure QuotientCoordinates {I : Type*} [Group I] (L : Subgroup I) where
  equiv : (I ⧸ pPrimeCore 3 I) ≃* S6
  component_normal : L.Normal
  component_image : L.map (equiv.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 3 I))) = A6
  component_faithful : Function.Injective
    ((equiv.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 3 I))).comp L.subtype)
  kernel_two : IsPGroup 2 (pPrimeCore 3 I)

namespace QuotientCoordinates
variable {I : Type*} [Group I] {L : Subgroup I} (d : QuotientCoordinates L)

/-- The quotient map followed by the specified model equivalence. -/
def quotientMap : I →* S6 :=
  d.equiv.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 3 I))

theorem quotientMap_surjective : Function.Surjective d.quotientMap :=
  d.equiv.surjective.comp (QuotientGroup.mk'_surjective (pPrimeCore 3 I))

theorem quotientMap_ker : d.quotientMap.ker = pPrimeCore 3 I := by
  rw [quotientMap, MonoidHom.ker_comp_of_injective _ _ d.equiv.injective,
    QuotientGroup.ker_mk']

theorem kernel_le_sylow [Finite I] (T : Sylow 2 I) :
    d.quotientMap.ker ≤ (T : Subgroup I) := by
  rw [d.quotientMap_ker]
  exact d.kernel_two.le_sylow_of_normal T

/-- Component containment makes the quotient faithful on each original
factor; recognition of an image can therefore be lifted to that factor. -/
theorem factor_map_injective {Y : Subgroup I} (hYL : Y ≤ L) :
    Function.Injective (d.quotientMap.comp Y.subtype) := by
  intro x y h
  apply inclusion_injective hYL
  apply d.component_faithful
  exact h

end QuotientCoordinates
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals
