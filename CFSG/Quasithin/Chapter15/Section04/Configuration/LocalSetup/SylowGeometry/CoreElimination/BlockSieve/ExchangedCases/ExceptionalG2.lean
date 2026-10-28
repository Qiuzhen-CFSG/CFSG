module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.Models
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup

/-!
# The exceptional binary G₂ comparison

A G₂(2)-block has quotient the actual derived subgroup G₂(2)′. The checked
identification with the long-root normal closure gives its order 6048, which
is incompatible with either rank-one model of an exchanged component.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.30 and
C.2.7(3)(f), printed pp.135 and 145. The group and order calculations are
imported from the attributed ATLAS development.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases
variable {Q : Type*} [Group Q]

/-- The actual binary derived group, including the derived-group convention in C.1.30. -/
theorem not_binaryG2Derived_quotient
    (hs : Chapter1.XiEmbedding.SwappedModel 3 Q) :
    ¬ Nonempty (Q ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  rintro ⟨e⟩
  have hc : Nat.card Q = 6048 := by
    rw [Nat.card_congr e.toEquiv,
      Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
    exact Atlas.G2.BinaryException.card_H
  exact not_swapped_of_exceptional_order (Or.inr (Or.inr (Or.inl hc))) hs

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases
