module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.SylowEightRigidity.Certificates
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex.CentralizerSylow

/-!
# Comparing a full two-part max4 Sylow with the reference matrix group

The independently proved literal involution-centralizer calculation bounds
every ambient J₄ Sylow two-subgroup by order 2^21. If 2^21 divides the order of
literal max4, a local Sylow has at least that order. Its actual ambient image
is therefore Sylow. The reference matrix two-subgroup has the same proved
order and is also ambient Sylow. Ambient Sylow conjugacy supplies an actual
multiplicative equivalence, restricted along the injective subgroup maps.

This uses the ambient Sylow-order theorem, not the full order of J₄. Equal
orders alone are not used to identify abstract groups: both groups are
embedded into the same literal matrix carrier and are proved Sylow there.
The lower bound on the two-part of max4 remains an explicit premise.

Source context: Kleidman--Wilson (1988), pp.484--510, and the literal ATLAS
max4 words in `SymmetricLinear.Model`. The ambient-order bound is proved in
`OddIndex.CentralizerSylow` from the actual involution centralizer.
-/

public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover
open Subgroup Janko4.OuterReduction.OddIndex

attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The literal max4 two-part lower bound supplies the required actual model comparison. -/
theorem max4SylowEightModelComparison_of_twoPart
    (horder : 2 ^ 21 ∣ Nat.card Janko4.LocalStructure.SymmetricLinear.max4Subgroup) :
    Max4SylowEightModelComparison := by
  let M := Janko4.LocalStructure.SymmetricLinear.max4Subgroup
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := M)
  let U : Subgroup Janko4.Model := P.toSubgroup.map M.subtype
  have hUcard : Nat.card U = Nat.card P := card_map_of_injective M.subtype_injective
  have hUtwo : IsPGroup 2 U := P.isPGroup'.map M.subtype
  obtain ⟨S, hUS⟩ := hUtwo.exists_le_sylow
  have hlarge : 2 ^ 21 ≤ Nat.card P :=
    Nat.le_of_dvd Nat.card_pos (P.pow_dvd_card_of_pow_dvd_card horder)
  have heq : U = S.toSubgroup := eq_of_le_of_card_ge hUS (by
    rw [hUcard, ambient_sylow_card]
    exact hlarge)
  let Q : Sylow 2 Janko4.Model := Sylow.ofCard twoSubgroup
    (twoSubgroup_card.trans ((ambient_sylow_card S).symm.trans S.card_eq_multiplicity))
  let e : P ≃* S := (P.toSubgroup.equivMapOfInjective M.subtype M.subtype_injective).trans
    (MulEquiv.subgroupCongr heq)
  exact ⟨P, ⟨e.trans (S.equiv Q)⟩⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover
