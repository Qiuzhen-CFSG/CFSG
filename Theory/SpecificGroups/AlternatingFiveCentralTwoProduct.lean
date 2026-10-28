module
public import Theory.SpecificGroups.AlternatingFiveInvolutionSplit
public import Theory.GroupTheory.DisjointCommutingProduct
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The direct product of a central double cover with an involution lift

The full central kernel of order two has the actual derived subgroup as
a complement once a nonkernel involution lifts. Their commuting product
identifies the original cover with A₅ × C₂.
-/

public noncomputable section
open Subgroup
namespace alternatingGroup

/-- A central double cover of A₅ containing an actual nonkernel involution
is the direct product A₅ × C₂. The kernel in the hypotheses is the full kernel. -/
theorem central_two_product_of_involution
    {H : Type*} [Group H] [Finite H]
    (f : H →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center H) (hk : Nat.card f.ker = 2)
    (a : H) (ha : a ^ 2 = 1) (hne : f a ≠ 1) :
    Nonempty (H ≃* (alternatingGroup (Fin 5) × Multiplicative (ZMod 2))) := by
  have hK := central_two_complement_of_involution f hf hc hk a ha hne
  let eA : commutator H ≃* alternatingGroup (Fin 5) :=
    hK.symm.QuotientMulEquiv.symm.trans (QuotientGroup.quotientKerEquivOfSurjective f hf)
  let eZ : f.ker ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hk (by
    simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card])
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    f.ker (commutator H) hK.disjoint (hc.trans (center_le_centralizer _))
  let ep : f.ker × commutator H ≃* H :=
    e.trans ((MulEquiv.subgroupCongr hK.sup_eq_top).trans topEquiv)
  exact ⟨ep.symm.trans ((eZ.prodCongr eA).trans MulEquiv.prodComm)⟩

end alternatingGroup
