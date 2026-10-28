module

public import CFSG.KnownSimple.CarrierCatalogue

/-!
# Simple sections of solvable groups

A solvable simple group is cyclic of prime order. Consequently every
solvable group has all simple sections in the already constructed cyclic
part of the known-simple catalogue. This supplies the solvable cases of
the proper-K calculations in the converse of Aschbacher–Smith,
Theorem 0.1.2, printed p.4. It does not identify the partial catalogue with K.
-/

namespace CFSG.Quasithin.MainConverse

open CFSG.KnownSimple

public theorem primeCyclic_of_solvable_simple (S : Type*) [Group S] [IsSimpleGroup S]
    [Group.IsSolvable S] : IsPrimeCyclicCarrier S := by
  let : CommGroup S := { (inferInstance : Group S) with
    mul_comm := IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance }
  exact ⟨Nat.card S, IsSimpleGroup.prime_card,
    ⟨(zmodCyclicMulEquiv (inferInstance : IsCyclic S)).symm⟩⟩

/-- The cyclic branch suffices for all simple sections of a solvable group. -/
public theorem solvable_isKGroup_constructed (G : Type*) [Group G]
    [Group.IsSolvable G] : IsKGroup IsConstructedCarrier G := by
  intro S _ hS U f hf
  let := hS
  let : Group.IsSolvable S := Group.isSolvable_of_surjective (f := f) hf
  exact .cyclic (primeCyclic_of_solvable_simple S)

end CFSG.Quasithin.MainConverse
