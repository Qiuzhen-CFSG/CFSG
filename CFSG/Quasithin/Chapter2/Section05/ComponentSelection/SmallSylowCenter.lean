module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallModelFacts
public import Theory.GroupTheory.DihedralGeneratedFactor
public import Theory.GroupTheory.SemidihedralSquareData
/-! # The order-two Sylow center of every surviving component shape
Both the dihedral groups of order at least eight and the semidihedral group
of order sixteen have center of order two. This transports the exact source
2.5.8(3) model equivalences to the intrinsic center, used in 2.5.8(4).
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup
variable {K:Type*} [Group K]
theorem SourceSylowTwoShape.center_card (h:SourceSylowTwoShape K) : Nat.card (center K)=2 := by
  unfold SourceSylowTwoShape at h
  rcases h with h|h
  · obtain ⟨m,hm,⟨e⟩⟩:=h
    exact DihedralGroup.center_card_of_equiv hm e
  · obtain ⟨e⟩:=h
    rw [Nat.card_congr (centerCongr e).toEquiv]
    exact (Semidihedral.square_data (by omega : 4≤4)
      (Semidihedral.standardRotation 4 (by omega)) (Semidihedral.standardReflection 4 (by omega))
      (Semidihedral.standardRotation_order 4 (by omega)) (Semidihedral.standardReflection_order 4 (by omega))
      (Semidihedral.standard_conjugation 4 (by omega)) (Semidihedral.standard_generators 4 (by omega))).1
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
