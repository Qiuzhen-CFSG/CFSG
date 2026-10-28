module

public import Theory.SpecificGroups.OmegaSixThree.OrthogonalityGraph

/-!
# The number of projective negative points

The existing list of 117 negative representatives is complete. Checking that
its representatives are distinct even up to sign makes it a bijective list of
the actual projective points. This is the point count in the orbit-stabilizer
calculation of the F.5 vertex group.

Source: Aschbacher–Smith F.5.1(1), printed p.300.
-/

public section
namespace OmegaSixThree.OrthogonalityGraph

theorem coordinate_representatives_distinct : ∀ i j : Fin 117,
    Certificate.coords i = Certificate.coords j ∨
      Certificate.coords i = -Certificate.coords j → i = j := by
  decide +kernel

theorem coordinatePoint_injective : Function.Injective coordinatePoint := by
  intro i j hij
  exact coordinate_representatives_distinct i j ((point_eq_iff _ _ _ _).mp hij)

theorem card_point : Nat.card Point = 117 := by
  exact (Nat.card_congr (Equiv.ofBijective coordinatePoint
    ⟨coordinatePoint_injective,coordinatePoint_surjective⟩)).symm.trans (Nat.card_fin 117)

end OmegaSixThree.OrthogonalityGraph
