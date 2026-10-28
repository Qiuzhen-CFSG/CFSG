module
public import Theory.GroupAction.PointwiseInnerFrattini
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSylowFixers
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSylowCenter
/-!
# The actual small-component pointwise-fixer kernel

The surviving component catalogue has Sylow centers of order two.
Except for its genuine A6 alternative, its pointwise Sylow fixers are
inner by that Sylow. Consequently every finite two-group fixing this
Sylow pointwise has its Frattini subgroup in the literal action kernel.
This includes the prime-linear case needed by the paired-Sylow argument
of Aschbacher–Smith 2.5.20, printed pp.563–565.
-/
open Subgroup
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
public theorem IsSmallRemainingComponent.alternatingSix_or_frattini_le_fixer_kernel
    {A K : Type*} [Group A] [Finite A] [Group K] [Finite K]
    (hA : IsPGroup 2 A) (hK : IsSmallRemainingComponent K) (P : Sylow 2 K)
    (α : A →* MulAut K) (hfix : ∀ a x, x ∈ P → α a x = x) :
    Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ frattini A ≤ α.ker := by
  rcases hK.alternatingSix_or_sylowPointwiseFixersInner with h | h
  · exact Or.inl h
  · exact Or.inr (Theory.GroupAction.pointwise_inner_frattini_le_ker hA P
      (hK.sylowTwoShape P).center_card (h P) α hfix)
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
