module
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure

/-!
# Reduced closures of elementary central Sylow seeds

In a characteristic-two group, every elementary subgroup of the center of
its Sylow two-subgroup lies in the two-core and centralizes that core.
Its normal closure is therefore elementary abelian, and the Sylow-central
inheritance theorem makes its literal centralizer quotient two-reduced.

This retains the original smaller seed in Aschbacher--Smith B.2.14,
printed p.78, as used by the tensor point argument 9.4.1, printed p.735.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory

theorem centralSeed_normalClosure_reduced
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G) (Z : Subgroup G)
    [IsElementaryAbelian 2 Z]
    (hZP : Z ≤ P) (hc : Z ≤ centralizer (P : Set G))
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    IsPReduced 2 (normalClosure (Z : Set G)) := by
  have hZQ : Z ≤ pCore 2 G := fun z hz => hchar
    (fun y hy => hc hz y (pCore_isPGroup.le_sylow_of_normal P hy))
  let W := normalClosure (Z : Set G)
  have hWQ : W ≤ pCore 2 G := normalClosure_le_normal hZQ
  have hWC : W ≤ centralizer (pCore 2 G : Set G) := normalClosure_le_normal
    (hc.trans (centralizer_le (pCore_isPGroup.le_sylow_of_normal P)))
  let : IsMulCommutative W := le_centralizer_iff_isMulCommutative.mp
    (hWC.trans (centralizer_le hWQ))
  exact isPReduced_normalClosure_of_sylow_central P Z hZP hc

end Theory.GroupTheory
