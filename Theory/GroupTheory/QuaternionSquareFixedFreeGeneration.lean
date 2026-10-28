module
public import Theory.GroupTheory.FrattiniFixedFreeDisplacement
public import Theory.GroupTheory.ConjugatePairSeed.OrthogonalAction
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms

/-!
# Lifting a fixed-free square action through a quaternion core

The exact square coordinates transport fixed-freeness to Q/Z(Q). Its center
is the Frattini subgroup, so the displacement-generation lemma forces an
actor-normalized subgroup containing all commutators to contain Q itself.
The ambient consumer keeps both original subgroup inclusions.

Source: Aschbacher–Smith13.5.15, printed p.920.
-/

@[expose] public section
open Subgroup
namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (q : QuaternionCentralProductData Q)

theorem square_action_intertwines (a : MulAut Q) (v : Q⧸center Q) :
    (BinaryFourPlus.wreathToIsometry (q.quotientWreathAction a)).val
      (q.squareCoordinates (Additive.ofMul v))=
      q.squareCoordinates (Additive.ofMul (quotientAut (center Q) a v)) := by
  have hh (i : BinaryFourPlus.C2) : BinaryFourPlus.coordinate
      ((BinaryFourPlus.wreathToIsometry (q.quotientWreathAction a)).val
        (q.squareCoordinates (Additive.ofMul v))) i=
      BinaryFourPlus.coordinate (q.squareCoordinates (Additive.ofMul (quotientAut (center Q) a v))) i := by
    rw [BinaryFourPlus.wreathToIsometry_coordinate]
    exact (q.quotientWreathAction_apply a v i).symm
  exact Prod.ext (by simpa only [BinaryFourPlus.coordinate,ite_true] using hh 1)
    (by simpa only [BinaryFourPlus.coordinate,BinaryFourPlus.swapIndex_ne_one,ite_false]
      using hh BinaryFourPlus.swapIndex)

theorem eq_top_of_square_fixed_free (a : MulAut Q)
    (hf : ∀v:BinaryFourPlus.V,(BinaryFourPlus.wreathToIsometry (q.quotientWreathAction a)).val v=v→v=0)
    (K : Subgroup Q) (hd : ∀x:Q,a x*x⁻¹∈K) : K=⊤ := by
  let : IsExtraspecial 2 Q := q.extraspecial
  let : IsElementaryAbelian 2 (Q⧸center Q) := q.quotient_elementary
  let : IsMulCommutative (Q⧸center Q) := IsElementaryAbelian.toIsMulCommutative (p:=2)
  apply eq_top_of_fixedFree_quotient_displacements (center Q)
    (IsExtraspecial.frattini_eq_center (p:=2)).symm.le a ?_ K hd
  intro v hv
  have hx := hf (q.squareCoordinates (Additive.ofMul v)) (by rw [square_action_intertwines,hv])
  have hzero : Additive.ofMul v=0 := q.squareCoordinates.injective (hx.trans (map_zero _).symm)
  exact hzero

end Subgroup.QuaternionCentralProductData
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem quaternion_le_of_square_fixed_free (Q I : Subgroup G)
    (q : QuaternionCentralProductData Q) (hIQ : I≤normalizer (Q:Set G))
    (hQI : Q≤normalizer (I:Set G)) (x : I)
    (hf : ∀v:BinaryFourPlus.V,(BinaryFourPlus.wreathToIsometry (seedOrthogonalAction I Q hIQ q x)).val v=v→v=0) :
    Q≤I := by
  apply subgroupOf_eq_top.mp
  apply q.eq_top_of_square_fixed_free (seedConjugation I Q hIQ x) hf
  intro u
  exact (le_normalizer_iff_commutator_le_left.mp hQI)
    (commutator_mem_commutator x.property u.property)

end Subgroup
end
