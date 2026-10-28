module
public import Theory.GroupTheory.PairedInvolutiveExtension.Geometry
public import Theory.SpecificGroups.PSL3Two.InvolutionConjugacy
public import Theory.SpecificGroups.PSL3Two.PairedOuterInputs

/-!
# Marked involution geometry for a pair of binary linear components

The actual outer involution of SL₃(2) has a fixed S₃ subgroup, and its
involution cocycles are coboundaries. Together with the unique inner
involution class, these concrete facts instantiate the paired-extension
geometry. The stable order-eight subgroup and selected involution remain
arbitrary, so an application retains its original Sylow subgroup and marks.

This discharges the local class-cover and centralizer-size inputs in the
proof of Aschbacher--Smith 2.4.34, printed p.548 of the 1 March 2004 manuscript.
The ambient nonfusion and component-pair construction belong to that source
application, not to the intrinsic model calculation.
-/

public section
namespace Matrix.PSL3Two.PairedInvolutionGeometry
open Subgroup Theory.GroupTheory.PairedInvolutiveExtension
variable (α : MulAut SL) (hα : Function.Involutive α)
variable (houter : ∀ g : SL, α ≠ MulAut.conj g)
variable (D : Subgroup SL) (hD : ∀ a∈D,α a∈D)
variable (t : SL) (ht : t∈D) (htord : orderOf t=2)

include htord in
private theorem factor_involution_class (a : SL) (ha : a^2=1) (hne : a≠1) : IsConj a t := by
  have haord : orderOf a=2 := orderOf_eq_prime ha hne
  have h := Matrix.PSL3Two.isConj_of_orderOf_eq_two (equiv a) (equiv t)
    ((equiv.orderOf_eq a).trans haord) ((equiv.orderOf_eq t).trans htord)
  simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
    equiv.symm.toMonoidHom.map_isConj h

include htord in
/-- The first marked index-two subgroup has only the two inner classes and s. -/
theorem first_kernel_cover (u : PairedSubgroup α hα D hD)
    (hu : u ∈ (firstBit α hα D hD).ker) (hord : orderOf u.val=2) :
    IsConj (diagonalIn α hα D hD t ht).val u.val ∨
      IsConj (pureIn α hα D hD t ht).val u.val ∨ IsConj (swapIn α hα D hD).val u.val :=
  Theory.GroupTheory.PairedInvolutiveExtension.first_kernel_cover α hα D hD t ht
    (factor_involution_class t htord) u hu hord

include htord in
/-- The second marked index-two subgroup has only the two inner classes and sx. -/
theorem equal_bits_cover (u : PairedSubgroup α hα D hD)
    (hu : u ∈ (differenceBit α hα D hD).ker) (hord : orderOf u.val=2) :
    IsConj (diagonalIn α hα D hD t ht).val u.val ∨
      IsConj (pureIn α hα D hD t ht).val u.val ∨ IsConj (graphSwapIn α hα D hD).val u.val :=
  Theory.GroupTheory.PairedInvolutiveExtension.equal_bits_cover α hα D hD t ht
    (factor_involution_class t htord) u hu hord

include houter htord in
/-- Every remaining involution has Sylow centralizer no larger than that of s. -/
theorem centralizer_class_bound (hcardD : Nat.card D=8)
    (u : PairedSubgroup α hα D hD) (hord : orderOf u.val=2) :
    IsConj (diagonalIn α hα D hD t ht).val u.val ∨ IsConj (pureIn α hα D hD t ht).val u.val ∨
      Nat.card (centralizer ({u} : Set (PairedSubgroup α hα D hD))) ≤
        Nat.card (centralizer ({swapIn α hα D hD} : Set (PairedSubgroup α hα D hD))) :=
  Theory.GroupTheory.PairedInvolutiveExtension.centralizer_class_bound α hα D hD t ht
    (factor_involution_class t htord) (PairedOuterInputs.exists_coboundary_of_outer α hα houter)
    card_SL (PairedOuterInputs.card_fixed_of_outer α hα houter) hcardD u hord

include houter htord in
/-- The literal interchange centralizer has the required four-class cover. -/
theorem swap_centralizer_cover (u : PairedSubgroup α hα D hD)
    (hu : u ∈ centralizer ({swapIn α hα D hD} : Set (PairedSubgroup α hα D hD)))
    (hord : orderOf u.val=2) :
    IsConj (diagonalIn α hα D hD t ht).val u.val ∨ IsConj (graphIn α hα D hD).val u.val ∨
      IsConj (swapIn α hα D hD).val u.val ∨ IsConj (graphSwapIn α hα D hD).val u.val :=
  Theory.GroupTheory.PairedInvolutiveExtension.swap_centralizer_cover α hα D hD t ht
    (factor_involution_class t htord) (PairedOuterInputs.exists_coboundary_of_outer α hα houter)
    u hu hord

/-- The original component involution commutes with the diagonal outer actor
exactly when it is fixed by that actor. -/
theorem pure_commute_graph (htfix : α t=t) :
    Commute (pureIn α hα D hD t ht) (graphIn α hα D hD) := by
  change _ * _ = _ * _
  apply Subtype.ext
  change base α hα 1 t * graph α hα = graph α hα * base α hα 1 t
  simp [base,graph,htfix]

end Matrix.PSL3Two.PairedInvolutionGeometry
