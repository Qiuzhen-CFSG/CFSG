module
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.ElementaryAbelian.Join

/-!
# Inverted cubic elements in an elementary-plane centralizer

In a finite group of three-rank at most two, an elementary nine-group
contains every cubic element of its centralizer: their elementary join
still has order at most nine. An element centralizing the nine-group
therefore cannot invert a nonidentity cubic element in that centralizer.

Source application: the dihedral-pair reduction in Aschbacher--Smith,
proof of 12.6.26, printed pp.831--832. The original Sylow nine-group and
literal quotient application are in NaturalSource/ResidualCentralizer.
-/

public section
open Subgroup
namespace Theory.GroupTheory
/-- In three-rank at most two, an element fixing an elementary nine-group
cannot invert a cubic element in its centralizer. -/
theorem no_inverted_three_in_plane_centralizer
    {X : Type*} [Group X] [Finite X] (hr : primeRank 3 X ≤ 2)
    (A : Subgroup X) [IsElementaryAbelian 3 A] (hA : Nat.card A = 9)
    (t x : X) (ht : t ∈ centralizer (A : Set X))
    (hx : x ∈ centralizer (A : Set X)) (hi : t*x*t⁻¹=x⁻¹)
    (ho : orderOf x = 3) : False := by
  have hx3 : x^3=1 := ho ▸ pow_orderOf_eq_one x
  let : IsElementaryAbelian 3 (zpowers x) := IsElementaryAbelian.zpowers_of_pow_eq_one hx3
  let : IsElementaryAbelian 3 (A ⊔ zpowers x : Subgroup X) :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hx)
  have hb := (primeRank_le_iff_elementary_card_le X).mp hr (A ⊔ zpowers x) inferInstance
  have he : A = A ⊔ zpowers x := eq_of_le_of_card_ge le_sup_left (by rw [hA];exact hb)
  have hxm : x ∈ A := he.symm ▸ mem_sup_right (mem_zpowers x)
  have hc : t*x*t⁻¹=x := by rw [←ht x hxm,mul_inv_cancel_right]
  have hx2 : x^2=1 := by
    calc
      x^2 = x*x := pow_two x
      _ = x*x⁻¹ := congrArg (x*·) (hc.symm.trans hi)
      _ = 1 := mul_inv_cancel x
  have hd := orderOf_dvd_of_pow_eq_one hx2
  exact (by decide : ¬ 3 ∣ 2) (ho ▸ hd)
end Theory.GroupTheory
