module
public import Theory.GroupTheory.AbelianExponentFourRecognition
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# A product of three commuting cyclic factors

Two order-four elements with different squares generate a direct product
of two cyclic groups. Its elements of square one belong to the two square
subgroups. An additional involution outside those square subgroups is
therefore an independent direct factor.

This is the abelian span calculation in Aschbacher--Smith 14.3.22,
printed p.999, separated from the source-specific construction.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem mem_square_zpowers_of_square_one (a x : G) (ha : orderOf a = 4)
    (hx : x ∈ zpowers a) (hx2 : x ^ 2 = 1) : x ∈ zpowers (a ^ 2) := by
  by_cases hx1 : x = 1
  · exact hx1 ▸ (zpowers (a ^ 2)).one_mem
  have ho : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have ha2 : orderOf (a ^ 2) = 2 := by rw [orderOf_pow, ha]; decide
  have he : x = a ^ 2 := congrArg Subtype.val
    (IsCyclic.eq_of_orderOf_eq_two
      (show orderOf (⟨x, hx⟩ : zpowers a) = 2 from (orderOf_coe _).symm.trans ho)
      (show orderOf (⟨a ^ 2, (zpowers a).pow_mem (mem_zpowers a) 2⟩ : zpowers a) = 2 from
        (orderOf_coe _).symm.trans ha2))
  exact he.symm ▸ mem_zpowers (a ^ 2)

/-- All square-one elements in the product of two independent cyclic
four-groups lie in the product of their square subgroups. -/
theorem square_one_mem_square_join (x y t : G)
    (hx : orderOf x = 4) (hy : orderOf y = 4)
    (hxy : x ^ 2 ≠ y ^ 2) (hc : Commute x y)
    (ht : t ∈ zpowers x ⊔ zpowers y) (ht2 : t ^ 2 = 1) :
    t ∈ zpowers (x ^ 2) ⊔ zpowers (y ^ 2) := by
  have hd := disjoint_zpowers_of_order_four_distinct_squares hx hy hxy
  have hcomm : zpowers x ≤ centralizer (zpowers y : Set G) := by
    rintro u ⟨i, rfl⟩ v ⟨j, rfl⟩
    exact (hc.zpow_zpow i j).symm.eq
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (zpowers x) (zpowers y) hd hcomm
  obtain ⟨⟨u, v⟩, huv⟩ := e.surjective ⟨t, ht⟩
  have huvG : (u : G) * v = t := (he u v).symm.trans (congrArg Subtype.val huv)
  have hcuv : Commute (u : G) v := (hcomm u.property v v.property).symm
  have hp : (u : G) ^ 2 * (v : G) ^ 2 = 1 := by rw [← hcuv.mul_pow, huvG, ht2]
  have hu2 : (u : G) ^ 2 = 1 := by
    apply disjoint_def.mp hd ((zpowers x).pow_mem u.property 2)
    rw [eq_inv_of_mul_eq_one_left hp]
    exact (zpowers y).inv_mem ((zpowers y).pow_mem v.property 2)
  have hv2 : (v : G) ^ 2 = 1 := by simpa only [hu2, one_mul] using hp
  rw [← huvG]
  exact (zpowers (x ^ 2) ⊔ zpowers (y ^ 2)).mul_mem
    (mem_sup_left (mem_square_zpowers_of_square_one x u hx u.property hu2))
    (mem_sup_right (mem_square_zpowers_of_square_one y v hy v.property hv2))

/-- An independent involution splits off from two commuting cyclic
four-groups, with the literal join as domain. -/
theorem three_cyclic_four_span_equiv (x y w : G)
    (hx : orderOf x = 4) (hy : orderOf y = 4) (hw : orderOf w = 2)
    (hxy : x ^ 2 ≠ y ^ 2) (hcxy : Commute x y)
    (hcxw : Commute x w) (hcyw : Commute y w)
    (hwout : w ∉ zpowers (x ^ 2) ⊔ zpowers (y ^ 2)) :
    Nonempty ((zpowers x ⊔ zpowers y ⊔ zpowers w : Subgroup G) ≃*
      ((Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) × Multiplicative (ZMod 2))) := by
  classical
  have hcomm : zpowers x ≤ centralizer (zpowers y : Set G) := by
    rintro u ⟨i, rfl⟩ v ⟨j, rfl⟩
    exact (hcxy.zpow_zpow i j).symm.eq
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (zpowers x) (zpowers y)
    (disjoint_zpowers_of_order_four_distinct_squares hx hy hxy) hcomm
  let ex : zpowers x ≃* Multiplicative (ZMod 4) := mulEquivOfCyclicCardEq
    (by simpa using hx)
  let ey : zpowers y ≃* Multiplicative (ZMod 4) := mulEquivOfCyclicCardEq
    (by simpa using hy)
  let ew : zpowers w ≃* Multiplicative (ZMod 2) := mulEquivOfCyclicCardEq
    (by simpa using hw)
  have hwE : w ∉ zpowers x ⊔ zpowers y := fun ht => hwout
    (square_one_mem_square_join x y w hx hy hxy hcxy ht (hw ▸ pow_orderOf_eq_one w))
  have hd : Disjoint (zpowers x ⊔ zpowers y) (zpowers w) := by
    apply disjoint_def.mpr
    intro t ht htW
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp htW)
    have hi2 : i < 2 := by simpa only [hw, Finset.mem_range] using hi
    interval_cases i
    · simp
    · exact False.elim (hwE (by simpa only [pow_one] using ht))
  have hc : zpowers x ⊔ zpowers y ≤ centralizer (zpowers w : Set G) := by
    apply sup_le
    · rintro u ⟨i, rfl⟩ v ⟨j, rfl⟩
      exact (hcxw.zpow_zpow i j).symm.eq
    · rintro u ⟨i, rfl⟩ v ⟨j, rfl⟩
      exact (hcyw.zpow_zpow i j).symm.eq
  obtain ⟨f, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (zpowers x ⊔ zpowers y) (zpowers w) hd hc
  exact ⟨f.symm.trans ((e.symm.trans (ex.prodCongr ey)).prodCongr ew)⟩

end Theory.GroupTheory
