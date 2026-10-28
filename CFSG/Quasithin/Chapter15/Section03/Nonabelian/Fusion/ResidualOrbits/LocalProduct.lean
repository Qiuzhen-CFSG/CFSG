module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Constructions
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.InvolutionCount
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The actual local product and corrected elementary cover in 15.3.61

An involution outside a subgroup which centralizes it gives an actual direct
factor, via multiplication in the ambient group. Applied to `U_a ≃ E₄ × D₈`
and the hyperplane generation of `V`, this constructs `U_a V ≃ E₈ × D₈`.
The two checked model planes then give actual elementary subgroups of order
32 covering the involutions of this local product.

The fixed-lift recognition and hyperplane generation remain explicit inputs.
This module neither identifies arbitrary equal-order groups nor asserts that
the source's fixed lift has those properties before their calculation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1150.
The printed `E₁₆` is incompatible with the checked local product; see
`Fusion.InvolutionCount` for the obstruction and corrected model cover.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits
variable {G : Type*} [Group G]

abbrev FixedLiftModel := Multiplicative (Fin 2 → ZMod 2) × DihedralGroup 4

private noncomputable def commutingJoinEquiv (A B : Subgroup G)
    (hc : ∀ a : A, ∀ b : B, Commute (a : G) (b : G)) (hd : Disjoint A B) :
    (A ⊔ B : Subgroup G) ≃* A × B := by
  let f := A.subtype.noncommCoprod B.subtype hc
  have hr : f.range = A ⊔ B := by
    exact (MonoidHom.noncommCoprod_range A.subtype B.subtype hc).trans
      (by rw [A.range_subtype, B.range_subtype])
  let f' : A × B →* (A ⊔ B : Subgroup G) :=
    f.codRestrict _ (fun x => hr ▸ (show f x ∈ f.range from ⟨x, rfl⟩))
  have hi : Function.Injective f' := by
    intro x y h
    exact Subgroup.mul_injective_of_disjoint hd (congrArg Subtype.val h)
  have hs : Function.Surjective f' := by
    intro y
    have hy : (y : G) ∈ f.range := by rw [hr]; exact y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  exact (MulEquiv.ofBijective f' ⟨hi, hs⟩).symm

private def addCoordinate : FixedLiftModel × Multiplicative (ZMod 2) ≃*
    CentralProductModel where
  toFun x := (Multiplicative.ofAdd (Fin.cons (Multiplicative.toAdd x.2)
    (Multiplicative.toAdd x.1.1)), x.1.2)
  invFun x := ((Multiplicative.ofAdd (Fin.tail (Multiplicative.toAdd x.1)), x.2),
    Multiplicative.ofAdd (Multiplicative.toAdd x.1 0))
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by
    apply Prod.ext
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    · rfl

/-- An involution outside `A`, centralizing `A`, is a genuine direct factor
of `A⟨a⟩`. The equivalence uses multiplication in the ambient group. -/
noncomputable def joinInvolutionEquiv (A : Subgroup G) (a : G)
    (ha : orderOf a = 2) (haA : a ∉ A)
    (hc : a ∈ centralizer (A : Set G)) :
    (A ⊔ zpowers a : Subgroup G) ≃* A × Multiplicative (ZMod 2) := by
  have hd : Disjoint A (zpowers a) := by
    apply Subgroup.disjoint_def.mpr
    intro x hxA hxa
    have hcard : Nat.card (zpowers a) = 2 := by rw [Nat.card_zpowers, ha]
    obtain ⟨_, _, hall⟩ := (Nat.card_eq_two_iff' (1 : zpowers a)).mp hcard
    have ha1 : (⟨a, mem_zpowers a⟩ : zpowers a) ≠ 1 := by
      intro h
      have he : a = 1 := congrArg Subtype.val h
      simp [he] at ha
    by_cases hx : (⟨x, hxa⟩ : zpowers a) = 1
    · exact congrArg Subtype.val hx
    · have he : x = a := congrArg Subtype.val ((hall _ hx).trans (hall _ ha1).symm)
      exact (haA (he ▸ hxA)).elim
  have hc' : ∀ x : A, ∀ y : zpowers a, Commute (x : G) (y : G) := by
    intro x y
    have hy := (zpowers_le.mpr hc) y.property
    exact mem_centralizer_iff.mp hy x x.property
  exact (commutingJoinEquiv A (zpowers a) hc' hd).trans
    (MulEquiv.prodCongr (MulEquiv.refl A) (mulEquivOfPrimeCardEq
      (by rw [Nat.card_zpowers, ha]) (show Nat.card (Multiplicative (ZMod 2)) = 2 by
        rw [Nat.card_eq_fintype_card]; decide)))

/-- Construct `U_a V ≃ E₈ × D₈` from its actual commuting factors.
The `E₄ × D₈` recognition and the source hyperplane generation are explicit. -/
noncomputable def localProductEquiv (A V : Subgroup G) (a : G)
    (ha : orderOf a = 2) (haA : a ∉ A) (haV : a ∈ V)
    (hc : a ∈ centralizer (A : Set G)) (hgen : V ≤ A ⊔ zpowers a)
    (eA : A ≃* FixedLiftModel) : (A ⊔ V : Subgroup G) ≃* CentralProductModel := by
  have he : A ⊔ V = A ⊔ zpowers a :=
    le_antisymm (sup_le le_sup_left hgen) (sup_le_sup_left (zpowers_le.mpr haV) A)
  exact (MulEquiv.subgroupCongr he).trans
    ((joinInvolutionEquiv A a ha haA hc).trans
      ((MulEquiv.prodCongr eA (MulEquiv.refl _)).trans addCoordinate))

/-- The source hyperplane order supplies the required generation of `V`.
Only the intersection order is used; multiplication constructs the product. -/
noncomputable def localProductEquiv_of_hyperplane [Finite G]
    (A V : Subgroup G) (a : G)
    (ha : orderOf a = 2) (haA : a ∉ A) (haV : a ∈ V)
    (hc : a ∈ centralizer (A : Set G))
    (hindex : Nat.card V = 2 * Nat.card (A ⊓ V : Subgroup G))
    (eA : A ≃* FixedLiftModel) : (A ⊔ V : Subgroup G) ≃* CentralProductModel := by
  have hc' : a ∈ centralizer ((A ⊓ V : Subgroup G) : Set G) :=
    centralizer_le (show ((A ⊓ V : Subgroup G) : Set G) ⊆ A from inf_le_left) hc
  let e := joinInvolutionEquiv (A ⊓ V) a ha (fun h => haA h.1) hc'
  have he : (A ⊓ V) ⊔ zpowers a = V := by
    apply eq_of_le_of_card_ge (sup_le inf_le_right (zpowers_le.mpr haV))
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, hindex]
    have htwo : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide
    rw [htwo, Nat.mul_comm]
  apply localProductEquiv A V a ha haA haV hc _ eA
  rw [← he]
  exact sup_le_sup_right inf_le_left _

/-- The corrected elementary planes, embedded in the actual ambient subgroup. -/
@[expose] noncomputable def localPlane (L : Subgroup G) (e : L ≃* CentralProductModel)
    (i : Fin 2) : Subgroup G :=
  (modelPlane i).map (L.subtype.comp e.symm.toMonoidHom)

theorem localPlane_le (L : Subgroup G) (e : L ≃* CentralProductModel) (i : Fin 2) :
    localPlane L e i ≤ L := by
  rintro x ⟨y, _, rfl⟩
  exact (e.symm y).property

theorem localPlane_card (L : Subgroup G) (e : L ≃* CentralProductModel) (i : Fin 2) :
    Nat.card (localPlane L e i) = 32 := by
  rw [localPlane, card_map_of_injective (Subtype.val_injective.comp e.symm.injective)]
  exact modelPlane_card i

theorem localPlane_elementary (L : Subgroup G) (e : L ≃* CentralProductModel) (i : Fin 2) :
    IsElementaryAbelian 2 (localPlane L e i) := by
  let := modelPlane_elementary i
  exact IsElementaryAbelian.map _

/-- Every involution in the actual local product lies in one of the two E₃₂ planes. -/
theorem localPlane_cover (L : Subgroup G) (e : L ≃* CentralProductModel)
    (x : G) (hx : x ∈ L) (hx2 : orderOf x = 2) :
    x ∈ localPlane L e 0 ∨ x ∈ localPlane L e 1 := by
  let xL : L := ⟨x, hx⟩
  have hsq : (e xL) ^ 2 = 1 := by
    rw [← map_pow, show xL ^ 2 = 1 from Subtype.ext (hx2 ▸ pow_orderOf_eq_one x), map_one]
  have hm (i : Fin 2) (hi : e xL ∈ modelPlane i) : x ∈ localPlane L e i := by
    exact mem_map.mpr ⟨e xL, hi, by simp [xL]⟩
  exact (centralProductModel_two_plane_cover (e xL) hsq).imp (hm 0) (hm 1)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits
