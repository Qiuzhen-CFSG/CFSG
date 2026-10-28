module

public import Theory.GroupTheory.QuaternionCentralProductInvolutions
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.ElementaryAbelian.Extraspecial

/-!
# Intrinsic square geometry of the plus quaternion central product

The data are two actual commuting quaternion subgroups generating the group,
with intersection of order two. They determine the center, the order 32,
and the elementary central quotient of order 16. Squaring descends to this
quotient with values in the actual center and is invariant under the actual
automorphism action. Thus no choice of an abstract group of order 32 replaces
the factor embeddings or the square geometry.

The center calculation and the square calculation use the existing quaternion
factor lemmas. A change of representative is a central involution, so it does
not change the square. Every automorphism fixes the center pointwise.

Source: Aschbacher–Smith, Lemma 14.2.21, printed p.988, PDF p.1005.
-/

namespace Subgroup

/-- An intrinsic presentation as the central product of two quaternion eights. -/
public structure QuaternionCentralProductData (Q : Type*) [Group Q] where
  left : Subgroup Q
  right : Subgroup Q
  left_model : Nonempty (left ≃* QuaternionGroup 2)
  right_model : Nonempty (right ≃* QuaternionGroup 2)
  intersection_card : Nat.card (left ⊓ right : Subgroup Q) = 2
  commute : ∀ b ∈ left, ∀ c ∈ right, b * c = c * b
  span : left ⊔ right = ⊤

namespace QuaternionCentralProductData

variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

include d

/-- The intrinsic central product has order 32. -/
public theorem card : Nat.card Q = 32 := by
  have hc (D : Subgroup Q) (hD : Nonempty (D ≃* QuaternionGroup 2)) :
      Nat.card D = 8 := by
    obtain ⟨e⟩ := hD
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hn : d.right ≤ normalizer (d.left : Set Q) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro c hc b hb
    exact d.commute b hb c hc
  have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes d.left d.right hn
  rw [hc d.left d.left_model, hc d.right d.right_model, d.intersection_card,
    d.span, Nat.card_congr (topEquiv : (⊤ : Subgroup Q) ≃* Q).toEquiv] at h
  omega

/-- The center is precisely the common subgroup of the quaternion factors. -/
public theorem center_eq : center Q = d.left ⊓ d.right := by
  have hcard : Nat.card (center Q) = 2 := by
    let e : (d.left ⊔ d.right : Subgroup Q) ≃* Q :=
      (MulEquiv.subgroupCongr d.span).trans topEquiv
    exact (Nat.card_congr (centerCongr e).toEquiv).symm.trans
      (quaternion_central_product_center_card d.left d.right d.left_model d.right_model
        d.intersection_card d.commute)
  symm
  apply eq_of_le_of_card_ge ?_ (by rw [hcard, d.intersection_card])
  intro z hz
  have h : d.left ⊔ d.right ≤ centralizer ({z} : Set Q) := by
    apply sup_le
    · intro b hb
      exact mem_centralizer_singleton_iff.mpr (d.commute b hb z hz.2)
    · intro c hc
      exact mem_centralizer_singleton_iff.mpr (d.commute z hz.1 c hc).symm
  apply mem_center_iff.mpr
  intro x
  exact mem_centralizer_singleton_iff.mp (h (d.span ▸ mem_top x))

public theorem center_card : Nat.card (center Q) = 2 := by
  rw [d.center_eq, d.intersection_card]

/-- Every square lies in the actual common center. -/
public theorem square_mem_center (x : Q) : x ^ 2 ∈ center Q := by
  rw [d.center_eq]
  exact quaternion_central_product_square_mem_inf d.left d.right d.left_model
    d.right_model d.intersection_card d.commute x (d.span ▸ mem_top x)

public theorem center_square (z : center Q) : z ^ 2 = 1 := by
  simpa only [d.center_card] using pow_card_eq_one' (x := z)

/-- The central quotient has order sixteen. -/
public theorem quotient_card : Nat.card (Q ⧸ center Q) = 16 := by
  have h := (center Q).card_mul_index
  rw [d.center_card, d.card, index_eq_card] at h
  omega

/-- The central quotient is an elementary abelian two-group. -/
public theorem quotient_elementary : IsElementaryAbelian 2 (Q ⧸ center Q) := by
  have hs (x : Q ⧸ center Q) : x ^ 2 = 1 := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center Q) x
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (d.square_mem_center x)
  have hi (x : Q ⧸ center Q) : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_two] using hs x
  refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  calc
    x * y = (x * y)⁻¹ := (hi _).symm
    _ = y * x := by rw [mul_inv_rev, hi, hi]

/-- Extraspeciality follows from the factor presentation; it is not an input. -/
public theorem extraspecial : IsExtraspecial 2 Q where
  center_order_p := d.center_card
  quotient_elementary_abelian := d.quotient_elementary
  quotient_nontrivial := by
    classical
    let := Fintype.ofFinite (Q ⧸ center Q)
    apply Fintype.one_lt_card_iff_nontrivial.mp
    rw [← Nat.card_eq_fintype_card, d.quotient_card]
    decide

/-- Automorphisms fix the common central involution, and hence the whole center. -/
public theorem fixes_center (a : MulAut Q) (z : center Q) : a (z : Q) = z := by
  let e := centerCongr a
  have he : e z = z := by
    by_cases hz : z = 1
    · simp [hz]
    · obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : center Q)).mp d.center_card
      have hn : e z ≠ 1 := fun h => hz (e.injective (h.trans e.map_one.symm))
      exact (hw (e z) hn).trans (hw z hz).symm
  exact congrArg Subtype.val he

/-- Squares do not depend on the choice of representative modulo the center. -/
public theorem square_eq_of_quotient_eq (x y : Q)
    (h : QuotientGroup.mk' (center Q) x = QuotientGroup.mk' (center Q) y) :
    x ^ 2 = y ^ 2 := by
  have hm := QuotientGroup.eq.mp h
  have hc : Commute x (x⁻¹ * y) := mem_center_iff.mp hm x
  have hs : (x⁻¹ * y) ^ 2 = 1 :=
    congrArg Subtype.val (d.center_square ⟨x⁻¹ * y, hm⟩)
  simpa only [mul_inv_cancel_left, hs, mul_one] using (hc.mul_pow 2).symm

/-- Squaring on the central quotient, valued in the actual center. -/
public def square : Q ⧸ center Q → center Q :=
  Quotient.lift (fun x => ⟨x ^ 2, d.square_mem_center x⟩) (by
    intro x y h
    exact Subtype.ext (d.square_eq_of_quotient_eq x y (Quotient.sound h)))

@[simp] public theorem square_mk (x : Q) :
    (d.square (QuotientGroup.mk' (center Q) x) : Q) = x ^ 2 := by rfl

/-- The actual quotient action preserves the square map. -/
public theorem square_invariant (a : MulAut Q) (v : Q ⧸ center Q) :
    d.square (quotientAut (center Q) a v) = d.square v := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center Q) v
  apply Subtype.ext
  rw [quotientAut_apply_mk, d.square_mk, d.square_mk, ← map_pow]
  exact d.fixes_center a ⟨x ^ 2, d.square_mem_center x⟩

end QuaternionCentralProductData
end Subgroup
