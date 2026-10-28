module

public import Theory.SpecificGroups.C4SquareSignSwap
public import Theory.ElementaryAbelian.Basic

/-!
# An invariant elementary eight in the C₄-square inverter core

The four elementary eights containing the involutions in the abelian base are
indexed by the parities of the two coordinates of an outside involution. They
are normal in the inverter core. An automorphism whose square is inner and
which moves a central involution fixes one of these four eights. The finite
certificate below evaluates the action from the images of the three standard
generators; all checks are kernel-checked coordinate calculations.

Source: the order-64 specialization of Janko--Thompson, Math. Z. 113 (1970),
§§1.3--1.4, printed p. 386, used on p. 389.
-/

namespace C4SquareSignSwap

private abbrev K := inverterCore

private def eightMember (i j : Fin 2) (g : K) : Prop :=
  g.val.left.1.toAdd.val % 2 = (if g.val.right.1 = 1 then 0 else i.val) ∧
  g.val.left.2.toAdd.val % 2 = (if g.val.right.1 = 1 then 0 else j.val)

private instance (i j : Fin 2) (g : K) : Decidable (eightMember i j g) :=
  inferInstanceAs (Decidable (_ ∧ _))

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private def eight (i j : Fin 2) : Subgroup K where
  carrier := {g | eightMember i j g}
  one_mem' := by
    have h : ∀ i j : Fin 2, eightMember i j 1 := by decide +kernel
    exact h i j
  mul_mem' := by
    have h : ∀ i j : Fin 2, ∀ x y : K,
        eightMember i j x → eightMember i j y → eightMember i j (x * y) := by
      decide +kernel
    exact h i j
  inv_mem' := by
    have h : ∀ i j : Fin 2, ∀ x : K,
        eightMember i j x → eightMember i j x⁻¹ := by decide +kernel
    exact h i j

private instance (i j : Fin 2) : DecidablePred (· ∈ eight i j) :=
  fun g => inferInstanceAs (Decidable (eightMember i j g))

private theorem eight_normal (i j : Fin 2) : (eight i j).Normal := by
  have h : ∀ i j : Fin 2, ∀ x : K, x ∈ eight i j → ∀ g : K,
      g * x * g⁻¹ ∈ eight i j := by decide +kernel
  exact ⟨h i j⟩

private theorem eight_elementary (i j : Fin 2) : IsElementaryAbelian 2 (eight i j) := by
  have hcomm : ∀ i j : Fin 2, ∀ x y : K,
      x ∈ eight i j → y ∈ eight i j → x * y = y * x := by decide +kernel
  have hpow : ∀ i j : Fin 2, ∀ x : K, x ∈ eight i j → x ^ 2 = 1 := by
    decide +kernel
  exact { toIsMulCommutative := IsMulCommutative.of_comm
            (fun a b => Subtype.ext (hcomm i j a b a.property b.property))
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
            (fun a => Subtype.ext (hpow i j a a.property)) }

private theorem eight_card (i j : Fin 2) : Nat.card (eight i j) = 8 := by
  rw [Nat.card_eq_fintype_card]
  have h : ∀ i j : Fin 2, Fintype.card (eight i j) = 8 := by decide +kernel
  exact h i j

private def r₁ : K := ⟨rotation₁, rfl⟩
private def r₂ : K := ⟨rotation₂, rfl⟩
private def t₀ : K := ⟨inverter, rfl⟩

private theorem core_normal_form (g : K) :
    g = r₁ ^ g.val.left.1.toAdd.val * r₂ ^ g.val.left.2.toAdd.val *
      t₀ ^ g.val.right.1.toAdd.val := by
  have h : ∀ g : K,
      g = r₁ ^ g.val.left.1.toAdd.val * r₂ ^ g.val.left.2.toAdd.val *
        t₀ ^ g.val.right.1.toAdd.val := by decide +kernel
  exact h g

private def coreEval (a b t : K) (g : K) : K :=
  a ^ g.val.left.1.toAdd.val * b ^ g.val.left.2.toAdd.val *
    t ^ g.val.right.1.toAdd.val

private theorem coreEval_aut (f : MulAut K) (g : K) :
    coreEval (f r₁) (f r₂) (f t₀) g = f g := by
  calc
    coreEval (f r₁) (f r₂) (f t₀) g =
        f (r₁ ^ g.val.left.1.toAdd.val * r₂ ^ g.val.left.2.toAdd.val *
          t₀ ^ g.val.right.1.toAdd.val) := by
      simp [coreEval, map_mul, map_pow]
    _ = f g := by rw [← core_normal_form g]

private instance : DecidablePred (· ∈ Subgroup.center K) := fun z =>
  decidable_of_iff (∀ g : K, g * z = z * g) Subgroup.mem_center_iff.symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
set_option synthInstance.maxSize 4096 in
private theorem finite_selection : ∀ a b t : K,
    (a : Model) ∈ base → (b : Model) ∈ base → (t : Model) ∉ base →
    a ^ 2 ≠ 1 → b ^ 2 ≠ 1 → a ^ 2 ≠ b ^ 2 →
    (¬ ∀ z : K, z ∈ Subgroup.center K → z ^ 2 = 1 → coreEval a b t z = z) →
    (∀ i j : Fin 2, ∀ u : K, u ∈ eight i j →
      coreEval a b t (coreEval a b t u) ∈ eight i j) →
    ∃ i j : Fin 2, ∀ u : K, u ∈ eight i j → coreEval a b t u ∈ eight i j := by
  decide +kernel

private theorem order_four_in_base : ∀ g : K,
    g ^ 2 ≠ 1 → (g : Model) ∈ base := by decide +kernel

set_option synthInstance.maxSize 4096 in
private theorem outside_of_inverts_order_four : ∀ a t : K,
    (a : Model) ∈ base → a ^ 2 ≠ 1 → t * a * t⁻¹ = a⁻¹ →
      (t : Model) ∉ base := by decide +kernel

private theorem r₁_square_ne : r₁ ^ 2 ≠ 1 := by decide +kernel
private theorem r₂_square_ne : r₂ ^ 2 ≠ 1 := by decide +kernel
private theorem r₁_square_ne_r₂ : r₁ ^ 2 ≠ r₂ ^ 2 := by decide +kernel
private theorem t₀_inverts_r₁ : t₀ * r₁ * t₀⁻¹ = r₁⁻¹ := by decide +kernel

/-- An automorphism of the inverter core whose square is inner and which moves
a central involution preserves a normal elementary subgroup of order eight. -/
public theorem inverterCore_invariant_elementary_eight (f : MulAut inverterCore)
    (hsquare : ∃ c : inverterCore, ∀ x : inverterCore, f (f x) = c * x * c⁻¹)
    (hmove : ¬ ∀ z : inverterCore, z ∈ Subgroup.center inverterCore →
      z ^ 2 = 1 → f z = z) :
    ∃ U : Subgroup inverterCore, U.Normal ∧ IsElementaryAbelian 2 U ∧
      8 ≤ Nat.card U ∧ ∀ u ∈ U, f u ∈ U := by
  let a := f r₁
  let b := f r₂
  let t := f t₀
  have ha2 : a ^ 2 ≠ 1 := by
    intro h
    apply r₁_square_ne
    apply f.injective
    simpa only [map_pow, map_one] using h
  have hb2 : b ^ 2 ≠ 1 := by
    intro h
    apply r₂_square_ne
    apply f.injective
    simpa only [map_pow, map_one] using h
  have hab2 : a ^ 2 ≠ b ^ 2 := by
    intro h
    apply r₁_square_ne_r₂
    apply f.injective
    simpa only [map_pow] using h
  have haBase : (a : Model) ∈ base := order_four_in_base a ha2
  have hbBase : (b : Model) ∈ base := order_four_in_base b hb2
  have hta : t * a * t⁻¹ = a⁻¹ := by
    calc
      t * a * t⁻¹ = f (t₀ * r₁ * t₀⁻¹) := by simp [a, t]
      _ = a⁻¹ := by rw [t₀_inverts_r₁, map_inv]
  have htBase : (t : Model) ∉ base :=
    outside_of_inverts_order_four a t haBase ha2 hta
  have hmoveEval : ¬ ∀ z : K, z ∈ Subgroup.center K → z ^ 2 = 1 →
      coreEval a b t z = z := by
    intro h
    apply hmove
    intro z hz hz2
    rw [← coreEval_aut f]
    exact h z hz hz2
  obtain ⟨c, hc⟩ := hsquare
  have hsq : ∀ i j : Fin 2, ∀ u : K, u ∈ eight i j →
      coreEval a b t (coreEval a b t u) ∈ eight i j := by
    intro i j u hu
    simpa only [a, b, t, coreEval_aut, hc] using
      (eight_normal i j).conj_mem u hu c
  obtain ⟨i, j, hstable⟩ := finite_selection a b t
    haBase hbBase htBase ha2 hb2 hab2 hmoveEval hsq
  refine ⟨eight i j, eight_normal i j, eight_elementary i j, ?_, ?_⟩
  · rw [eight_card]
  · intro u hu
    simpa only [a, b, t, coreEval_aut] using hstable u hu

end C4SquareSignSwap
