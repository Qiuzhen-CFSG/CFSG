module

public import Theory.GroupTheory.SpecificGroups.QuaternionEightInvolution
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic.DeriveFintype

/-!
# An explicit model of Q₈ ◦ C₄

The normal forms are `q rᵇ`, where `q ∈ Q₈`, `b ∈ {0,1}`, `r` is central,
and `r²` is the quaternion involution. The carry in multiplication identifies
the two involutions. This gives actual injective factor homomorphisms, with
intersection of order two, and a surjection onto the central quotient C₂².
All finite tables are checked by the kernel.

Quaternion automorphisms extend by fixing `r`; the extension is a faithful
homomorphism into the automorphism group of the central product. In particular
the explicit cubic automorphism retains its action on the group and on C₂².

Source: the elementary central-product calculation used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 14.2.21, printed p.988.
-/

@[expose] public section

namespace QuaternionCyclic

/-- Normal forms `q rᵇ` for the central product Q₈ ◦ C₄. -/
@[ext] structure Model where
  quaternion : QuaternionGroup 2
  odd : Bool
  deriving DecidableEq, Fintype

/-- The shared involution in quaternion coordinates. -/
def z : QuaternionGroup 2 := QuaternionGroup.a 2

instance : One Model := ⟨⟨1, false⟩⟩
instance : Mul Model := ⟨fun x y =>
  ⟨x.quaternion * y.quaternion * (if x.odd && y.odd then z else 1),
    xor x.odd y.odd⟩⟩
instance : Inv Model := ⟨fun x =>
  ⟨x.quaternion⁻¹ * (if x.odd then z else 1), x.odd⟩⟩

set_option maxRecDepth 10000 in
instance : Group Model where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide

/-- The quaternion factor, with its actual inclusion. -/
def quaternionEmbedding : QuaternionGroup 2 →* Model where
  toFun q := ⟨q, false⟩
  map_one' := rfl
  map_mul' := by decide

def cyclicMap (n : Multiplicative (ZMod 4)) : Model :=
  ⟨QuaternionGroup.a (if n.toAdd.val < 2 then 0 else 2), n.toAdd.val % 2 = 1⟩

/-- The central cyclic factor, with its actual inclusion. -/
def cyclicEmbedding : Multiplicative (ZMod 4) →* Model where
  toFun := cyclicMap
  map_one' := by decide
  map_mul' := by decide

/-- The central generator of order four. -/
def r : Model := cyclicEmbedding (Multiplicative.ofAdd 1)

theorem quaternionEmbedding_injective : Function.Injective quaternionEmbedding := by decide
theorem cyclicEmbedding_injective : Function.Injective cyclicEmbedding := by decide

theorem card_model : Nat.card Model = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem r_sq : r ^ 2 = quaternionEmbedding z := by decide
theorem r_order : orderOf r = 4 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) (by decide)
  intro p hp hd
  have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from hd))
  subst p
  decide
theorem shared_involution : cyclicEmbedding (Multiplicative.ofAdd 2) =
    quaternionEmbedding z := by decide

theorem normal_form (x : Model) : x = quaternionEmbedding x.quaternion *
    cyclicEmbedding (if x.odd then Multiplicative.ofAdd 1 else 1) := by
  have h : ∀ x : Model, x = quaternionEmbedding x.quaternion *
      cyclicEmbedding (if x.odd then Multiplicative.ofAdd 1 else 1) := by decide
  exact h x

theorem factors_commute (q : QuaternionGroup 2) (c : Multiplicative (ZMod 4)) :
    quaternionEmbedding q * cyclicEmbedding c =
      cyclicEmbedding c * quaternionEmbedding q := by
  have h : ∀ q : QuaternionGroup 2, ∀ c : Multiplicative (ZMod 4),
      quaternionEmbedding q * cyclicEmbedding c =
        cyclicEmbedding c * quaternionEmbedding q := by decide
  exact h q c

theorem factors_generate : quaternionEmbedding.range ⊔ cyclicEmbedding.range = ⊤ := by
  apply top_unique
  intro x _
  rw [normal_form x]
  exact (quaternionEmbedding.range ⊔ cyclicEmbedding.range).mul_mem
    (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right ⟨_, rfl⟩)

theorem mem_factor_intersection (x : Model) :
    x ∈ quaternionEmbedding.range ⊓ cyclicEmbedding.range ↔
      x = 1 ∨ x = quaternionEmbedding z := by
  have h : ∀ x : Model, (∃ q, quaternionEmbedding q = x) ∧
      (∃ c, cyclicEmbedding c = x) ↔ x = 1 ∨ x = quaternionEmbedding z := by decide
  exact h x

theorem card_factor_intersection :
    Nat.card (quaternionEmbedding.range ⊓ cyclicEmbedding.range : Subgroup Model) = 2 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight mem_factor_intersection),
    Nat.card_eq_fintype_card]
  decide

theorem center_eq_cyclic : Subgroup.center Model = cyclicEmbedding.range := by
  ext x
  change (x ∈ Subgroup.center Model) ↔ ∃ c, cyclicEmbedding c = x
  rw [Subgroup.mem_center_iff]
  have h : ∀ x : Model, (∀ y : Model, y * x = x * y) ↔
      ∃ c, cyclicEmbedding c = x := by decide
  exact h x

/-- A group-invariant description of the quaternion factor. -/
theorem mem_quaternion_iff (x : Model) : x ∈ quaternionEmbedding.range ↔
    x = 1 ∨ x = quaternionEmbedding z ∨
      (x ^ 2 ≠ 1 ∧ x ∉ Subgroup.center Model) := by
  have h : ∀ x : Model, (∃ q, quaternionEmbedding q = x) ↔
      x = 1 ∨ x = quaternionEmbedding z ∨
        (x ^ 2 ≠ 1 ∧ ¬ ∀ y : Model, y * x = x * y) := by decide
  simpa only [Subgroup.mem_center_iff, MonoidHom.mem_range] using h x

/-- Every nontrivial square is the shared involution. -/
theorem square_eq_involution (x : Model) (hx : x ^ 2 ≠ 1) :
    x ^ 2 = quaternionEmbedding z := by
  have h : ∀ x : Model, x ^ 2 ≠ 1 → x ^ 2 = quaternionEmbedding z := by decide
  exact h x hx

/-- Coordinates on the actual quotient by the center. -/
abbrev CentralQuotient := Multiplicative (ZMod 2 × ZMod 2)

def quotientMap (x : Model) : CentralQuotient :=
  Multiplicative.ofAdd (match x.quaternion with
  | .a i => ((i.val : ZMod 2), 0)
  | .xa i => ((i.val : ZMod 2), 1))

/-- The central quotient map; its kernel is exactly the cyclic factor. -/
def centralQuotient : Model →* CentralQuotient where
  toFun := quotientMap
  map_one' := by decide
  map_mul' := by decide

theorem centralQuotient_surjective : Function.Surjective centralQuotient := by decide

theorem centralQuotient_ker : centralQuotient.ker = Subgroup.center Model := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  have h : ∀ x : Model, centralQuotient x = 1 ↔
      ∀ y : Model, y * x = x * y := by decide
  exact h x

private theorem quaternion_aut_fixes_z (e : MulAut (QuaternionGroup 2)) : e z = z := by
  apply QuaternionGroup.eq_a_two_of_orderOf_eq_two
  rw [e.orderOf_eq]
  exact orderOf_eq_prime (by decide : z ^ 2 = 1) (by decide : z ≠ 1)

/-- Extend a quaternion automorphism by fixing the central generator. -/
def extendAut (e : MulAut (QuaternionGroup 2)) : MulAut Model where
  toFun x := ⟨e x.quaternion, x.odd⟩
  invFun x := ⟨e.symm x.quaternion, x.odd⟩
  left_inv x := by cases x; simp
  right_inv x := by cases x; simp
  map_mul' x y := by
    apply Model.ext
    · change e (x.quaternion * y.quaternion * _) =
        e x.quaternion * e y.quaternion * _
      rw [map_mul, map_mul]
      split <;> simp [quaternion_aut_fixes_z]
    · rfl

/-- The extension respects composition, so it retains the full action map. -/
def extendAutHom : MulAut (QuaternionGroup 2) →* MulAut Model where
  toFun := extendAut
  map_one' := by ext x <;> rfl
  map_mul' e f := by ext x <;> rfl

theorem extendAut_quaternion (e : MulAut (QuaternionGroup 2)) (q : QuaternionGroup 2) :
    extendAut e (quaternionEmbedding q) = quaternionEmbedding (e q) := rfl

theorem extendAut_cyclic (e : MulAut (QuaternionGroup 2)) (c : Multiplicative (ZMod 4)) :
    extendAut e (cyclicEmbedding c) = cyclicEmbedding c := by
  apply Model.ext
  · change e (QuaternionGroup.a (if c.toAdd.val < 2 then 0 else 2)) =
      QuaternionGroup.a (if c.toAdd.val < 2 then 0 else 2)
    split
    · exact map_one e
    · exact quaternion_aut_fixes_z e
  · rfl

theorem extendAutHom_injective : Function.Injective extendAutHom := by
  intro e f h
  apply MulEquiv.ext
  intro q
  have hh := congrArg (fun a : MulAut Model => (a (quaternionEmbedding q)).quaternion) h
  exact hh

/-- Quaternion inner automorphisms extend to the corresponding inner actions. -/
theorem extendAut_conj (q : QuaternionGroup 2) :
    extendAut (MulAut.conj q) = MulAut.conj (quaternionEmbedding q) := by
  have h : ∀ q : QuaternionGroup 2, ∀ x : Model,
      extendAut (MulAut.conj q) x = MulAut.conj (quaternionEmbedding q) x := by decide
  apply MulEquiv.ext
  intro x
  exact h q x

/-- The central coordinate has no effect on an inner automorphism. -/
theorem conj_eq_extendAut (x : Model) :
    MulAut.conj x = extendAut (MulAut.conj x.quaternion) := by
  have h : ∀ x y : Model,
      MulAut.conj x y = extendAut (MulAut.conj x.quaternion) y := by decide
  apply MulEquiv.ext
  intro y
  exact h x y

theorem inner_range_eq_map : (MulAut.conj : Model →* MulAut Model).range =
    (MulAut.conj : QuaternionGroup 2 →* MulAut (QuaternionGroup 2)).range.map
      extendAutHom := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨MulAut.conj x.quaternion, ⟨x.quaternion, rfl⟩, (conj_eq_extendAut x).symm⟩
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨quaternionEmbedding q, (extendAut_conj q).symm⟩

/-- The isomorphism induced by the specified central quotient map. -/
noncomputable def centralQuotientEquiv :
    Model ⧸ Subgroup.center Model ≃* CentralQuotient :=
  (QuotientGroup.quotientMulEquivOfEq centralQuotient_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective centralQuotient centralQuotient_surjective)

theorem centralQuotientEquiv_mk (x : Model) :
    centralQuotientEquiv (QuotientGroup.mk' (Subgroup.center Model) x) =
      centralQuotient x := rfl

/-- The quaternion cubic cycles `i`, `j`, and `ij`. -/
def quaternionCubicMap : QuaternionGroup 2 → QuaternionGroup 2
  | .a i => (QuaternionGroup.xa 0) ^ i.val
  | .xa i => QuaternionGroup.xa 3 * (QuaternionGroup.xa 0) ^ i.val

def quaternionCubic : MulAut (QuaternionGroup 2) where
  toFun := quaternionCubicMap
  invFun x := quaternionCubicMap (quaternionCubicMap x)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

/-- The corresponding cubic action on the central product fixes C₄ pointwise. -/
def cubic : MulAut Model := extendAut quaternionCubic

theorem quaternionCubic_cube : quaternionCubic ^ 3 = 1 := by
  ext x
  have h : ∀ x : QuaternionGroup 2, quaternionCubic (quaternionCubic
      (quaternionCubic x)) = x := by decide
  exact h x

theorem cubic_cube : cubic ^ 3 = 1 := by
  change extendAutHom quaternionCubic ^ 3 = 1
  rw [← map_pow, quaternionCubic_cube, map_one]

theorem cubic_ne_one : cubic ≠ 1 := by
  intro h
  have hh := DFunLike.congr_fun h (quaternionEmbedding (QuaternionGroup.a 1))
  exact (by decide : cubic (quaternionEmbedding (QuaternionGroup.a 1)) ≠
    quaternionEmbedding (QuaternionGroup.a 1)) hh

theorem cubic_order : orderOf cubic = 3 := orderOf_eq_prime cubic_cube cubic_ne_one

theorem cubic_fixes_cyclic (c : Multiplicative (ZMod 4)) :
    cubic (cyclicEmbedding c) = cyclicEmbedding c := extendAut_cyclic _ _

/-- The quotient action `(a,b) ↦ (b,a+b)` of the cubic. -/
def cubicQuotient : MulAut CentralQuotient where
  toFun x := Multiplicative.ofAdd (x.toAdd.2, x.toAdd.1 + x.toAdd.2)
  invFun x := Multiplicative.ofAdd (x.toAdd.1 + x.toAdd.2, x.toAdd.1)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

theorem cubic_centralQuotient (x : Model) :
    centralQuotient (cubic x) = cubicQuotient (centralQuotient x) := by
  have h : ∀ x : Model,
      centralQuotient (cubic x) = cubicQuotient (centralQuotient x) := by decide
  exact h x

theorem cubicQuotient_fixed (x : CentralQuotient) (hx : cubicQuotient x = x) : x = 1 := by
  have h : ∀ x : CentralQuotient, cubicQuotient x = x → x = 1 := by decide
  exact h x hx

theorem cubic_fixed_iff (x : Model) : cubic x = x ↔ x ∈ Subgroup.center Model := by
  rw [Subgroup.mem_center_iff]
  have h : ∀ x : Model, cubic x = x ↔ ∀ y : Model, y * x = x * y := by decide
  exact h x

end QuaternionCyclic

end
