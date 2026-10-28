module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.LowRows.Reduction
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# The actual factors of the terminal prime-product row

In F.6.18(3), the prime-field PSL₂ factor is simple and perfect, while the
cubic factor is abelian. The multiplication-compatible product therefore
identifies the first factor with the derived subgroup of the ambient
two-residual. In particular it is normal in the original ambient group.
The specified outer element cannot lie in that residual. The order formula
also supplies the prime divisor and the factor four needed for comparison
with the actual Sylow subgroup.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.6.17–18,
printed pp.309–310; terminal comparison on printed p.1155. The perfectness
argument uses Mathlib's PSL₂ transvection calculation.
-/

public section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
namespace LowRows.PrimeProduct
variable {D : Type*} [Group D] {S : Sylow 2 D} (c : FSource.ProductRow S)

/-- The source parameter is a prime field, not a proper extension. -/
theorem field_card : Nat.card c.field.Carrier = c.field.prime := by
  rw [c.field.card, c.degree, pow_one]

/-- Both retained congruences force a prime at least eleven. -/
theorem prime_lower : 11 ≤ c.field.prime := by have := c.congruence; omega

/-- The field in the product row has odd order. -/
theorem field_odd : Odd (Nat.card c.field.Carrier) := by
  rw [field_card c, Nat.odd_iff]
  have := c.congruence
  omega

/-- Simplicity of the actual first factor, through its PSL₂ equivalence. -/
theorem first_simple : IsSimpleGroup c.first := by
  let : IsSimpleGroup PSL(2,c.field.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [field_card c]; have := prime_lower c; omega)
  exact c.firstEquiv.isSimpleGroup

/-- Perfectness of the same embedded first factor. -/
theorem first_perfect : Group.IsPerfect c.first := by
  have hlarge : 4 ≤ Nat.card c.field.Carrier := by rw [field_card c]; have := prime_lower c; omega
  obtain ⟨x, hx⟩ : IsCyclic c.field.Carrierˣ := inferInstance
  have hF : ∃ a : c.field.Carrier, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
    refine ⟨x, Units.ne_zero x, fun h => ?_⟩
    have hb := orderOf_le_of_pow_eq_one zero_lt_two (Units.ext h)
    rw [orderOf_eq_card_of_forall_mem_zpowers hx, Nat.card_units] at hb
    omega
  let : Group.IsPerfect PSL(2,c.field.Carrier) := ⟨SL2Simple.PSL_commutator_eq_top hF⟩
  exact Group.IsPerfect.ofSurjective (f := c.firstEquiv.symm.toMonoidHom) c.firstEquiv.symm.surjective

/-- The actual cubic factor is abelian. -/
theorem second_commutative : IsMulCommutative c.second :=
  ⟨⟨fun a b => c.secondEquiv.injective (by simp only [map_mul, mul_comm])⟩⟩

/-- Multiplication compatibility proves commutation of the embedded factors. -/
theorem first_commutes_second (a : c.first) (b : c.second) :
    (a : D) * b = b * a := by
  have h : (a, (1 : c.second)) * (1, b) = (1, b) * (a, 1) := by simp
  have hh := congrArg (fun x => (c.product x : D)) h
  simpa only [map_mul, Subgroup.coe_mul, c.product_apply, Subgroup.coe_one, mul_one, one_mul] using hh

/-- The first factor is the derived subgroup of the actual ambient two-residual. -/
theorem residual_commutator : ⁅pResidual 2 D, pResidual 2 D⁆ = c.first := by
  let : Group.IsPerfect c.first := first_perfect c
  let : IsMulCommutative c.second := second_commutative c
  let f : c.first × c.second →* D := (c.first ⊔ c.second).subtype.comp c.product.toMonoidHom
  have hf : f.range = c.first ⊔ c.second := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩; exact (c.product y).property
    · intro hx
      obtain ⟨y, hy⟩ := c.product.surjective ⟨x,hx⟩
      exact ⟨y, congrArg Subtype.val hy⟩
  have hc : _root_.commutator (c.first × c.second) =
      (⊤ : Subgroup c.first).prod (⊥ : Subgroup c.second) := by
    change ⁅⊤, ⊤⁆ = _
    rw [← Subgroup.top_prod_top, commutator_prod_prod]
    change (_root_.commutator c.first).prod (_root_.commutator c.second) = _
    rw [Group.IsPerfect.commutator_eq_top, (commutator_eq_bot_iff c.second).mpr inferInstance]
  rw [c.residual, ← hf, ← map_commutator_eq _ f, hc]
  ext x
  constructor
  · rintro ⟨⟨a,b⟩, ⟨_,hb⟩, rfl⟩
    have hb1 : b = 1 := hb
    change (c.product (a,b) : D) ∈ c.first
    rw [c.product_apply, hb1, Subgroup.coe_one, mul_one]
    exact a.property
  · intro hx
    refine ⟨(⟨x,hx⟩,1), ⟨mem_top _, mem_bot.mpr rfl⟩, ?_⟩
    change (c.product (⟨x,hx⟩,1) : D) = x
    rw [c.product_apply, Subgroup.coe_one, mul_one]

/-- The residual identity implies ambient normality, with no extra premise. -/
theorem first_normal : c.first.Normal := by
  rw [← residual_commutator c]
  infer_instance

private theorem conjugate_of_mem_residual {x : D} (hx : x ∈ pResidual 2 D) :
    ∃ a : c.first, ∀ k : c.first, x * k * x⁻¹ = (a * k * a⁻¹ : c.first) := by
  obtain ⟨⟨a,b⟩, hab⟩ := c.product.surjective ⟨x, c.residual ▸ hx⟩
  have he : x = (a : D) * b := (congrArg Subtype.val hab).symm.trans (c.product_apply a b)
  refine ⟨a, fun k => ?_⟩
  rw [he]
  calc
    ((a : D) * b) * k * ((a : D) * b)⁻¹ = a * ((b : D) * k) * (b : D)⁻¹ * (a : D)⁻¹ := by group
    _ = a * ((k : D) * b) * (b : D)⁻¹ * (a : D)⁻¹ := by rw [first_commutes_second c k b]
    _ = (a * k * a⁻¹ : c.first) := by simp [mul_assoc]

/-- The specified outer automorphism separates its element from the residual. -/
theorem outer_element_not_mem_residual : c.element ∉ pResidual 2 D := by
  intro hx
  obtain ⟨a,ha⟩ := conjugate_of_mem_residual c hx
  obtain ⟨α,hα,hout⟩ := c.firstOuter
  apply hout
  refine ⟨a, ?_⟩
  ext k
  exact (ha k).symm.trans (hα k).symm

/-- The defining prime divides the actual first factor. -/
theorem prime_dvd_first_card : c.field.prime ∣ Nat.card c.first := by
  have hp := c.field.prime_isPrime
  have h := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (field_odd c)
  rw [field_card c, ← Nat.card_congr c.firstEquiv.toEquiv] at h
  have hd : c.field.prime ∣ Nat.card c.first * 2 := by rw [h]; exact dvd_mul_right _ _
  exact (hp.dvd_mul.mp hd).resolve_right (by intro h; have := Nat.le_of_dvd (by decide : 0 < 2) h; have := prime_lower c; omega)

/-- Four divides the actual first factor; no model Sylow identification is needed. -/
theorem four_dvd_first_card : 4 ∣ Nat.card c.first := by
  have h := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (field_odd c)
  rw [field_card c, ← Nat.card_congr c.firstEquiv.toEquiv] at h
  have hp : c.field.prime % 8 = 3 ∨ c.field.prime % 8 = 5 := by have := c.congruence; omega
  have hs : (c.field.prime ^ 2 - 1) % 8 = 0 := by
    have he : c.field.prime ^ 2 % 8 = 1 := by
      rw [Nat.pow_mod]
      rcases hp with hp | hp <;> rw [hp]
    omega
  have hd : 8 ∣ Nat.card c.first * 2 := by
    rw [h]
    exact dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero hs) _
  obtain ⟨k,hk⟩ := hd
  exact ⟨k, by omega⟩

end LowRows.PrimeProduct
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
