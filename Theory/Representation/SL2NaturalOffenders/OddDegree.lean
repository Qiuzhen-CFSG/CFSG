module
public import Theory.Representation.SL2NaturalOffenders.PointwiseFixer
public import Theory.Representation.SL2NaturalOffenders.NaturalNormalizer
public import Theory.Representation.SL2NaturalOffenders.FieldAction.Basic
public import Theory.FieldTheory.FiniteAutomorphismOrder

/-!
# Two-elements in natural SL₂ normalizers over odd-degree fields

The coefficient homomorphism of a binary semilinear action takes values in
an automorphism group of order equal to the field degree. If that degree
is odd, every two-element has trivial coefficient action. Its determinant
is also trivial in characteristic two, so a faithful natural extension
places it in the original marked SL₂ layer.

The last theorem applies this argument to the full binary linear normalizer,
retaining the actual natural action. This is the odd-degree part of the
fixed-kernel calculation used in Aschbacher--Smith, 10.1.1(1) and 10.2.9,
printed pp.741 and750, using the natural normalizer calculation of B.4.2(1).
-/

public section
open Subgroup Representation.BinaryOffender
namespace Representation.SL2NaturalOffenders
variable {F H : Type*} [Field F] [Finite F] [CharP F 2] [Group H]
local instance oddDegreeBinaryAlgebra : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- A binary semilinear two-element is linear when the field degree is odd. -/
theorem linear_of_odd_field_degree
    {n : ℕ} (hn : Odd n) (hcard : Nat.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) H (Fin 2 → F))
    (hsemi : ∀ h : H, ∃ σ : F ≃+* F, ∀ c v, ρ h (c • v) = σ c • ρ h v)
    {a : H} (ha : ∃ k : ℕ, a ^ (2 ^ k) = 1) :
    ∀ (c : F) (v : Fin 2 → F), ρ a (c • v) = c • ρ a v := by
  apply (fieldAction_eq_one_iff ρ hsemi a).mp
  let σ := fieldAction ρ hsemi a
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun f : F ≃+* F => (f : F → F)) DFunLike.coe_injective
  have hd : orderOf σ ∣ n := (orderOf_dvd_natCard σ).trans
    (dvd_of_eq (FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hcard))
  obtain ⟨k,hk⟩ := ha
  have hp : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
    change fieldAction ρ hsemi a ^ (2 ^ k) = 1
    rw [← map_pow,hk,map_one])
  apply orderOf_eq_one_iff.mp
  have hh := Nat.dvd_gcd hd hp
  rw [(hn.coprime_two_right.pow_right k).gcd_eq_one] at hh
  exact Nat.dvd_one.mp hh

/-- All two-elements of a faithful natural extension lie in its marked
SL₂ layer when the defining field has odd degree. -/
theorem mem_layer_of_odd_field_degree
    {n : ℕ} (hn : Odd n) (hcard : Nat.card F = 2 ^ n)
    (L : Subgroup H) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (ρ : Representation (ZMod 2) H (Fin 2 → F)) (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v : Fin 2 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    {a : H} (ha : ∃ k : ℕ, a ^ (2 ^ k) = 1) : a ∈ L :=
  mem_of_linear_two_power_one L e ρ hfaith hnat ha
    (linear_of_odd_field_degree hn hcard ρ (normalizer_semilinear L e ρ hnat) ha)

/-- Two-elements in the full binary normalizer of the natural action lie
in its original SL₂ image over an odd-degree field. -/
theorem natural_normalizer_two_element_mem_layer
    {n : ℕ} (hn : Odd n) (hcard : Nat.card F = 2 ^ n)
    (a : linearNormalizer (SL2.BinarySmall.natural (K := F)))
    (ha : ∃ k : ℕ, a ^ (2 ^ k) = 1) :
    a ∈ (actionImage (SL2.BinarySmall.natural (K := F))).subgroupOf
      (linearNormalizer (SL2.BinarySmall.natural (K := F))) := by
  let σ := SL2.BinarySmall.natural (K := F)
  let N := linearNormalizer σ
  let L := (actionImage σ).subgroupOf N
  have hi : Function.Injective σ.asGroupHom := by
    intro x y h
    apply Subtype.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    exact congrArg (fun f => f.val v) h
  let E : Matrix.SpecialLinearGroup (Fin 2) F ≃* actionImage σ := MonoidHom.ofInjective hi
  let e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (subgroupOfEquivOfLe (actionImage σ).le_normalizer).trans E.symm
  let : L.Normal := normal_subgroupOf_of_le_normalizer (le_refl N)
  have hnat : ∀ (g : L) (v : Fin 2 → F), normalizerRepresentation σ (g : N) v =
      Matrix.mulVec (e g).val v := by
    intro g v
    have hh := E.apply_symm_apply ((subgroupOfEquivOfLe (actionImage σ).le_normalizer) g)
    exact (congrArg (fun x : actionImage σ => x.val.val v) hh).symm
  have hf : Function.Injective (normalizerRepresentation σ) := by
    intro x y h
    exact Subtype.ext (Units.ext h)
  exact mem_layer_of_odd_field_degree hn hcard L e _ hf hnat ha
end Representation.SL2NaturalOffenders
