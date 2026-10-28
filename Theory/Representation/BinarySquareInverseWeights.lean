module
public import Theory.Representation.SimpleHeadQuotient.DistinctPair
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Module.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Square and inverse weights over the binary field

The same field-unit group acts on two additive field lines, by square and
inverse scalar multiplication. Both binary representations are simple. Away
from field order four, for a nonbinary finite field, there are no nonzero
intertwiners in either direction, and the only invariant subgroups of field
order in their sum are its coordinate axes.

For the essential separation, a nonzero intertwiner gives
`f(b²) = b⁻¹ f(1)`. Additivity at `(a+1)²` forces `a²+a+1=0` for every
`a` other than zero and one. Thus every element is a root of `X⁴-X`, bounding
the field order by four. The distinct-simple-pair theorem supplies the
submodule classification. At field order four the two weights agree.

Source: the elementary scalar comparison underlying MS93 (3.7),
“Pushing up weak BN-pairs of rank two”, printed p.877. Identifying particular
source sections with these representations is a separate transport problem.
-/

@[expose] public section
open scoped CharTwo
open Polynomial
namespace Representation.BinarySquareInverseWeights
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem square_surjective : Function.Surjective (fun x : F => x ^ 2) :=
  Finite.surjective_of_injective CharTwo.sq_injective

theorem card_le_four_of_intertwiner (f : F →+ F) (hf : f ≠ 0)
    (he : ∀ a : Fˣ, ∀ x : F, f ((a : F)^2 * x) = (a : F)⁻¹ * f x) :
    Nat.card F ≤ 4 := by
  have hv (b : F) (hb : b ≠ 0) : f (b^2) = b⁻¹ * f 1 := by
    simpa using he (Units.mk0 b hb) 1
  have hc : f 1 ≠ 0 := by
    intro hc
    apply hf
    ext x
    obtain ⟨b,rfl⟩ := square_surjective x
    by_cases hb : b = 0
    · simp [hb]
    · simp [hv b hb, hc]
  have hquad (a : F) (ha : a ≠ 0) (ha1 : a ≠ 1) : a^2 + a + 1 = 0 := by
    have ha' : a + 1 ≠ 0 := fun hh => ha1 (CharTwo.add_eq_zero.mp hh)
    have hh : (a+1)⁻¹ * f 1 = a⁻¹ * f 1 + f 1 := by
      rw [←hv (a+1) ha', CharTwo.add_sq, map_add, hv a ha, one_pow]
    have hi : (a+1)⁻¹ = a⁻¹ + 1 :=
      mul_right_cancel₀ hc (by simpa [add_mul] using hh)
    have hi' : a = (1+a)*(a+1) := by
      field_simp at hi
      linear_combination hi
    have hz : a^2 + a + 1 = a - (1+a)*(a+1) := by
      simp only [CharTwo.sub_eq_add]
      ring_nf
      simp
    exact hz.trans (sub_eq_zero.mpr hi')
  have hpow (a : F) : a^4 - a = 0 := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases ha1 : a = 1
    · simp [ha1]
    have h := hquad a ha ha1
    calc
      a^4 - a = (a^2+a+1)*(a^2-a) := by ring
      _ = 0 := by rw [h, zero_mul]
  let := Fintype.ofFinite F
  have hne : (X^4-X : F[X]) ≠ 0 := by
    intro h
    have := congrArg (fun p : F[X] => p.coeff 4) h
    simp [coeff_X] at this
  have h := card_le_degree_of_subset_roots (p := (X^4-X : F[X]))
    (Z := Finset.univ) (fun x _ => (mem_roots hne).mpr (by simpa using hpow x))
  have hd : (X^4-X : F[X]).natDegree ≤ 4 := by
    exact (natDegree_sub_le _ _).trans (by simp)
  rw [Nat.card_eq_fintype_card]
  exact h.trans hd

theorem card_eq_four_of_intertwiner (hq : 2 < Nat.card F)
    (f : F →+ F) (hf : f ≠ 0)
    (he : ∀ a : Fˣ, ∀ x : F, f ((a : F)^2 * x) = (a : F)⁻¹ * f x) :
    Nat.card F = 4 := by
  have hb := card_le_four_of_intertwiner f hf he
  let := Fintype.ofFinite F
  obtain ⟨n, _, hn⟩ := FiniteField.card F 2
  have hd : 2 ∣ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self 2 n.ne_zero
  omega

variable [Algebra (ZMod 2) F]

noncomputable def scalar (w : Fˣ →* Fˣ) : Representation (ZMod 2) Fˣ F where
  toFun a := ((w a : F) • (LinearMap.id : F →ₗ[F] F)).restrictScalars (ZMod 2)
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp [mul_assoc]

omit [Finite F] [CharP F 2] in
@[simp] theorem scalar_apply (w : Fˣ →* Fˣ) (a : Fˣ) (x : F) :
    scalar w a x = (w a : F) * x := rfl

def squareWeight : Fˣ →* Fˣ where
  toFun a := a^2
  map_one' := one_pow 2
  map_mul' a b := mul_pow a b 2

def inverseWeight : Fˣ →* Fˣ where
  toFun a := a⁻¹
  map_one' := inv_one
  map_mul' := mul_inv

noncomputable abbrev square : Representation (ZMod 2) Fˣ F := scalar squareWeight
noncomputable abbrev inverse : Representation (ZMod 2) Fˣ F := scalar inverseWeight

omit [Finite F] [CharP F 2] in
@[simp] theorem square_apply (a : Fˣ) (x : F) : square a x = (a : F)^2 * x := by
  simp [square, scalar_apply, squareWeight]

omit [Finite F] [CharP F 2] in
@[simp] theorem inverse_apply (a : Fˣ) (x : F) : inverse a x = (a : F)⁻¹ * x := by
  simp [inverse, scalar_apply, inverseWeight]


omit [Finite F] [CharP F 2] in
theorem scalar_irreducible (w : Fˣ →* Fˣ) (hw : Function.Surjective w) :
    IsIrreducible (scalar w) := by
  refine ⟨fun U => ?_⟩
  by_cases hU : U = ⊥
  · exact Or.inl hU
  right
  have hn : U.toSubmodule ≠ ⊥ := fun hh => hU (Subrepresentation.toSubmodule_injective hh)
  obtain ⟨x,hx,hx0⟩ := U.toSubmodule.ne_bot_iff.mp hn
  apply top_unique
  intro y _
  by_cases hy : y = 0
  · rw [hy]; exact U.toSubmodule.zero_mem
  obtain ⟨a,ha⟩ := hw (Units.mk0 (y/x) (div_ne_zero hy hx0))
  have h := U.apply_mem_toSubmodule a hx
  change y ∈ U.toSubmodule
  simpa [scalar_apply, ha, hx0] using h

instance square_irreducible : IsIrreducible (square (F := F)) :=
  scalar_irreducible _ (Finite.surjective_of_injective (by
    intro a b hab
    apply Units.ext
    exact CharTwo.sq_injective (congrArg Units.val hab)))

instance inverse_irreducible : IsIrreducible (inverse (F := F)) :=
  scalar_irreducible _ (fun a => ⟨a⁻¹, inv_inv a⟩)

omit [Algebra (ZMod 2) F] in
theorem square_to_inverse_eq_zero (hq : 2 < Nat.card F) (h4 : Nat.card F ≠ 4)
    (f : F →+ F)
    (he : ∀ a : Fˣ, ∀ x : F, f ((a : F)^2 * x) = (a : F)⁻¹ * f x) : f = 0 := by
  by_contra hf
  exact h4 (card_eq_four_of_intertwiner hq f hf he)

theorem not_equiv (hq : 2 < Nat.card F) (h4 : Nat.card F ≠ 4) :
    ¬ Nonempty ((square (F := F)).Equiv inverse) := by
  rintro ⟨e⟩
  have hf := square_to_inverse_eq_zero hq h4 e.toIntertwiningMap.toLinearMap.toAddMonoidHom
    (fun a x => by
      have hh := LinearMap.congr_fun (e.isIntertwining' a) x
      simpa only [LinearMap.comp_apply, square_apply, inverse_apply, LinearMap.toAddMonoidHom_coe] using hh)
  have hz : e (1 : F) = 0 := congrArg (fun f : F →+ F => f 1) hf
  exact one_ne_zero (e.toLinearEquiv.injective (hz.trans e.map_zero.symm))

theorem inverse_to_square_eq_zero (hq : 2 < Nat.card F) (h4 : Nat.card F ≠ 4)
    (f : F →+ F)
    (he : ∀ a : Fˣ, ∀ x : F, f ((a : F)⁻¹ * x) = (a : F)^2 * f x) : f = 0 := by
  let φ : (inverse (F := F)).IntertwiningMap square :=
    (f.toZModLinearMap 2).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro a x
      simpa [inverse, square, scalar, inverseWeight, squareWeight] using he a x)
  rcases IsIrreducible.bijective_or_eq_zero φ with hφ | hφ
  · exact False.elim (not_equiv hq h4 ⟨(φ.ofBijective hφ).symm⟩)
  · ext x
    exact congrArg (fun φ => φ x) hφ

theorem submodules (hq : 2 < Nat.card F) (h4 : Nat.card F ≠ 4)
    (K : Submodule (ZMod 2) (F × F))
    (hK : ∀ a : Fˣ, ∀ x ∈ K, ((a : F)^2 * x.1, (a : F)⁻¹ * x.2) ∈ K) :
    K = ⊥ ∨ K = (⊤ : Submodule (ZMod 2) F).prod ⊥ ∨
      K = (⊥ : Submodule (ZMod 2) F).prod ⊤ ∨ K = ⊤ :=
  SimpleHeadQuotient.distinct_pair_submodules square inverse (not_equiv hq h4) K (by
    intro a x hx
    change ((square a) x.1, (inverse a) x.2) ∈ K
    simpa [square, inverse, scalar, squareWeight, inverseWeight] using hK a x hx)

theorem order_q_axes (hq : 2 < Nat.card F) (h4 : Nat.card F ≠ 4)
    (K : Submodule (ZMod 2) (F × F)) (hcard : Nat.card K = Nat.card F)
    (hK : ∀ a : Fˣ, ∀ x ∈ K, ((a : F)^2 * x.1, (a : F)⁻¹ * x.2) ∈ K) :
    K = (⊤ : Submodule (ZMod 2) F).prod ⊥ ∨
      K = (⊥ : Submodule (ZMod 2) F).prod ⊤ := by
  rcases submodules hq h4 K hK with rfl | h | h | rfl
  · have hb : Nat.card (⊥ : Submodule (ZMod 2) (F × F)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
    omega
  · exact Or.inl h
  · exact Or.inr h
  · have ht : Nat.card (⊤ : Submodule (ZMod 2) (F × F)) = Nat.card F * Nat.card F := by
      rw [Nat.card_congr (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) (F × F)) ≃ₗ[ZMod 2] (F × F)).toEquiv,
        Nat.card_prod]
    nlinarith

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
theorem weights_eq_of_card_four (h4 : Nat.card F = 4) (a : Fˣ) :
    (a : F)^2 = (a : F)⁻¹ := by
  have hh : a^3 = 1 := by
    have h := pow_card_eq_one' (x := a)
    simpa [Nat.card_units, h4] using h
  have hv : (a : F)^3 = 1 := congrArg Units.val hh
  exact eq_inv_of_mul_eq_one_left (by simpa [pow_succ] using hv)

omit [Finite F] [CharP F 2] in
theorem representations_eq_of_card_four (h4 : Nat.card F = 4) :
    square (F := F) = inverse := by
  ext a x
  simpa [squareWeight, inverseWeight] using congrArg (fun c : F => c * x) (weights_eq_of_card_four h4 a)

/-- Arbitrary additive subgroups need no extra defining-field scalar closure. -/
theorem order_q_addSubgroup_axes (hq : 2 < Nat.card F) (h4 : Nat.card F ≠ 4)
    (K : AddSubgroup (F × F)) (hcard : Nat.card K = Nat.card F)
    (hK : ∀ a : Fˣ, ∀ x ∈ K, ((a : F)^2 * x.1, (a : F)⁻¹ * x.2) ∈ K) :
    K = (⊤ : AddSubgroup F).prod ⊥ ∨ K = (⊥ : AddSubgroup F).prod ⊤ := by
  rcases order_q_axes hq h4 (K.toZModSubmodule 2) hcard hK with hk | hk
  · left
    exact congrArg Submodule.toAddSubgroup hk
  · right
    exact congrArg Submodule.toAddSubgroup hk
end Representation.BinarySquareInverseWeights
