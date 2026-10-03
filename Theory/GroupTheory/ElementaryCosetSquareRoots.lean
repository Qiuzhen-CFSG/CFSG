module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic

/-!
# Square roots in cosets of an elementary abelian two-subgroup

For an exponent-two subgroup F, the elements of mF with square m² are
precisely m C_F(m). Multiplication by m gives the explicit equivalence.
If the full root fiber in K is contained in the two distinct cosets mF and
m⁻¹F and m has fourth power one, its size is twice the centralizer size.
Automorphisms preserving F preserve these coset counts.

Source: the elementary counting step in D. Parrott,
*A characterization of the Tits' simple group* (1972), printed p.682.
The lemmas here do not require the additional structure of that example.
-/

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- An involutory right factor preserves the square exactly when it commutes. -/
public theorem mul_sq_eq_sq_iff_commute_of_sq_eq_one (m f : G) (hf : f ^ 2 = 1) :
    (m * f) ^ 2 = m ^ 2 ↔ Commute m f := by
  have hff : f * f = 1 := by simpa only [pow_two] using hf
  constructor
  · intro hh
    have hh' : f * m * f = m := mul_left_cancel (by
      simpa only [pow_two, mul_assoc] using hh)
    change m * f = f * m
    calc
      m * f = (f * m * f) * f := congrArg (fun x => x * f) hh'.symm
      _ = f * m := by rw [mul_assoc, hff, mul_one]
  · intro hh
    rw [hh.mul_pow, hf, mul_one]

/-- Translate roots in mF to the centralizer of m in F. -/
public def squareCosetEquivCentralizer (F : Subgroup G) [IsElementaryAbelian 2 F] (m : G) :
    {g : G // m⁻¹ * g ∈ F ∧ g ^ 2 = m ^ 2} ≃
      (F ⊓ centralizer ({m} : Set G) : Subgroup G) where
  toFun g := ⟨m⁻¹ * g, g.property.1, mem_centralizer_singleton_iff.mpr (by
    have hh := (mul_sq_eq_sq_iff_commute_of_sq_eq_one m (m⁻¹ * g)
      (elemPow_eq_one_of_isElementaryAbelian _ g.property.1)).mp
        (by simpa using g.property.2)
    exact hh.symm.eq)⟩
  invFun f := ⟨m * f, by simpa using f.property.1,
    (mul_sq_eq_sq_iff_commute_of_sq_eq_one m f
      (elemPow_eq_one_of_isElementaryAbelian _ f.property.1)).mpr
        (mem_centralizer_singleton_iff.mp f.property.2).symm⟩
  left_inv g := Subtype.ext (by simp)
  right_inv f := Subtype.ext (by simp)

/-- Count the roots of m² in the coset mF. -/
public theorem ncard_square_coset (F : Subgroup G) [IsElementaryAbelian 2 F] (m : G) :
    {g : G | m⁻¹ * g ∈ F ∧ g ^ 2 = m ^ 2}.ncard =
      Nat.card (F ⊓ centralizer ({m} : Set G) : Subgroup G) := by
  exact Nat.card_congr (squareCosetEquivCentralizer F m)

/-- The inverse coset has the same number of roots when m⁴ = 1. -/
public theorem ncard_square_inverse_coset (F : Subgroup G) [IsElementaryAbelian 2 F]
    (m : G) (hfour : m ^ 4 = 1) :
    {g : G | m * g ∈ F ∧ g ^ 2 = m ^ 2}.ncard =
      Nat.card (F ⊓ centralizer ({m} : Set G) : Subgroup G) := by
  have hi : (m⁻¹) ^ 2 = m ^ 2 := by
    rw [inv_pow]
    apply inv_eq_of_mul_eq_one_right
    simpa only [← pow_add] using hfour
  have hc : centralizer ({m⁻¹} : Set G) = centralizer ({m} : Set G) := by
    ext g
    simp only [mem_centralizer_singleton_iff]
    exact ⟨fun h => by simpa only [inv_inv] using (show Commute g m⁻¹ from h).inv_right.eq,
      fun h => (show Commute g m from h).inv_right.eq⟩
  simpa only [inv_inv, hi, hc] using ncard_square_coset F m⁻¹

/-- Two distinct root cosets give twice the elementary centralizer cardinality.
The covering hypothesis is separate from this counting argument. -/
public theorem ncard_square_roots_of_two_cosets [Finite G]
    (F K : Subgroup G) [IsElementaryAbelian 2 F]
    (hFK : F ≤ K) (m : G) (hm : m ∈ K) (hfour : m ^ 4 = 1)
    (hsq : m ^ 2 ∉ F)
    (hcover : ∀ g ∈ K, g ^ 2 = m ^ 2 → m⁻¹ * g ∈ F ∨ m * g ∈ F) :
    {g : G | g ∈ K ∧ g ^ 2 = m ^ 2}.ncard =
      2 * Nat.card (F ⊓ centralizer ({m} : Set G) : Subgroup G) := by
  let A : Set G := {g | m⁻¹ * g ∈ F ∧ g ^ 2 = m ^ 2}
  let B : Set G := {g | m * g ∈ F ∧ g ^ 2 = m ^ 2}
  have hAB : Disjoint A B := Set.disjoint_left.mpr (by
    rintro g ⟨hg, _⟩ ⟨hg', _⟩
    apply hsq
    have hh := F.mul_mem hg' (F.inv_mem hg)
    convert hh using 1
    simp only [pow_two]
    group)
  have heq : {g : G | g ∈ K ∧ g ^ 2 = m ^ 2} = A ∪ B := by
    ext g
    constructor
    · rintro ⟨hg, hg2⟩
      exact (hcover g hg hg2).imp (fun hh => ⟨hh, hg2⟩) (fun hh => ⟨hh, hg2⟩)
    · rintro (⟨hg, hg2⟩ | ⟨hg, hg2⟩)
      · exact ⟨by simpa using K.mul_mem hm (hFK hg), hg2⟩
      · exact ⟨by simpa using K.mul_mem (K.inv_mem hm) (hFK hg), hg2⟩
  rw [heq, Set.ncard_union_eq hAB]
  change {g : G | m⁻¹ * g ∈ F ∧ g ^ 2 = m ^ 2}.ncard +
    {g : G | m * g ∈ F ∧ g ^ 2 = m ^ 2}.ncard = _
  rw [ncard_square_coset, ncard_square_inverse_coset F m hfour, two_mul]
/-- An automorphism preserving F transports the root count in mF. -/
public theorem ncard_square_coset_mulEquiv (F : Subgroup G) (m : G) (φ : MulAut G)
    (hF : ∀ g : G, φ g ∈ F ↔ g ∈ F) :
    {g : G | (φ m)⁻¹ * g ∈ F ∧ g ^ 2 = (φ m) ^ 2}.ncard =
      {g : G | m⁻¹ * g ∈ F ∧ g ^ 2 = m ^ 2}.ncard := by
  symm
  apply Nat.card_congr
  exact φ.toEquiv.subtypeEquiv (fun g => by
    change (_ ∧ _) ↔ ((φ m)⁻¹ * φ g ∈ F ∧ (φ g) ^ 2 = (φ m) ^ 2)
    rw [← map_inv, ← map_mul, hF, ← map_pow, ← map_pow, φ.injective.eq_iff])
end Subgroup
