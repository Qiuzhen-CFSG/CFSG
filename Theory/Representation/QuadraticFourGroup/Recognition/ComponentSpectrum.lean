module

public import Theory.Representation.QuadraticFourGroup.Models
public import Theory.Representation.QuadraticFourGroup.Recognition.Spectrum

/-!
# From odd transpositions to the actual component quotient

For `x` in a subgroup `L` and `u` centralizing `L`, the order of `x Z(L)`
divides the order of `u x`: a power killing `u x` makes the corresponding
power of `x` central in `L`. Apply this to `u = a x⁻¹ a⁻¹`. Distinct
components `L` and `Lᵃ` commute, so the odd-transposition condition gives the
required element orders in the actual `L / Z(L)`.

Source: GLS, volume 2, Theorem 25.14, Step 3. This proves the quotient-order
inference, with the odd-transposition conclusion of Steps 1--2 still an
explicit input. It does not assert Burnside recognition.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- Multiplication by an element centralizing a subgroup cannot decrease
the order of an element modulo that subgroup's center except by divisibility. -/
theorem quotient_center_order_dvd_of_centralizer {L : Subgroup G}
    (x : L) {u : G} (hu : u ∈ centralizer (L : Set G)) :
    orderOf (QuotientGroup.mk' (center L) x) ∣ orderOf (u * (x : G)) := by
  let n := orderOf (u * (x : G))
  have hc : Commute u (x : G) :=
    (mem_centralizer_iff.mp hu (x : G) x.property).symm
  have hp : u ^ n * (x : G) ^ n = 1 := by
    rw [← hc.mul_pow]
    exact pow_orderOf_eq_one _
  have hxpow : (x : G) ^ n = (u ^ n)⁻¹ := by
    apply mul_left_cancel (a := u ^ n)
    rw [hp, mul_inv_cancel]
  apply orderOf_dvd_of_pow_eq_one
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff (x ^ n)).mpr
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  change (y : G) * (x : G) ^ n = (x : G) ^ n * (y : G)
  rw [hxpow]
  exact mem_centralizer_iff.mp
    ((centralizer (L : Set G)).inv_mem ((centralizer (L : Set G)).pow_mem hu n))
    y y.property

end Theory.GroupTheory

namespace Representation.QuadraticFourGroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}

/-- The conclusion of the odd-transposition argument, expressed for the
conjugacy class of the distinguished involution. -/
def HasOddTranspositions {G : Type*} [Group G] (a : G) : Prop :=
  ∀ x : G, orderOf (a * (x⁻¹ * a * x)) = 2 ∨ Odd (orderOf (a * (x⁻¹ * a * x)))

/-- Odd transpositions force the spectrum condition on the actual component quotient. -/
theorem Hypotheses.quotient_spectrum (h : Hypotheses ρ L B a)
    (hodd : HasOddTranspositions a) : InvolutionOddSpectrum (L ⧸ center L) := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center L) y
  have haa : a⁻¹ = a := by
    have ha2 : a ^ 2 = 1 := by rw [← h.involution]; exact pow_orderOf_eq_one _
    exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha2)
  have hu : a * (x : G)⁻¹ * a⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    have hx : a * (x : G)⁻¹ * a⁻¹ ∈ L.map (MulAut.conj a).toMonoidHom := by
      exact mem_map_of_mem (MulAut.conj a).toMonoidHom (L.inv_mem x.property)
    have hc' := commutator_eq_bot_iff_le_centralizer.mp
      ((commutator_comm _ _).trans h.commuting_conjugate)
    exact hc' hx
  have hd := quotient_center_order_dvd_of_centralizer x hu
  rw [haa] at hd
  have he : a * (x : G)⁻¹ * a * (x : G) = a * ((x : G)⁻¹ * a * (x : G)) := by group
  rw [he] at hd
  exact involution_or_odd_of_dvd (hodd x) hd

end Representation.QuadraticFourGroup

end
