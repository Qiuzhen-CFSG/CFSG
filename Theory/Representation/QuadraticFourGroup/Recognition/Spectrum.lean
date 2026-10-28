module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Sylow

/-!
# The element-order condition in quadratic four-group recognition

If every element has order two or odd order, every two-subgroup is elementary
abelian. More strongly, the full centralizer of any involution is elementary
abelian: an odd-order element commuting with that involution would give an
element of twice its order. Sylow maximality then identifies the full
centralizer with any Sylow two-subgroup containing the involution.

This fills the centralizer inference needed in GLS, volume 2, Theorem 25.14,
Step 3. The displayed `C_T(t) = T` in the transcription alone would not give
the full centralizer hypothesis of Burnside's characterization. The actual
recognition theorem and the derivation of the element-order condition from
the representation remain separate arguments.
-/

@[expose] public section

open Subgroup

namespace Theory.GroupTheory

/-- Every element has order two or odd order (including the identity). -/
def InvolutionOddSpectrum (G : Type*) [Group G] : Prop :=
  ∀ g : G, orderOf g = 2 ∨ Odd (orderOf g)

/-- The order condition is inherited by divisors. -/
theorem involution_or_odd_of_dvd {m n : ℕ} (hn : n = 2 ∨ Odd n) (hmn : m ∣ n) :
    m = 2 ∨ Odd m := by
  rcases hn with rfl | hn
  · rcases (Nat.dvd_prime Nat.prime_two).mp hmn with rfl | rfl
    · exact Or.inr (by decide)
    · exact Or.inl rfl
  · exact Or.inr (hn.of_dvd_nat hmn)

variable {G H : Type*} [Group G] [Group H]

/-- Surjective homomorphisms preserve the element-order condition. -/
theorem InvolutionOddSpectrum.of_surjective (hG : InvolutionOddSpectrum G)
    (f : G →* H) (hf : Function.Surjective f) : InvolutionOddSpectrum H := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact involution_or_odd_of_dvd (hG x) (orderOf_map_dvd f x)

/-- Subgroups inherit the element-order condition. -/
theorem InvolutionOddSpectrum.subgroup (hG : InvolutionOddSpectrum G) (K : Subgroup G) :
    InvolutionOddSpectrum K := by
  intro x
  simpa only [Subgroup.orderOf_coe] using hG (x : G)

private theorem elementary_of_order_dvd_two (h : ∀ x : G, orderOf x ∣ 2) :
    IsElementaryAbelian 2 G where
  toIsMulCommutative := IsMulCommutative.of_comm (fun x y =>
    (Commute.of_orderOf_dvd_two h x y).eq)
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    (fun x => orderOf_dvd_iff_pow_eq_one.mp (h x))

/-- A two-group with this spectrum is elementary abelian. -/
theorem InvolutionOddSpectrum.elementaryAbelian (hG : InvolutionOddSpectrum G)
    (hP : IsPGroup 2 G) : IsElementaryAbelian 2 G := by
  apply elementary_of_order_dvd_two
  intro x
  by_cases hx : x = 1
  · simp [hx]
  rcases hG x with he | ho
  · simp [he]
  · exact (ho.not_two_dvd_nat (hP.dvd_orderOf hx)).elim

/-- The full centralizer of an involution is elementary abelian. -/
theorem InvolutionOddSpectrum.centralizer_elementaryAbelian
    (hG : InvolutionOddSpectrum G) {t : G} (ht : orderOf t = 2) :
    IsElementaryAbelian 2 (centralizer ({t} : Set G)) := by
  apply elementary_of_order_dvd_two
  intro x
  rw [← Subgroup.orderOf_coe]
  rcases hG (x : G) with he | ho
  · simp [he]
  have hc : Commute t (x : G) :=
    (mem_centralizer_singleton_iff.mp x.property).symm
  have hprod : orderOf (t * (x : G)) = 2 * orderOf (x : G) := by
    simpa only [ht] using hc.orderOf_mul_eq_mul_orderOf_of_coprime
      (by simpa only [ht] using ho.coprime_two_left)
  rcases hG (t * (x : G)) with he | ho'
  · rw [hprod] at he
    have hx : orderOf (x : G) = 1 := by omega
    simp [hx]
  · rw [hprod] at ho'
    exact (ho'.not_two_dvd_nat (dvd_mul_right 2 _)).elim

/-- The full involution centralizer equals a Sylow subgroup containing it. -/
theorem InvolutionOddSpectrum.centralizer_eq_sylow
    (hG : InvolutionOddSpectrum G) (T : Sylow 2 G)
    {t : G} (htT : t ∈ T) (ht : t ≠ 1) :
    centralizer ({t} : Set G) = T := by
  let : IsElementaryAbelian 2 T := (hG.subgroup T).elementaryAbelian T.isPGroup'
  have htorder : orderOf t = 2 := by
    have htpow : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t htT
    exact orderOf_eq_prime htpow ht
  let : IsElementaryAbelian 2 (centralizer ({t} : Set G)) :=
    hG.centralizer_elementaryAbelian htorder
  apply T.is_maximal' (IsElementaryAbelian.isPGroup 2 _)
  intro x hx
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : T) ⟨t, htT⟩)

end Theory.GroupTheory

end
