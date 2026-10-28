module
public import Theory.SpecificGroups.PSL2.ThreeFiveInverters

/-!
# Cubic inversion bounds in odd PSL₂

Every involution in PSL₂(31) is conjugate to the reflector of the split
torus of order fifteen, so it inverts an element of order five. The
three-or-five inversion sieve therefore leaves only field order seven
when all inverted odd prime-power rotations have order three.

Source application: Aschbacher--Smith 8.2.9, printed p.720,
refs/quasithin.pdf; split torus reflection is Huppert II.8.3.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Theory.PSL2.CubicInverters

/-- A fixed involution in PSL₂(31) inverts an element of order five. -/
theorem exists_inverted_five_of_card_thirty_one
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 31)
    (t : PSL(2,F)) (ht : orderOf t = 2) :
    ∃ r : PSL(2,F), orderOf r = 5 ∧ t*r*t⁻¹ = r⁻¹ := by
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨U,w,hU,hcard,_,hw,hw2,hi,_,_⟩ :=
    BenderSuzuki.External.huppert_II_8_3_split_torus_reflection_data
      (by simpa only [pow_one] using hF : Nat.card F = 31^1)
  have hu : Nat.card U = 15 := by rw [hF] at hcard; norm_num at hcard; exact hcard
  obtain ⟨r,hr⟩ := exists_prime_orderOf_dvd_card' (G := U) 5 (by rw [hu]; decide)
  have hwc : orderOf w = 2 := orderOf_eq_prime (by simpa only [pow_two] using hw2)
    (fun he => hw (he ▸ U.one_mem))
  obtain ⟨c,hc⟩ := isConj_iff.mp (involutions_isConj w t hwc ht)
  let y : PSL(2,F) := c*(r : PSL(2,F))*c⁻¹
  refine ⟨y,?_,?_⟩
  · change orderOf (MulAut.conj c (r : PSL(2,F))) = 5
    rw [MulEquiv.orderOf_eq,Subgroup.orderOf_coe,hr]
  · rw [←hc]
    calc
      _ = c*(w*(r : PSL(2,F))*w⁻¹)*c⁻¹ := by dsimp [y]; group
      _ = c*(r : PSL(2,F))⁻¹*c⁻¹ := by rw [hi r r.property]
      _ = _ := by dsimp [y]; group

/-- Only the field of order seven survives a cubic-only rotation bound. -/
theorem field_card_eq_seven
    {F : Type*} [Field F] [Finite F] {p d : ℕ} [Fact p.Prime]
    (hp : 3<p) (hd : d=1 ∨ d=2) (hF : Nat.card F=p^d)
    (hmod : Nat.card F%8=1 ∨ Nat.card F%8=7)
    (t : PSL(2,F)) (ht : orderOf t=2)
    (hrot : ∀ r : PSL(2,F), t*r*t⁻¹=r⁻¹ → ∀ r₀ a : ℕ,
      r₀.Prime → r₀≠2 → 0<a → orderOf r=r₀^a → orderOf r=3) :
    Nat.card F=7 := by
  rcases ThreeFiveInverters.field_card_eq_seven_or_thirty_one hp hd hF hmod t ht
    (fun r hi p a hp hp2 ha hr => Or.inl (hrot r hi p a hp hp2 ha hr)) with h7 | h31
  · exact h7
  · obtain ⟨r,hr,hi⟩ := exists_inverted_five_of_card_thirty_one h31 t ht
    have hh := hrot r hi 5 1 (by decide) (by decide) (by decide) (by simpa only [pow_one] using hr)
    omega

end Theory.PSL2.CubicInverters
