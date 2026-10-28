module
public import Theory.Mathieu.M23.Properties.Automorphisms
public import Theory.Mathieu.M23.Properties.Order
public import Theory.PGroupCore
/-!
# Two-group actors on the actual Mathieu group M₂₃

Every automorphism of the concrete M₂₃ carrier is inner. Its automorphism
order therefore divides 10200960, whose two-part is 128. The resulting bound
applies to any faithful two-group actor and to its original target marking.
It supplies the size estimate for the root-projection kernel in the terminal
Suzuki argument of Aschbacher–Smith 13.6.27, printed pp.934–935.
-/
public section
namespace Sporadic.Mathieu

/-- Innerness bounds the full automorphism order by the actual group order. -/
theorem m23_automorphism_card_dvd : Nat.card (MulAut M23) ∣ 10200960 := by
  rw [← m23_order]
  exact Subgroup.card_dvd_of_surjective (MulAut.conj : M23 →* MulAut M23)
    m23_conj_surjective

/-- An injective two-group actor has order dividing 128. -/
theorem m23_twoGroup_card_dvd_128_of_injective {A : Type*} [Group A]
    (hA : IsPGroup 2 A) (f : A →* MulAut M23) (hf : Function.Injective f) :
    Nat.card A ∣ 128 := by
  let : Finite A := Finite.of_injective f hf
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hd := (Subgroup.card_dvd_of_injective f hf).trans m23_automorphism_card_dvd
  have hb : n ≤ 7 := by
    by_contra hb
    have h256 : 256 ∣ Nat.card A := by
      rw [hn]
      exact Nat.pow_dvd_pow 2 (by omega : 8 ≤ n)
    have := h256.trans hd
    norm_num at this
  rw [hn]
  exact Nat.pow_dvd_pow 2 hb

/-- The full original two-group actor has order at most 128. -/
theorem m23_twoGroup_card_le_128_of_injective {A : Type*} [Group A]
    (hA : IsPGroup 2 A) (f : A →* MulAut M23) (hf : Function.Injective f) :
    Nat.card A ≤ 128 :=
  Nat.le_of_dvd (by decide) (m23_twoGroup_card_dvd_128_of_injective hA f hf)

/-- Transport a component marking while keeping the same acting group. -/
theorem m23_twoGroup_card_le_128_of_equiv {A K : Type*} [Group A] [Group K]
    (e : K ≃* M23) (hA : IsPGroup 2 A)
    (f : A →* MulAut K) (hf : Function.Injective f) : Nat.card A ≤ 128 :=
  m23_twoGroup_card_le_128_of_injective hA ((MulAut.congr e).toMonoidHom.comp f)
    ((MulAut.congr e).injective.comp hf)

end Sporadic.Mathieu
