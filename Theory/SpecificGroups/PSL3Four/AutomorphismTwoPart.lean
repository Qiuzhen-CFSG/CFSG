module
public import Theory.SpecificGroups.PSL3Four.OuterThreeStructure
/-!
# Two-group actors on the actual PSL₃(4)

The inner automorphism order divides 20160 and the outer order divides twelve.
Thus the full automorphism order divides 241920, whose two-part is 256.
An injective two-group actor, including the literal root-projection kernel in
13.6.27's terminal Suzuki argument, consequently has order at most 256.
The marking adapter preserves the original actor and homomorphism.

Source: Aschbacher–Smith 13.6.27, printed pp.934–935; the actual outer
calculation is proved in `OuterThreeStructure`.
-/
public section
namespace Matrix.PSL3Four
open Subgroup

/-- The full automorphism order divides the inner order times twelve. -/
theorem automorphism_card_dvd : Nat.card (MulAut PSL) ∣ 241920 := by
  have hi : Nat.card (MulAut.innerSubgroup PSL) ∣ 20160 := by
    change Nat.card (MulAut.conj : PSL →* MulAut PSL).range ∣ 20160
    rw [← card_PSL]
    exact card_dvd_of_surjective (MulAut.conj : PSL →* MulAut PSL).rangeRestrict
      (MulAut.conj : PSL →* MulAut PSL).rangeRestrict_surjective
  have ho := OuterThreeStructure.outer_card_dvd_twelve
  have hc := (MulAut.innerSubgroup PSL).card_mul_index
  rw [← hc]
  exact Nat.mul_dvd_mul hi ho

/-- An injective two-group actor has order dividing the full two-part. -/
theorem twoGroup_card_dvd_256_of_injective {A : Type*} [Group A]
    (hA : IsPGroup 2 A) (f : A →* MulAut PSL) (hf : Function.Injective f) :
    Nat.card A ∣ 256 := by
  let : Finite A := Finite.of_injective f hf
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hd := (card_dvd_of_injective f hf).trans automorphism_card_dvd
  have hb : n ≤ 8 := by
    by_contra hb
    have h512 : 512 ∣ Nat.card A := by
      rw [hn]
      exact Nat.pow_dvd_pow 2 (by omega : 9 ≤ n)
    have := h512.trans hd
    norm_num at this
  rw [hn]
  exact Nat.pow_dvd_pow 2 hb

/-- The original two-group actor has order at most 256. -/
theorem twoGroup_card_le_256_of_injective {A : Type*} [Group A]
    (hA : IsPGroup 2 A) (f : A →* MulAut PSL) (hf : Function.Injective f) :
    Nat.card A ≤ 256 :=
  Nat.le_of_dvd (by decide) (twoGroup_card_dvd_256_of_injective hA f hf)

/-- Transport the target marking without replacing the acting group by an image. -/
theorem twoGroup_card_le_256_of_equiv {A K : Type*} [Group A] [Group K]
    (e : K ≃* PSL) (hA : IsPGroup 2 A)
    (f : A →* MulAut K) (hf : Function.Injective f) : Nat.card A ≤ 256 :=
  twoGroup_card_le_256_of_injective hA ((MulAut.congr e).toMonoidHom.comp f)
    ((MulAut.congr e).injective.comp hf)

end Matrix.PSL3Four
