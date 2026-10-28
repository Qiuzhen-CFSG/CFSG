module

public import Theory.SpecificGroups.SU3.EvenProjectiveComparison

/-!
# The prime central kernel of the actual SU₃ projection

The kernel of `J.specialToProjective` embeds in the scalar matrices. Those
form a cyclic group over a finite field, and determinant one gives exponent
three. Consequently the kernel has order dividing three, for every stored
nondegenerate Hermitian form. This uses no multiplier theorem.

For fixed-field order `2^n`, `n ≥ 2`, the actual projective model is
centerless, so this kernel is the whole SU₃ center. The existing injectivity
result at even `n` then shows that a nontrivial center has order three and
requires odd `n`.

Source: the canonical unitary center in GLS3, Table 6.1.2, and its use in
GLS4, Chapter 4, Lemma 2.8(a). These matrix calculations do not establish
universality of SU₃.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm

/-- The literal special-to-projective scalar kernel has order dividing three. -/
public theorem card_specialToProjective_ker_dvd_three
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E) :
    Nat.card J.specialToProjective.ker ∣ 3 := by
  let : IsCyclic (center (GL (Fin 3) E)) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact isCyclic_of_surjective (GeneralLinearGroup.scalar (Fin 3)).rangeRestrict
      (GeneralLinearGroup.scalar (Fin 3)).rangeRestrict_surjective
  let f : J.specialToProjective.ker →* center (GL (Fin 3) E) :=
    (J.specialSubgroup.subtype.comp J.specialToProjective.ker.subtype).codRestrict
      (center (GL (Fin 3) E)) (fun x => by
        change x.val.val ∈ center (GL (Fin 3) E)
        apply ProjGenLinGroup.mk_eq_one.mp
        simpa only [J.specialToProjective_apply_val, Subgroup.coe_one] using
          congrArg Subtype.val (MonoidHom.mem_ker.mp x.property))
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : center (GL (Fin 3) E) => z.val) h
  let := isCyclic_of_injective f hf
  rw [← IsCyclic.exponent_eq_card]
  exact Monoid.exponent_dvd_of_forall_pow_eq_one J.specialToProjective_ker_cube


/-- A nontrivial SU₃(2ⁿ) center has order three, and `n` is odd. -/
public theorem special_center_eq_bot_or_card_three_odd
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    center J.specialSubgroup = ⊥ ∨
      Nat.card (center J.specialSubgroup) = 3 ∧ Odd n := by
  have hconj := External.huppert_II_10_4_conj_eq_frobenius J (2 ^ n) hcard hfixed
  have hZ := HermitianForm.EvenProjectiveComparison.center_eq_bot J
    (by omega : 0 < n) hcard hconj
  have hker := J.specialToProjective_ker_eq_center hZ
  have hdiv : Nat.card (center J.specialSubgroup) ∣ 3 := by
    rw [← hker]
    exact J.card_specialToProjective_ker_dvd_three
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdiv with hc | hc
  · exact Or.inl ((eq_bot_iff_card _).mpr hc)
  · refine Or.inr ⟨hc, ?_⟩
    rcases Nat.even_or_odd n with he | ho
    · have hi := HermitianForm.EvenProjectiveComparison.specialToProjective_injective
        J he hconj
      have hb := J.specialToProjective.ker_eq_bot_iff.mpr hi
      have heq : Nat.card (center J.specialSubgroup) = 1 :=
        (eq_bot_iff_card _).mp (hker ▸ hb)
      omega
    · exact ho


end BenderSuzuki.MatrixGroups.HermitianForm
