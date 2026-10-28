module

public import Theory.SpecificGroups.Rudvalis.Model.DirectDisplacementWords
public import Theory.SpecificGroups.Rudvalis.Model.ThreeConjugates.Fusion
public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer.TitsEmbedding
public import Theory.Representation.Tits.FrobeniusDisplacement
public import Theory.Representation.BinaryPrimeDisplacement

/-!
# Displacement in every faithful binary Rudvalis action

The marked 2B involution has an order-29 commutator, so it moves at least
fourteen dimensions. The certified Tits subgroup fixes a point in the
degree-4060 action. Its five-local quaternion square therefore belongs to
the 2A class: it cannot be conjugate to the fixed-point-free 2B generator.
The Frobenius weight argument gives its moved dimension at least twelve.
Involution fusion extends these two bounds to all involutions.

These arguments require neither a degree bound nor irreducibility. They
replace the small-representation catalogue in the displacement step of
Guralnick--Malle, *Classification of 2F-modules I*, Proposition 5.1 (Ru),
used in Aschbacher--Smith K.4, printed p.457. All group comparisons use
the native permutation and Tits carriers.
-/

public section
namespace Representation.RudvalisDirectDisplacement
open Subgroup BinaryOffender Rudvalis.DirectDisplacementWords

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem orderOf_two_mod_twentyNine : orderOf (2 : ZMod 29) = 28 := by
  apply (orderOf_eq_iff (by decide : 0 < 28)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> norm_num at * <;> decide

/-- Every faithful binary action of the native Ru carrier has degree at least 28. -/
theorem finrank_ge_twentyEight (σ : Representation (ZMod 2) Rudvalis.Model V)
    (hf : Function.Injective σ) : 28 ≤ Module.finrank (ZMod 2) V := by
  have h := prime_order_le_fixedCodim σ hf (by decide : Nat.Prime 29) (by decide)
    oddWord oddWord_order
  rw [orderOf_two_mod_twentyNine] at h
  have hd := fixedCodim_add_finrank σ (zpowers oddWord)
  omega

/-- The order-29 commutator gives a degree-free bound for the 2B class. -/
theorem a_displacement (σ : Representation (ZMod 2) Rudvalis.Model V)
    (hf : Function.Injective σ) :
    14 ≤ fixedCodim σ (zpowers Rudvalis.a) := by
  have h := prime_order_le_fixedCodim σ hf (by decide : Nat.Prime 29) (by decide)
    oddWord oddWord_order
  rw [orderOf_two_mod_twentyNine] at h
  have hu := fixedCodim_commutator_le_twice σ Rudvalis.a conjugator⁻¹
  rw [← oddWord_eq_commutator] at hu
  omega

/-- The literal Tits five-inverter embeds in Ru's marked 2A class. The
point-stabilizer marking, together with Ru's proved two-class fusion, suffices. -/
theorem exists_tits_embedding_inverter_class :
    ∃ ι : Tits.ParrottGroup →* Rudvalis.Model, Function.Injective ι ∧
      IsConj (ι (Tits.parrottFiniteImageEquiv.symm (Tits.FiveFrobenius.r ^ 2)))
        (Rudvalis.b ^ 2) := by
  obtain ⟨K, hK, _, ⟨e⟩⟩ := Rudvalis.outer_stabilizer_tits_subgroup
  let j : Tits.ParrottGroup ≃* K := Tits.parrottFiniteImageEquiv.trans e
  let ι : Tits.ParrottGroup →* Rudvalis.Model := K.subtype.comp j.toMonoidHom
  have hi : Function.Injective ι := K.subtype_injective.comp j.injective
  let t := Tits.parrottFiniteImageEquiv.symm (Tits.FiveFrobenius.r ^ 2)
  have ht : orderOf t = 2 := TitsFrobeniusDisplacement.inverter_order
  have hit : orderOf (ι t) = 2 := (orderOf_injective ι hi t).trans ht
  have hfix : ι t • (0 : Fin 4060) = 0 := hK (j t).property
  refine ⟨ι, hi, ?_⟩
  rcases Rudvalis.involution_isConj_a_or_b_sq (ι t) hit with h | h
  · obtain ⟨g, hg⟩ := isConj_iff.mp h
    exact (a_no_fixed_point (g • (0 : Fin 4060))) (by
      rw [← hg]
      simp only [mul_smul, inv_smul_smul, hfix]) |>.elim
  · exact h

private theorem fixedCodim_eq_of_isConj
    (σ : Representation (ZMod 2) Rudvalis.Model V)
    {s t : Rudvalis.Model} (h : IsConj s t) :
    fixedCodim σ (zpowers s) = fixedCodim σ (zpowers t) := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact (fixedCodim_zpowers_conj σ s g).symm

/-- The five-local Frobenius action gives a degree-free bound for the 2A class. -/
theorem b_sq_displacement (σ : Representation (ZMod 2) Rudvalis.Model V)
    (hf : Function.Injective σ) :
    12 ≤ fixedCodim σ (zpowers (Rudvalis.b ^ 2)) := by
  obtain ⟨ι, hi, hclass⟩ := exists_tits_embedding_inverter_class
  have h := TitsFrobeniusDisplacement.fiveInverter_displacement (σ.comp ι) (hf.comp hi)
  have hd : 12 ≤ fixedCodim σ
      (zpowers (ι (Tits.parrottFiniteImageEquiv.symm (Tits.FiveFrobenius.r ^ 2)))) := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    exact h
  rwa [fixedCodim_eq_of_isConj σ hclass] at hd

/-- The exact bounds needed by maximal-centralizer saturation, for the
original arbitrary representation rather than one selected matrix model. -/
theorem involution_displacement (σ : Representation (ZMod 2) Rudvalis.Model V)
    (hf : Function.Injective σ) (t : Rudvalis.Model) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    12 ≤ fixedCodim σ (zpowers t) ∧
      (fixedCodim σ (zpowers t) ≤ 12 → IsConj t (Rudvalis.b ^ 2)) := by
  rcases Rudvalis.involution_isConj_a_or_b_sq t (orderOf_eq_prime ht2 ht) with ha | hb
  · have hd := a_displacement σ hf
    rw [← fixedCodim_eq_of_isConj σ ha] at hd
    exact ⟨by omega, fun h => by omega⟩
  · have hd := b_sq_displacement σ hf
    rw [← fixedCodim_eq_of_isConj σ hb] at hd
    exact ⟨hd, fun _ => hb⟩

end Representation.RudvalisDirectDisplacement
