module
public import Theory.SpecificGroups.PSL3Four.OuterThreeStructure
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.GroupTheory.SylowOuterAutomorphisms

/-!
# Coprime actors preserving a Sylow subgroup of PSL₃(4)

The actual Borel normalizer has order 192. The outer automorphism group has
order dividing twelve, so a Sylow-preserving automorphism has its twelfth
power induced by an element of that Borel. Its order therefore divides
12 · 192. An actor of order prime to six must be trivial.

Source application: the opening paragraph of Aschbacher–Smith 5.1.17,
printed p.640, where the odd-exponent Cartan preserves the residual Sylow.
-/

public section
open Subgroup
open scoped Pointwise MatrixGroups
namespace Matrix.PSL3Four

private theorem borel_card : Nat.card (PSL3.LinearThree.borel F) = 192 := by
  have ht := PSL3.CartanActions.BorelQuotient.card_torus_mul_scalar F
  rw [card_F] at ht
  norm_num at ht
  have hc := (PSL3.CartanActions.BorelQuotient.borel_complement F
    (n := 2) (by simpa using card_F)).card_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (PSL3.LinearThree.unipotent_le_borel F)).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (PSL3.CartanActions.torus_le_borel F)).toEquiv,
    PSL3.LinearThree.card_unipotent, card_F] at hc
  omega

/-- Every Sylow two-normalizer is the order-192 projective Borel. -/
theorem sylow_normalizer_card (P : Sylow 2 PSL) :
    Nat.card (normalizer (P : Set PSL)) = 192 := by
  rw [Nat.card_congr (PSL3.CartanActions.BorelQuotient.sylowNormalizerEquiv F
    (n := 2) (by decide) (by simpa using card_F) P).toEquiv]
  exact borel_card

/-- Sylow preservation bounds the order of the actual automorphism. -/
theorem sylow_preserving_aut_pow (P : Sylow 2 PSL) (a : MulAut PSL)
    (ha : (P : Subgroup PSL).map a.toMonoidHom = P) : a ^ (12 * 192) = 1 := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL)
  have ho : q a ^ 12 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard (q a) |>.trans
      OuterThreeStructure.outer_card_dvd_twelve)
  rw [← map_pow] at ho
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff _).mp ho
  have hpres : a ^ 12 ∈ MulAction.stabilizer (MulAut PSL) (P : Subgroup PSL) :=
    (MulAction.stabilizer (MulAut PSL) (P : Subgroup PSL)).pow_mem ha 12
  have hn : g ∈ normalizer (P : Set PSL) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [hg]
    exact hpres
  have hpow : g ^ 192 = 1 := by
    have h := pow_card_eq_one' (x := (⟨g, hn⟩ : normalizer (P : Set PSL)))
    rw [sylow_normalizer_card P] at h
    exact congrArg Subtype.val h
  rw [pow_mul, ← hg, ← map_pow, hpow, map_one]

/-- An automorphism of order prime to six cannot act nontrivially while preserving a Sylow. -/
theorem sylow_preserving_aut_eq_one_of_coprime
    (P : Sylow 2 PSL) (a : MulAut PSL)
    (ha : (P : Subgroup PSL).map a.toMonoidHom = P)
    (hc : Nat.Coprime (orderOf a) 6) : a = 1 := by
  have hd : orderOf a ∣ 12 * 192 := orderOf_dvd_of_pow_eq_one (sylow_preserving_aut_pow P a ha)
  have hd' : orderOf a ∣ 6 ^ 8 := hd.trans (by decide)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hc.pow_right 8) dvd_rfl hd')
end Matrix.PSL3Four
