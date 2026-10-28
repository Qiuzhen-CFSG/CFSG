module
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.MarkedInvariants
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.InvolutionConjugacy
public import Theory.SpecificGroups.PSL3Two.EmbeddingObstructions
public import Theory.SpecificGroups.SymplecticFour.SevenNormalizer
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# The single-centralizer linear row in symplectic degree four

The full centralizer of a binary PSL₃ involution is conjugate to the
highest-root centralizer. Its projective torus has order
(q−1)/gcd(q−1,3). If the centralizer is a two-group, this odd torus is
trivial, so q≤4. At q=2, the actual seven-element and its squaring
normalizer contradict the symplectic spectrum. Hence precisely q=4 remains.

Source: Aschbacher--Smith G.4.1, printed p.342.
-/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open Matrix Subgroup
open scoped MatrixGroups
namespace Theory.SpecificGroups.SymplecticFour.NativeEvenLinear
open Matrix.PSL3.EvenInnerCentralizers
variable {K F : Type*} [Field K] [Finite K] [Field F] [CharP F 2]

/-- One actual two-group involution centralizer forces the PSL₃(4) row. -/
theorem degree_eq_two_of_one_twoGroup_centralizer {n : ℕ} (hn : 0<n)
    (hK : Nat.card K=2^n) (t : PSL(3,K)) (ht : orderOf t=2)
    (hc : IsPGroup 2 (Subgroup.centralizer ({t} : Set PSL(3,K))))
    (j : PSL(3,K) →* Sp F) (hj : Function.Injective j) : n=2 := by
  have hn1 : n≠1 := by
    intro he
    have hK2 : Nat.card K=2 := by simpa [he] using hK
    letI := Fintype.ofFinite K
    let eK : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card, Nat.card_zmod] using hK2)
    let e : PSL(3,K) ≃* Matrix.PSL3Two.PSL := Atlas.fieldEquivPSL 3 eK
    let f := j.comp e.symm.toMonoidHom
    have hf := hj.comp e.symm.injective
    obtain ⟨a,b,ha,han,hab⟩ := Matrix.PSL3Two.exists_seven_conjugate_square
    apply SevenNormalizer.seven_not_conjugate_square (f a) (f b)
    · rw [←map_pow,ha,map_one]
    · exact fun h => han (hf (h.trans f.map_one.symm))
    · simpa only [map_mul,map_inv,map_pow] using congrArg f hab
  have hn2 : 2≤n := by omega
  have htne : t≠1 := by intro h; simp [h] at ht
  have ht2 : t^2=1 := ht ▸ pow_orderOf_eq_one t
  have hp := hc.of_equiv (involutionCentralizerEquiv K hn2 hK t htne ht2)
  have hpt := hp.to_subgroup (torus K).range
  have ho : Odd (Nat.card (torus K).range) :=
    (MarkedInvariants.units_odd K hK hn).of_dvd_nat (Subgroup.card_range_dvd (torus K))
  obtain ⟨k,hk⟩ := hpt.exists_card_eq
  have hk0 : k=0 := by
    by_contra hh
    exact ho.not_two_dvd_nat (hk ▸ dvd_pow_self 2 hh)
  have hcard : Nat.card (torus K).range=1 := by simpa [hk0] using hk
  rw [MarkedInvariants.torus_card, hK] at hcard
  have hg : (2^n-1).gcd 3 ≤ 3 := Nat.gcd_le_right _ (by decide)
  have hdiv := Nat.div_mul_cancel (Nat.gcd_dvd_left (2^n-1) 3)
  rw [hcard,one_mul] at hdiv
  have hpow : 2^n≤4 := by omega
  have hnlt : n<3 := by
    by_contra hh
    have hh' : 2^3≤2^n := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  omega
end Theory.SpecificGroups.SymplecticFour.NativeEvenLinear
