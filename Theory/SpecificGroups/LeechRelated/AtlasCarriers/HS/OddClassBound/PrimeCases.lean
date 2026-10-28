module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.CarrierComparison
public import Theory.GroupTheory.PrimeCyclicCoverage

/-!
# The seven- and eleven-element conjugacy classes of the literal HS group

A checked word in the degree-100 generators raises the chosen seven-element
to its cube. The six nonzero residues modulo seven form one orbit under
multiplication by three. The marked eleven-normalizer, transported along the
actual point-stabilizer equivalence, raises its eleven-element to its fourth
power. Its two orbits cover all ten nonzero residues modulo eleven.

The exact carrier order has only one factor of each prime. Sylow conjugacy
therefore transfers the power calculations to every element of those orders.
These are coverage theorems for actual group elements, rather than checks
restricted to the chosen representatives. The nine-odd-class assembly consumes
both in `FixedSpace.OddClasses`.

Source: ATLAS HSG1-p100B0 and the HS class list at
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/HS/ . The original GAP discovery
script is retained in `PrimeCases/source/`; only kernel-checked permutation
identities enter the proofs. The eleven marking and its transport are the
same as in the existing HS trace-power-fusion calculation.
-/

public section
namespace Sporadic.LeechRelated.HS.OddClassBound
open OrderCertificate Theory.GroupTheory

private def a : Carrier := ⟨p0, by rw [a_eq_generator]; exact Subgroup.subset_closure (by simp)⟩
private def b : Carrier := ⟨p1, by rw [b_eq_generator]; exact Subgroup.subset_closure (by simp)⟩
/-- A marked element of order seven in the published carrier. -/
def seven : Carrier := a * b * a * b * a * b * b
private def letter (i : Fin 3) : Carrier := if i = 0 then a else if i = 1 then b else b⁻¹
private def conjugator : Carrier := evalWord letter
  [2, 0, 1, 1, 0, 2, 0, 2, 0, 1, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2,
   2, 0, 1, 0, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 0, 1,
   0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2]
/-- The marked seven-element has its asserted order. -/
theorem seven_order : orderOf seven = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply Subtype.ext
    apply Equiv.ext
    apply allFin
    decide +kernel
  · intro h
    have he := congrArg (fun z : Carrier => inclusion z 0) h
    exact (by decide +kernel : inclusion seven 0 ≠ 0) he

/-- An actual carrier word conjugates the marked element to its cube. -/
theorem seven_cube : IsConj seven (seven ^ 3) := by
  apply isConj_iff.mpr
  refine ⟨conjugator, ?_⟩
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem seven_power (k : ℕ) (hk : k % 7 ≠ 0) : IsConj seven (seven ^ k) := by
  have hmod (n : ℕ) : seven ^ (n % 7) = seven ^ n := by
    simpa only [seven_order] using pow_mod_orderOf seven n
  have hstep (n : ℕ) : IsConj (seven ^ n) (seven ^ ((3 * n) % 7)) := by
    rw [hmod]
    simpa only [← pow_mul] using seven_cube.pow n
  have h2 : IsConj seven (seven ^ 2) := seven_cube.trans (hstep 3)
  have h6 : IsConj seven (seven ^ 6) := h2.trans (hstep 2)
  have h4 : IsConj seven (seven ^ 4) := h6.trans (hstep 6)
  have h5 : IsConj seven (seven ^ 5) := h4.trans (hstep 4)
  rw [← hmod k]
  have hlt : k % 7 < 7 := Nat.mod_lt _ (by decide)
  interval_cases h : k % 7
  · exact (hk rfl).elim
  · simpa using IsConj.refl seven
  · exact h2
  · exact seven_cube
  · exact h4
  · exact h5
  · exact h6

/-- Every element of order seven lies in the marked element's conjugacy class. -/
theorem orderSeven_conjugate (g : Carrier) (hg : orderOf g = 7) : IsConj g seven := by
  obtain ⟨k, c, hc⟩ := PrimeCyclicCoverage.exists_conjugate_pow_of_prime_sq_not_dvd
    (G := Carrier) (by decide : Nat.Prime 7)
    (by rw [NormalizerIndex.card_carrier]; decide) seven_order hg
  have hk : k % 7 ≠ 0 := by
    intro hk
    rw [← pow_mod_orderOf, seven_order, hk, pow_zero, mul_one, mul_inv_cancel] at hc
    rw [hc, orderOf_one] at hg
    contradiction
  exact (isConj_iff.mpr ⟨c, hc.symm⟩).symm.trans (seven_power k hk).symm

private def certifiedEmbedding : SmallIndex.CertifiedStabilizer →* Carrier :=
  pointStabilizer.subtype.comp SmallIndex.pointStabilizerEquivCertified.symm.toMonoidHom
private theorem certifiedEmbedding_injective : Function.Injective certifiedEmbedding :=
  Subtype.val_injective.comp SmallIndex.pointStabilizerEquivCertified.symm.injective
/-- The certified point-stabilizer eleven-element in the actual HS carrier. -/
def eleven : Carrier := certifiedEmbedding SmallIndex.elevenElement
/-- The actual point-stabilizer embedding preserves the order eleven. -/
theorem eleven_order : orderOf eleven = 11 :=
  (orderOf_injective certifiedEmbedding certifiedEmbedding_injective _).trans
    SmallIndex.elevenElement_order
private theorem eleven_four : IsConj eleven (eleven ^ 4) := by
  have h9 : IsConj eleven (eleven ^ 9) := by
    apply isConj_iff.mpr
    refine ⟨certifiedEmbedding SmallIndex.normalizerElement, ?_⟩
    simpa only [eleven, map_mul, map_inv, map_pow] using
      congrArg certifiedEmbedding SmallIndex.normalizerElement_conj
  have h81 := h9.trans (h9.pow 9)
  have he : eleven ^ 81 = eleven ^ 4 := by
    rw [← pow_mod_orderOf, eleven_order]
  simpa only [← pow_mul, he] using h81

private theorem eleven_power (k : ℕ) (hk : k % 11 ≠ 0) :
    IsConj (eleven ^ k) eleven ∨ IsConj (eleven ^ k) (eleven ^ 2) := by
  have hmod (n : ℕ) : eleven ^ (n % 11) = eleven ^ n := by
    simpa only [eleven_order] using pow_mod_orderOf eleven n
  have hstep (n : ℕ) : IsConj (eleven ^ n) (eleven ^ ((4 * n) % 11)) := by
    rw [hmod]
    simpa only [← pow_mul] using eleven_four.pow n
  have h5 : IsConj eleven (eleven ^ 5) := eleven_four.trans (hstep 4)
  have h9 : IsConj eleven (eleven ^ 9) := h5.trans (hstep 5)
  have h3 : IsConj eleven (eleven ^ 3) := h9.trans (hstep 9)
  have h8 : IsConj (eleven ^ 2) (eleven ^ 8) := hstep 2
  have h10 : IsConj (eleven ^ 2) (eleven ^ 10) := h8.trans (hstep 8)
  have h7 : IsConj (eleven ^ 2) (eleven ^ 7) := h10.trans (hstep 10)
  have h6 : IsConj (eleven ^ 2) (eleven ^ 6) := h7.trans (hstep 7)
  rw [← hmod k]
  have hlt : k % 11 < 11 := Nat.mod_lt _ (by decide)
  interval_cases h : k % 11
  · exact (hk rfl).elim
  · exact Or.inl (by simpa using IsConj.refl eleven)
  · exact Or.inr (IsConj.refl _)
  · exact Or.inl h3.symm
  · exact Or.inl eleven_four.symm
  · exact Or.inl h5.symm
  · exact Or.inr h6.symm
  · exact Or.inr h7.symm
  · exact Or.inr h8.symm
  · exact Or.inl h9.symm
  · exact Or.inr h10.symm

/-- Two marked powers cover every element of order eleven in HS. -/
theorem orderEleven_conjugate (g : Carrier) (hg : orderOf g = 11) :
    IsConj g eleven ∨ IsConj g (eleven ^ 2) := by
  obtain ⟨k, c, hc⟩ := PrimeCyclicCoverage.exists_conjugate_pow_of_prime_sq_not_dvd
    (G := Carrier) (by decide : Nat.Prime 11)
    (by rw [NormalizerIndex.card_carrier]; decide) eleven_order hg
  have hk : k % 11 ≠ 0 := by
    intro hk
    rw [← pow_mod_orderOf, eleven_order, hk, pow_zero, mul_one, mul_inv_cancel] at hc
    rw [hc, orderOf_one] at hg
    contradiction
  have hcg : IsConj g (eleven ^ k) := (isConj_iff.mpr ⟨c, hc.symm⟩).symm
  exact (eleven_power k hk).imp hcg.trans hcg.trans

end Sporadic.LeechRelated.HS.OddClassBound
