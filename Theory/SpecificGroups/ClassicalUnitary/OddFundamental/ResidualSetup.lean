module

public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental
public import Theory.SpecificGroups.SL2.PrimeToResidual
public import Theory.SpecificGroups.SL2.DefiningRank

/-!
# The marked unitary centralizer and its prime-to-characteristic residual

The complementary block from `OddFundamental` lands in the actual projective
centralizer of the fundamental SU₂. Its inclusion remains injective. This
module fixes that centralizer and its literal prime-to-r residual as shared
interfaces for their computation.

When the complement has dimension two, SL₂ transvection generation puts the
whole complement in the residual, including q=3; no perfectness assumption is
used. This supplies the degree-four exponent restriction in the source consumer.

Source: Aschbacher–Smith, A.2.17, printed pp.38–39 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.OddFundamental
variable {F : Type*} [Field F] (σ : F ≃+* F) (hσ : Function.Involutive σ)
variable {n : ℕ}

/-- The complementary factor, as a subgroup of the actual projective centralizer. -/
def complementInCentralizer : (form σ hσ n).specialSubgroup →*
    Subgroup.centralizer (projectLeft σ hσ (m := 2) (n := n)).range.carrier :=
  (projectRight σ hσ).codRestrict _ fun b => by
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨a, rfl⟩
    exact (factors_commute σ hσ a b).eq

theorem complementInCentralizer_injective :
    Function.Injective (complementInCentralizer σ hσ (n := n)) := by
  intro a b h
  exact projectRight_injective σ hσ (congrArg Subtype.val h)

/-- The literal prime-to-r residual of the marked fundamental centralizer. -/
def residual (r : ℕ) :=
  Subgroup.primeToResidual r
    (Subgroup.centralizer (projectLeft σ hσ (m := 2) (n := n)).range.carrier)

/-- A complementary SU₂ contributes its full SL₂ to this residual, including q=3. -/
def complementaryTwoInResidual {r : ℕ} [CharP (FixedBy.subfield F σ) r]
    (e : (form σ hσ 2).specialSubgroup ≃*
      SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ)) :
    SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ) →* residual σ hσ (n := 2) r :=
  let f := (complementInCentralizer σ hσ (n := 2)).comp e.symm.toMonoidHom
  f.codRestrict _ (Matrix.SL2.map_mem_primeToResidual r f)

theorem complementaryTwoInResidual_injective {r : ℕ} [CharP (FixedBy.subfield F σ) r]
    (e : (form σ hσ 2).specialSubgroup ≃*
      SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ)) :
    Function.Injective (complementaryTwoInResidual σ hσ (r := r) e) := by
  intro a b h
  exact e.symm.injective (complementInCentralizer_injective σ hσ (congrArg Subtype.val h))

/-- Defining-field degree is visible inside the literal degree-four residual. -/
theorem fieldExponent_le_residual_two [Finite F] {r e : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (he : 0 < e) (hc : Nat.card F = (r ^ e) ^ 2)
    (hj : ∀ x, σ x = x ^ (r ^ e)) :
    e ≤ primeRank r (residual σ hσ (n := 2) r) := by
  let : Finite (ProjGenLinGroup (Fin 4) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  have hq : IsPrimePow (r ^ e) := (isPrimePow_nat_iff _).mpr
    ⟨r, e, Fact.out, he, rfl⟩
  have ho : Odd (r ^ e) := ((Fact.out : r.Prime).odd_of_ne_two hr).pow
  obtain ⟨a⟩ := nonempty_specialTwoEquiv_odd σ hσ hq ho hc hj
  have hk : Nat.card (FixedBy.subfield F σ) = r ^ e :=
    (form σ hσ 2).fixed_card_prime_power hq hc hj
  let : Fintype (FixedBy.subfield F σ) := Fintype.ofFinite _
  let : CharP (FixedBy.subfield F σ) r := charP_of_card_eq_prime_pow
    (by simpa only [← Nat.card_eq_fintype_card] using hk)
  exact SpecialLinearGroup.fieldExponent_le_primeRank_of_injective hk
    (complementaryTwoInResidual σ hσ a) (complementaryTwoInResidual_injective σ hσ a)

end Theory.SpecificGroups.ClassicalUnitary.OddFundamental
