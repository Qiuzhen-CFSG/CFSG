module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.StarPlacement.Models
public import Theory.GroupTheory.CComponent.ExceptionalQuotients
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic

/-!
# The prime-to-three cores of the actual mid-size quotients

Each of the five models in 13.3.2 has trivial prime-to-three core. For the
ordinary models, simplicity and divisibility by three suffice; for the
alternating triple cover, the only possible proper normal subgroup lies
in its center of order three. The same actual model list makes a perfect
quotient quasisimple.

These facts identify the selected component's kernel under the literal
O₃′ quotient in PrimeQuotient. They do not assert the 13.3.2 catalogue or
exclude its unitary or covered rows.
Source: Aschbacher–Smith 13.3.2(1) and the component comparison in 13.4.7,
printed pp.884–885,900.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Section03.Noncentrality.SupercriticalSource
variable {Q : Type*} [Group Q] [Finite Q]

private theorem simple_primeToThreeCore [IsSimpleGroup Q]
    (h3 : 3 ∣ Nat.card Q) : pPrimeCore 3 Q = ⊥ := by
  rcases (pPrimeCore_normal (p := 3) (G := Q)).eq_bot_or_eq_top with hb | ht
  · exact hb
  · have hc := pPrimeCore_coprime_card (p := 3) (G := Q)
    rw [ht, Nat.card_congr (topEquiv : (⊤ : Subgroup Q) ≃* Q).toEquiv] at hc
    exact (Nat.prime_three.coprime_iff_not_dvd.mp hc h3).elim

/-- Every actual quotient in the earlier 13.3.2 list has trivial three-prime core. -/
theorem midSize_primeToThreeCore_eq_bot (hm : MidSizeModel Q) :
    pPrimeCore 3 Q = ⊥ := by
  have h3 : 3 ∣ Nat.card Q := by
    rcases hm.card with h | h | h | h | h <;> rw [h] <;> decide
  rcases hm with ⟨⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨hq,⟨z⟩,⟨e⟩⟩ |
    ⟨F,_,_,J,hF,hJ,⟨e⟩⟩
  · let := alternatingGroup.isSimpleGroup (α := Fin 5) (by simp)
    let : IsSimpleGroup Q := e.isSimpleGroup
    exact simple_primeToThreeCore h3
  · let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
      Atlas.psl_simple_high_rank 3 (by decide)
    let : IsSimpleGroup Q := e.isSimpleGroup
    exact simple_primeToThreeCore h3
  · let := alternatingGroup.isSimpleGroup (α := Fin 6) (by simp)
    let : IsSimpleGroup Q := e.isSimpleGroup
    exact simple_primeToThreeCore h3
  · let := hq
    apply CComponentExceptionalQuotient.primeCore_bot ?_ h3
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_congr z.toEquiv]; simp)
  · let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
      Atlas.G2.isSimple_commutator_binary
    let : IsSimpleGroup Q := (e.trans (J.projectiveEquivBinaryG2Derived hF hJ)).isSimpleGroup
    exact simple_primeToThreeCore h3

omit [Finite Q] in
/-- The source model list makes a perfect quotient quasisimple. -/
theorem midSize_quasisimple [Group.IsPerfect Q] (hm : MidSizeModel Q) :
    IsQuasisimple Q := by
  have step [IsSimpleGroup Q] : IsQuasisimple Q := by
    refine ⟨?_⟩
    exact ((QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple_perfect (G := Q))).trans
      QuotientGroup.quotientBot).isSimpleGroup
  rcases hm with ⟨⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨hq,_⟩ |
    ⟨F,_,_,J,hF,hJ,⟨e⟩⟩
  · let := alternatingGroup.isSimpleGroup (α := Fin 5) (by simp)
    let : IsSimpleGroup Q := e.isSimpleGroup
    exact step
  · let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
      Atlas.psl_simple_high_rank 3 (by decide)
    let : IsSimpleGroup Q := e.isSimpleGroup
    exact step
  · let := alternatingGroup.isSimpleGroup (α := Fin 6) (by simp)
    let : IsSimpleGroup Q := e.isSimpleGroup
    exact step
  · exact hq
  · let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
      Atlas.G2.isSimple_commutator_binary
    let : IsSimpleGroup Q := (e.trans (J.projectiveEquivBinaryG2Derived hF hJ)).isSimpleGroup
    exact step



end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
