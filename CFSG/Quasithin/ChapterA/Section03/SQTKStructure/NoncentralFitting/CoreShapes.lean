module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.CoreShapes.Common
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.CoreShapes.PrimeSupport
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.CoreShapes.PrimaryShapes
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.CoreShapes.DefiningPrime
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.CenterFrattiniSource.OmegaActions

/-!
# Fitting-core classification for the noncentral branch of A.3.6

Given the actual prime-field Fitting quotient and prime SL₂ cover rigidity,
`structure_of_fitting_quotient` proves the natural or nilpotent alternative
and every common assertion of A.3.6. The actual supercritical actions restrict
prime support and identify the full primary cores. Away from the SL₂(5)
branch, the sole defining-prime core has its natural conjugation action.
The SL₂(5) branch retains both congruences and every positive homocyclic
exponent. The common-clause argument gives radical index two and identifies
its derived subgroup with F(L) = [F(L),L].

`conclusion_of_fitting_quotient` applies the omega-action strengthening with
all structural premises discharged. Only construction of the actual Fitting
quotient and the stated cover-rigidity input remain with the source assembly
owner. No center–Frattini equality is asserted.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.6, printed pp.43–45.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02 LocalModels
open CFSG.Quasithin.ChapterA.RankActions
namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.CoreShapes
universe u
variable {G : Type u} [Group G] [Finite G] {L : Subgroup G}

/-- Assemble the core alternatives from three independent mathematical branches.
The prime restrictions, full-core shapes and defining-prime natural action
remain explicit until their producers are supplied. Every common clause is
proved by `common_of_alternatives`; none is included among these premises. -/
theorem structure_of_prime_core_data
    (hrigid : PrimeSL2CoverRigidity.{u})
    (hL : L.IsCComponent) (hO : pCore 2 G = ⊥)
    (hn : ¬ fittingSubgroup L ≤ center L) (hquot : PrimeSL2FittingQuotient L)
    (hsupport : ∀ (r : ℕ) [Fact r.Prime], 3 < r →
      Nonempty ((L ⧸ fittingSubgroup L) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) →
      ∀ p : ℕ, p.Prime → p ∣ Nat.card (fittingSubgroup L) →
        p = r ∨ (r = 5 ∧ (p % 5 = 1 ∨ p % 5 = 4)))
    (hshape : ∀ (p : ℕ) [Fact p.Prime], p ∣ Nat.card (fittingSubgroup L) →
      OddExtraspecialThree p (pCore p L) ∨ HomocyclicTwo p (pCore p L))
    (hnatural : ∀ (r : ℕ) [Fact r.Prime], 3 < r →
      Nonempty ((L ⧸ fittingSubgroup L) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) →
      fittingSubgroup L = pCore r L →
      (OddExtraspecialThree r (pCore r L) ∨ HomocyclicTwo r (pCore r L)) →
      NaturalSL2Action L (generalizedFitting L) r) :
    (A36Natural L ∨ A36Nilpotent L) ∧ A36Common L := by
  have hF := generalizedFitting_eq_fitting hL hn
  have hs : A36Natural L ∨ A36Nilpotent L := by
    obtain ⟨r, hr, hr3, he⟩ := hquot
    let : Fact r.Prime := ⟨hr⟩
    by_cases hr5 : r = 5
    · subst r
      right
      refine ⟨hF, ?_, ?_, ?_⟩
      · rw [hF]; infer_instance
      · exact ⟨ZMod 5, inferInstance, inferInstance, Nat.card_zmod 5,
          ⟨(QuotientGroup.quotientMulEquivOfEq hF).trans he.some⟩⟩
      · intro p hp hd
        let : Fact p.Prime := ⟨hp⟩
        rw [hF] at hd
        refine ⟨?_, hshape p hd⟩
        rcases hsupport 5 hr3 he p hp hd with h | ⟨_, h⟩
        · exact Or.inr h
        · exact Or.inl h
    · have hsingle : ∀ p : ℕ, p.Prime → p ∣ Nat.card (fittingSubgroup L) → p = r := by
        intro p hp hd
        exact (hsupport r hr3 he p hp hd).resolve_right (fun h => hr5 h.1)
      have hcore := fitting_eq_core_of_support hsingle
      have hnontriv : Nat.card (fittingSubgroup L) ≠ 1 := by
        intro hc
        apply hn
        rw [card_eq_one.mp hc]
        exact bot_le
      obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd hnontriv
      have hrd : r ∣ Nat.card (fittingSubgroup L) := hsingle p hp hd ▸ hd
      exact Or.inl ⟨hF, r, hr, hr3, hnatural r hr3 he hcore (hshape r hrd)⟩
  exact ⟨hs, common_of_alternatives hrigid hL hO hn hquot hs⟩

/-- The noncentral A.3.6 core alternatives and all common clauses from the
actual prime-field Fitting quotient. Prime support, full primary-core shapes
and the natural conjugation equation are supplied by their proved producers. -/
theorem structure_of_fitting_quotient
    (hrigid : PrimeSL2CoverRigidity.{u})
    {𝒦 : GroupClass.{u}} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent) (hn : ¬ fittingSubgroup L ≤ center L)
    (hquot : PrimeSL2FittingQuotient L) :
    (A36Natural L ∨ A36Nilpotent L) ∧ A36Common L := by
  exact structure_of_prime_core_data hrigid hL hO hn hquot
    (PrimeSupport.prime_support_contract hrigid hG hO hL)
    (PrimaryShapes.primary_shapes hrigid hG hO hL hquot)
    (DefiningPrime.hnatural hG hL hn)

/-- Apply the actual omega-action theorem to the completed core classification.
Noncentrality of F(L) supplies its nonquasisimplicity premise. -/
theorem conclusion_of_fitting_quotient
    (hrigid : PrimeSL2CoverRigidity.{u})
    {𝒦 : GroupClass.{u}} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent) (hn : ¬ fittingSubgroup L ≤ center L)
    (hquot : PrimeSL2FittingQuotient L) :
    A36Conclusion L ∧ CenterFrattiniSource.OmegaActionData L := by
  obtain ⟨hs, hc⟩ := structure_of_fitting_quotient hrigid hG hO hL hn hquot
  have h : A36Conclusion L :=
    ⟨hs.elim A36Alternative.natural A36Alternative.nilpotent, hc⟩
  have hw := CenterFrattiniSource.strengthened_omega_actions hG hO hL h
  exact ⟨hw.1, hw.2 (not_quasisimple_of_noncentral_fitting hn)⟩

end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting.CoreShapes
