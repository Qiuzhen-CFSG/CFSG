module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions.Duality

/-!
# Actual four-subgroups for the two splitting exclusions

For each noncyclic subgroup of the elementary quadratic actor, choose an
order-four subgroup inside that very subgroup. On a faithful natural head,
fixing a hyperplane supplies the common axis. On a chosen socle submodule,
a common center supplies the common axis on the quotient of the dual by its
annihilator. Quadratic action is retained on the whole respective module.

These are the actor inputs to B.4.9(1) in the two uses in Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined manuscript of 1 March
2004, 13.8.25, printed p.961 (PDF p.978).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions

open Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) H U)

/-- A four-group inside the given noncyclic subgroup, with its inherited
elementary and quadratic structures. -/
theorem exists_quadratic_four [Finite H]
    (Vγ A : Subgroup H) [IsElementaryAbelian 2 Vγ]
    (hAV : A ≤ Vγ) (hn : ¬ IsCyclic A) (hq : IsQuadratic ρ Vγ) :
    ∃ E ≤ A, IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧ IsQuadratic ρ E := by
  have hA0 : A ≠ ⊥ := by
    intro h
    subst A
    exact hn inferInstance
  have hV0 : Vγ ≠ ⊥ := by
    intro h
    exact hA0 (le_bot_iff.mp (h ▸ hAV))
  let : IsElementaryAbelian 2 A :=
    (IsElementaryTwo.of_le ⟨hV0, inferInstance⟩ hAV hA0).2
  obtain ⟨E, hEA, hE, hc⟩ := exists_elementary_four_subgroup A hn
  exact ⟨E, hEA, hE, hc, quadratic_of_le ρ hq (hEA.trans hAV)⟩

variable [FiniteDimensional (ZMod 2) U]

/-- The first exclusion's precise four-group input, on the actual quotient
by W, with faithfulness obtained from the natural identification. -/
theorem exists_head_axis_four
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (W : Subrepresentation ρ)
    (hhead : IsNaturalOrDual W.quotientRepresentation eH)
    (Vγ A : Subgroup H) [IsElementaryAbelian 2 Vγ]
    (hAV : A ≤ Vγ) (hn : ¬ IsCyclic A) (hq : IsQuadratic ρ Vγ)
    (hfix : FixesHyperplane W.quotientRepresentation A) :
    ∃ E ≤ A, IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧ IsQuadratic ρ E ∧
      HasCommonAxis W.quotientRepresentation E := by
  let : Finite H := Finite.of_injective
    (fun g : H => (eH g : NaturalSpace → NaturalSpace))
    (fun _ _ h => eH.injective (DFunLike.coe_injective h))
  obtain ⟨E, hEA, hE, hc, hqE⟩ := exists_quadratic_four ρ Vγ A hAV hn hq
  exact ⟨E, hEA, hE, hc, hqE, commonAxis_of_fixesHyperplane _
    (naturalOrDual_faithful _ eH hhead) E (hfix.of_le hEA)⟩

/-- The second exclusion's four-group acts on the dual module, with common
axis on the quotient identified with the dual of the chosen I. -/
theorem exists_socle_dual_axis_four
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (I : Subrepresentation ρ)
    (Vγ A : Subgroup H) [IsElementaryAbelian 2 Vγ]
    (hAV : A ≤ Vγ) (hn : ¬ IsCyclic A) (hq : IsQuadratic ρ Vγ)
    (hcenter : HasCommonCenter I.toRepresentation A) :
    ∃ E ≤ A, IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧ IsQuadratic ρ.dual E ∧
      HasCommonAxis (annihilator ρ I).quotientRepresentation E := by
  let : Finite H := Finite.of_injective
    (fun g : H => (eH g : NaturalSpace → NaturalSpace))
    (fun _ _ h => eH.injective (DFunLike.coe_injective h))
  obtain ⟨E, hEA, hE, hc, hqE⟩ := exists_quadratic_four ρ Vγ A hAV hn hq
  exact ⟨E, hEA, hE, hc, quadratic_dual ρ E hqE,
    (annihilator_quotient_commonAxis ρ I A hcenter).of_le hEA⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions
