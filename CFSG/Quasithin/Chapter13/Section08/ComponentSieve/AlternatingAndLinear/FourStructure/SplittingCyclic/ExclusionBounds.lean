module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.CommutatorSpaces


/-!
# Nonsplitting exclusions in the conventions of the critical-pair consumers

For a faithful action, containment of every displacement in one line implies
that each nonidentity actor has exactly that line as its displacement range.
This connects the two common-center definitions without changing the actor.
An elementary actor of rank greater than one is noncyclic, and the head's
faithfulness turns the hyperplane exclusion into fixed codimension at least
two. The final theorem supplies both bounds to the subsequent source
arguments directly from the precise two-factor B.4.9(1) premise.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, B.4.9(1), printed p.92, and 13.8.25,
printed pp.961–962 (PDF pp.978–979).
-/

public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic
open ChiefFactors CriticalTransfer
universe u v
variable {H : Type u} {U : Type v} [Group H]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]

/-- The displacement-line convention in the later source argument agrees with
the exact transvection-center convention when the action is faithful. -/
theorem commonCenter_of_displacement_line
    (ρ : Representation (ZMod 2) H U) (hρ : Function.Injective ρ)
    (A : Subgroup H) (h : MarkedGeometry.HasCommonCenter ρ A) :
    AxisExclusions.HasCommonCenter ρ A := by
  obtain ⟨P, hP, hfix⟩ := h
  refine ⟨P, hP, ?_⟩
  intro a ha ha1
  have hle : LinearMap.range (ρ a - 1) ≤ P := by
    rintro _ ⟨v, rfl⟩
    exact hfix a ha v
  have hnonzero : LinearMap.range (ρ a - 1) ≠ ⊥ := by
    intro hz
    have hm : ρ a = 1 := sub_eq_zero.mp (LinearMap.range_eq_bot.mp hz)
    exact ha1 (hρ (hm.trans (map_one ρ).symm))
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hp : Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) ≠ 0 :=
    fun hz => hnonzero (Submodule.finrank_eq_zero.mp hz)
  have hm := Submodule.finrank_mono hle
  omega

/-- An elementary actor of binary rank greater than one is noncyclic. -/
theorem not_isCyclic_of_elementary_rank_gt_one
    (A : Subgroup H) [IsElementaryAbelian 2 A] (hA : 1 < rank A) : ¬ IsCyclic A := by
  intro hc
  let : IsCyclic A := hc
  have hd : Nat.card A ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 A
  have hm := Nat.log_monotone (b := 2) (Nat.le_of_dvd (by decide : 0 < 2) hd)
  have hb : rank A ≤ 1 := by simpa only [rank, show Nat.log 2 2 = 1 from by decide] using hm
  omega

/-- The two nonsplitting exclusions in the rank and displacement conventions
used by the subsequent critical-pair argument. -/
theorem nonsplitting_bounds
    (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (hsplit : AxisExclusions.TwoFactorSplitting.{u, v} H)
    (hchief : ChiefFactorsNaturalOrDual ρ eH)
    (W : Subrepresentation ρ) (hW : IsCoatom W) (hW0 : W ≠ ⊥)
    (hunique : ∀ X : Subrepresentation ρ, IsCoatom X → X = W)
    (hhead : IsNatural W.quotientRepresentation eH)
    (B : Subgroup H) (hB : IsElementaryTwo B) (hq : IsQuadratic ρ B) :
    (∀ A ≤ B, 1 < rank A → 1 < fixedCodim W.quotientRepresentation A) ∧
    (∀ I : Subrepresentation ρ, IsAtom I → I ≤ W →
      ∀ A ≤ B, 1 < rank A → ¬ MarkedGeometry.HasCommonCenter I.toRepresentation A) := by
  let : IsElementaryAbelian 2 B := hB.2
  have hA0 (A : Subgroup H) (hr : 1 < rank A) : A ≠ ⊥ := by
    intro he
    rw [he, Representation.BinaryOffender.rank_bot] at hr
    omega
  have hn (A : Subgroup H) (hAB : A ≤ B) (hr : 1 < rank A) : ¬ IsCyclic A := by
    let : IsElementaryAbelian 2 A := (hB.of_le hAB (hA0 A hr)).2
    exact not_isCyclic_of_elementary_rank_gt_one A hr
  obtain ⟨haxis, hcenter⟩ := AxisExclusions.nonsplitting_exclusions ρ eH hsplit hchief
    W hW hW0 hunique hhead B hq
  constructor
  · intro A hAB hr
    have hpos := fixedCodim_pos_of_faithful W.quotientRepresentation
      (AxisExclusions.natural_faithful _ eH hhead) (hA0 A hr)
    by_contra! hle
    have he : fixedCodim W.quotientRepresentation A = 1 := by omega
    exact haxis A hAB (hn A hAB hr)
      ⟨fixedSpace W.quotientRepresentation A, he, fun a ha v hv => hv ⟨a, ha⟩⟩
  · intro I hI hIW A hAB hr hline
    exact hcenter I hI hIW A hAB (hn A hAB hr)
      (commonCenter_of_displacement_line I.toRepresentation
        (AxisExclusions.naturalOrDual_faithful _ eH
          (AxisExclusions.naturalOrDual_atom ρ eH hchief I hI)) A hline)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic
