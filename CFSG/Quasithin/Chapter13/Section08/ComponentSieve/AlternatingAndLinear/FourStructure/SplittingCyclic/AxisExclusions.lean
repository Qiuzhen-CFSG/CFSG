module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.Induction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions.Actors
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions.TwoStep
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions.DualFactors

/-!
# The head-axis and socle-center nonsplitting exclusions

No noncyclic subgroup of the elementary quadratic actor fixes a hyperplane
of the natural head, or acts with a common transvection center on an
irreducible submodule of the nonzero unique maximal submodule W.

For the head, an actual four-subgroup supplies the common axis. Applying
the precise two-factor splitting input to each section in the finite-length
induction constructs an equivariant section of U → U/W, contradicting unique
maximality. For a chosen irreducible I ≤ W, duality transfers every chief
factor and identifies U*/Iᗮ equivariantly with I*. The common center on I
becomes a common axis on this quotient. The same induction supplies a
complement to Iᗮ, hence a complement to I, again contradicting unique
maximality in the original module.

Only the two-factor GL₄(2) instance of B.4.9(1) remains an explicit premise;
whole-module splitting and both exclusions are proved here from that input.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, B.4.9(1), printed p.92, and 13.8.25,
printed p.961 (PDF p.978).
-/

public section

universe u v

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions

open Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors

variable {H : Type u} {U : Type v} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)

/-- A noncyclic subgroup of the elementary quadratic actor cannot fix a
hyperplane of the actual natural-or-dual head. The two-factor splitting
input gives an equivariant section, contradicting unique maximality. -/
theorem not_fixesHyperplane_of_noncyclic
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (hsplit : TwoFactorSplitting.{u, v} H)
    (hchief : ChiefFactorsNaturalOrDual ρ eH)
    (W : Subrepresentation ρ) (hW : IsCoatom W) (hW0 : W ≠ ⊥)
    (hunique : ∀ X : Subrepresentation ρ, IsCoatom X → X = W)
    (hhead : IsNaturalOrDual W.quotientRepresentation eH)
    (Vγ A : Subgroup H) [IsElementaryAbelian 2 Vγ]
    (hAV : A ≤ Vγ) (hn : ¬ IsCyclic A) (hq : IsQuadratic ρ Vγ) :
    ¬ FixesHyperplane W.quotientRepresentation A := by
  intro hfix
  obtain ⟨E, _hEA, _hE, hcard, hqE, haxis⟩ :=
    exists_head_axis_four ρ eH W hhead Vγ A hAV hn hq hfix
  exact not_equivariant_section_of_unique_maximal ρ W hW hW0 hunique
    (equivariant_section_of_two_step_splitting ρ W
      (two_step_splitting_of_commonAxis ρ eH hsplit hchief W hW hhead E hcard hqE haxis))

/-- A noncyclic subgroup of the elementary quadratic actor cannot act with
a common transvection center on the chosen irreducible submodule I ≤ W.
Splitting above I's annihilator in the dual gives a complement to I in the
original module, contradicting unique maximality there. -/
theorem not_hasCommonCenter_of_noncyclic
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (hsplit : TwoFactorSplitting.{u, v} H)
    (hchief : ChiefFactorsNaturalOrDual ρ eH)
    (W : Subrepresentation ρ) (hW : IsCoatom W)
    (hunique : ∀ X : Subrepresentation ρ, IsCoatom X → X = W)
    (I : Subrepresentation ρ) (hI : IsAtom I) (hIW : I ≤ W)
    (Vγ A : Subgroup H) [IsElementaryAbelian 2 Vγ]
    (hAV : A ≤ Vγ) (hn : ¬ IsCyclic A) (hq : IsQuadratic ρ Vγ) :
    ¬ HasCommonCenter I.toRepresentation A := by
  intro hcenter
  obtain ⟨E, _hEA, _hE, hcard, hqE, haxis⟩ :=
    exists_socle_dual_axis_four ρ eH I Vγ A hAV hn hq hcenter
  obtain ⟨C, hi, hs⟩ := exists_complement_of_two_step_splitting ρ.dual (annihilator ρ I)
    (two_step_splitting_of_commonAxis ρ.dual eH hsplit
      (chiefFactorsNaturalOrDual_dual ρ eH hchief) (annihilator ρ I)
      (annihilator_isCoatom ρ I hI) (annihilator_quotient_naturalOrDual ρ eH hchief I hI)
      E hcard hqE haxis)
  exact not_annihilator_complement_of_le_unique_maximal ρ W I hW hunique hI.ne_bot hIW
    ⟨C, by simpa only [inf_comm] using hi, by simpa only [sup_comm] using hs⟩

/-- Both nonsplitting exclusions used in 13.8.25, with the actual natural
head and all compatible chief-factor identifications. B.4.9(1) is retained
only as its precise two-factor premise. -/
theorem nonsplitting_exclusions
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (hsplit : TwoFactorSplitting.{u, v} H)
    (hchief : ChiefFactorsNaturalOrDual ρ eH)
    (W : Subrepresentation ρ) (hW : IsCoatom W) (hW0 : W ≠ ⊥)
    (hunique : ∀ X : Subrepresentation ρ, IsCoatom X → X = W)
    (hhead : IsNatural W.quotientRepresentation eH)
    (Vγ : Subgroup H) [IsElementaryAbelian 2 Vγ] (hq : IsQuadratic ρ Vγ) :
    (∀ A : Subgroup H, A ≤ Vγ → ¬ IsCyclic A →
      ¬ FixesHyperplane W.quotientRepresentation A) ∧
    (∀ I : Subrepresentation ρ, IsAtom I → I ≤ W →
      ∀ A : Subgroup H, A ≤ Vγ → ¬ IsCyclic A →
        ¬ HasCommonCenter I.toRepresentation A) := by
  constructor
  · intro A hAV hn
    exact not_fixesHyperplane_of_noncyclic ρ eH hsplit hchief W hW hW0 hunique
      (Or.inl hhead) Vγ A hAV hn hq
  · intro I hI hIW A hAV hn
    exact not_hasCommonCenter_of_noncyclic ρ eH hsplit hchief W hW hunique I hI hIW
      Vγ A hAV hn hq

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions
