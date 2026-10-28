module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.HeadHypotheses
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Heads
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.CentralExclusion
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.ChiefDecomposition.Sections
public import Theory.Representation.BinaryOffender.FlagCodimension

/-!
# B.4 and offender transfer on the literal chief sections

Every noncentral chief section is faithful for the simple L₄(2) actor.
Irreducibility follows from the cover relation, while quadraticity and the
fixed-codimension bound descend to the section. Thus the same universal B.4
input used for the heads identifies every noncentral chief factor as natural,
dual, or exterior square, with one fixed actor identification.

An exterior-square factor lies below the unique maximal submodule: the sole
remaining chief section is its four-dimensional head. Absence of offenders on
that factor implies absence on the maximal submodule by the section dimension
inequality and best-offender extraction. This is the missing transfer between
B.3.2(6) on a chief factor and the numerical sieve on the whole maximal submodule.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.1.5(8),
B.3.2(6), B.4.2/B.4.5 and 13.8.25, printed p.961. The marked B.3 calculation
and critical-pair reversal are still separate source obligations.
-/

public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
open Alignment
universe v
variable {H : Type*} [Group H] {U : Type v} [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) H U)

/-- Noncentrality excludes the full-kernel alternative in the actual simple actor. -/
theorem noncentral_section_faithful (eH : H ≃* BinaryLinear.GL NaturalSpace)
    (A B : Subrepresentation ρ) (hn : ¬ IsCentralSection ρ A B) :
    Function.Injective (sectionRepresentation ρ A B) := by
  let : IsSimpleGroup H := simple_actor eH
  apply (sectionRepresentation ρ A B).ker_eq_bot_iff.mp
  rcases (MonoidHom.normal_ker (sectionRepresentation ρ A B)).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    apply hn
    intro g v
    have he := MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top g)
    exact congrArg (fun f : Module.End (ZMod 2)
      (B.toSubmodule ⧸ (sectionLower ρ A B).toSubmodule) => f v) he

variable [Finite H] [FiniteDimensional (ZMod 2) U]

/-- All hypotheses of the universal earlier B.4 classification hold on each
noncentral chief quotient, not just on maximal quotients. -/
theorem noncentral_chief_alternatives
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (hB4 : LinearB4.{v} eH)
    (C : Subgroup H) (hC : IsElementaryTwo C) (hq : IsQuadratic ρ C)
    (hb : fixedCodim ρ C ≤ 2 * rank C)
    (A B : Subrepresentation ρ) (hAB : A ⋖ B) (hn : ¬ IsCentralSection ρ A B) :
    HeadAlternatives (sectionRepresentation ρ A B) eH := by
  apply hB4 _ (sectionRepresentation ρ A B) (noncentral_section_faithful ρ eH A B hn)
    (FieldComponents.LinearThree.ExternalModules.chief_section_irreducible ρ A B hAB)
  apply (quadraticRatio_le_two_iff _).mpr
  exact ⟨C, hC, quadratic_section ρ A B hq, (fixedCodim_section_le ρ A B C).trans hb⟩

omit [Finite H] in
/-- Containment of the upper section term gives the fixed-codimension bound
needed to pass an offender to a factor of the maximal submodule. -/
theorem fixedCodim_section_le_subrepresentation
    (A B W : Subrepresentation ρ) (hAB : A ≤ B) (hBW : B ≤ W) (C : Subgroup H) :
    fixedCodim (sectionRepresentation ρ A B) C ≤ fixedCodim W.toRepresentation C := by
  have h₁ := fixedCodim_section_add_lower_le ρ A B hAB C
  have h₂ := fixedCodim_section_add_lower_le ρ B W hBW C
  omega

/-- A forbidden best offender on the maximal submodule would contain a best
offender on the specified chief section. No splitting of the module is used. -/
theorem no_bestOffender_of_section
    (A B W : Subrepresentation ρ) (hAB : A ≤ B) (hBW : B ≤ W) (C : Subgroup H)
    (hno : ∀ D ≤ C, ¬ IsBestOffender (sectionRepresentation ρ A B) D) :
    ∀ D ≤ C, ¬ IsBestOffender W.toRepresentation D := by
  intro D hDC hD
  have hd := hD.isOffender W.toRepresentation
  have hoff : IsOffender (sectionRepresentation ρ A B) D :=
    ⟨hd.1, (fixedCodim_section_le_subrepresentation ρ A B W hAB hBW D).trans hd.2⟩
  obtain ⟨E, hED, hE⟩ := hoff.exists_bestOffender _
  exact hno E (hED.trans hDC) hE

omit [Finite H] in
/-- A six-dimensional chief quotient cannot be the four-dimensional head;
hence its upper term lies in the unique maximal submodule. -/
theorem exterior_chief_le_unique_maximal
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (hheads : AllNaturalHeads ρ eH)
    (W : Subrepresentation ρ) (hu : ∀ X : Subrepresentation ρ, IsCoatom X → X = W)
    (A B : Subrepresentation ρ) (hAB : A ⋖ B)
    (hsix : IsExteriorSquare (sectionRepresentation ρ A B) eH) : B ≤ W := by
  let : IsCoatomic (Subrepresentation ρ) := SimpleHeadQuotient.subrepresentation_coatomic ρ
  by_cases hB : B = ⊤
  · subst B
    have hA : IsCoatom A := covBy_top_iff.mp hAB
    have hhead := IsNatural.finrank_eq_four A.quotientRepresentation eH (hheads A hA)
    obtain ⟨e, _⟩ := hsix
    have hs := e.finrank_eq.trans exteriorSquare_finrank
    have hl := (sectionLowerEquiv ρ hAB.le).finrank_eq
    have hd := (sectionLower ρ A ⊤).toSubmodule.finrank_quotient_add_finrank
    have ht := A.toSubmodule.finrank_quotient_add_finrank
    have hb : Module.finrank (ZMod 2) (⊤ : Subrepresentation ρ).toSubmodule =
        Module.finrank (ZMod 2) U := finrank_top (ZMod 2) U
    omega
  · obtain ⟨X, hX, hBX⟩ := (eq_top_or_exists_le_coatom B).resolve_left hB
    exact (hu X hX) ▸ hBX

/-- The remaining source obligation is precisely exclusion of an exterior
chief factor below the maximal submodule. B.4 recognition and the cohomology
step, including the absence of central factors, are discharged here. -/
theorem chief_factors_of_exterior_exclusion
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (hheads : AllNaturalHeads ρ eH)
    (W : Subrepresentation ρ) (hW : IsCoatom W)
    (hu : ∀ X : Subrepresentation ρ, IsCoatom X → X = W)
    (hB4 : LinearB4.{v} eH)
    (C : Subgroup H) (hC : IsElementaryTwo C) (hq : IsQuadratic ρ C)
    (hb : fixedCodim ρ C ≤ 2 * rank C)
    (hno : ∀ A B : Subrepresentation ρ, A ⋖ B → B ≤ W →
      ¬ IsCentralSection ρ A B → ¬ IsExteriorSquare (sectionRepresentation ρ A B) eH) :
    ChiefFactorsNaturalOrDual ρ eH := by
  apply central_chief_exclusion ρ eH hheads W hW hu
  intro A B hAB hn
  rcases noncentral_chief_alternatives ρ eH hB4 C hC hq hb A B hAB hn with h | h
  · exact h
  · exact (hno A B hAB (exterior_chief_le_unique_maximal ρ eH hheads W hu A B hAB h) hn h).elim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
