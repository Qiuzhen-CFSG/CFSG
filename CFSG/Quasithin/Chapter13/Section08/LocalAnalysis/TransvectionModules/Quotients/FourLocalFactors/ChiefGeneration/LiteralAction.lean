module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Action
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.Section
public import Theory.ElementaryAbelian.Quotient

public import Mathlib.RepresentationTheory.Coinvariants

/-!
# Transport to the literal central section

The exact kernel and surjectivity in `ConjugationSection` give the actual
multiplicative equivalence U_H/V₁ → U. We prove normality of the denominator
inside U_H and elementary abelianness of the quotient, linearize that
equivalence, and transport the supplied H* action back to the literal
quotient. Its formula on representatives is precisely conjugation.
Difference generation then transports back along the same equivalence.

This permits the source input on the literal Ũ_H to serve the arbitrary
but equivariantly identified carrier used in the assembly of 13.8.6(4).
Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.939 and 948 (PDF pp.956 and 965).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors.ChiefGeneration
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open TransvectionRecognition
variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
variable {H V₃ V₁ : Subgroup G}
variable {η : Representation (ZMod 2) (Source.Hstar H) U}

/-- The denominator is normal in the numerator, by the exact kernel. -/
theorem section_normal (s : ConjugationSection H (Source.UH H V₃) V₁ η) :
    (V₁.subgroupOf (Source.UH H V₃)).Normal := by
  rw [← s.kernel]
  exact s.quotient.normal_ker

variable [(V₁.subgroupOf (Source.UH H V₃)).Normal]

/-- The literal quotient inherits the binary structure of its supplied carrier. -/
theorem section_elementary (s : ConjugationSection H (Source.UH H V₃) V₁ η) :
    IsElementaryAbelian 2 (Source.Utilde H V₃ V₁) := by
  let : IsElementaryAbelian 2 (Multiplicative U) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      change (2 : ℕ) • x.toAdd = 0
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
      exact zero_smul (ZMod 2) x.toAdd) }
  exact IsElementaryAbelian.of_surjective s.sectionEquiv.symm.toMonoidHom
    s.sectionEquiv.symm.surjective

variable [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- Linearization of the actual quotient isomorphism. -/
noncomputable def sectionLinearEquiv (s : ConjugationSection H (Source.UH H V₃) V₁ η) :
    Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] U :=
  (MulEquiv.toAdditiveLeft s.sectionEquiv).toLinearEquiv
    (ZMod.map_smul (MulEquiv.toAdditiveLeft s.sectionEquiv).toAddMonoidHom)

theorem sectionLinearEquiv_vector (s : ConjugationSection H (Source.UH H V₃) V₁ η)
    (u : Source.UH H V₃) :
    sectionLinearEquiv s (vector H V₃ V₁ u) = (s.quotient u).toAdd := rfl

/-- The supplied H* representation transported to the literal quotient. -/
noncomputable def literalAction (s : ConjugationSection H (Source.UH H V₃) V₁ η) :
    Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)) :=
  (sectionLinearEquiv s).symm.conjRingEquiv.toMonoidHom.comp η

theorem literalAction_equivariant (s : ConjugationSection H (Source.UH H V₃) V₁ η)
    (a : Source.Hstar H) (v : Additive (Source.Utilde H V₃ V₁)) :
    sectionLinearEquiv s (literalAction s a v) = η a (sectionLinearEquiv s v) := by
  exact (sectionLinearEquiv s).apply_symm_apply _

theorem literalAction_isConjugation (s : ConjugationSection H (Source.UH H V₃) V₁ η) :
    IsConjugation H V₃ V₁ (literalAction s) := by
  intro h u
  apply (sectionLinearEquiv s).injective
  rw [literalAction_equivariant, sectionLinearEquiv_vector, sectionLinearEquiv_vector]
  exact s.conjugates h u

variable {J E F : Type*} [Group J] [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup F] [Module (ZMod 2) F]

theorem ker_eq_top_of_equivariant (ρ : Representation (ZMod 2) J E)
    (σ : Representation (ZMod 2) J F) (e : E ≃ₗ[ZMod 2] F)
    (he : ∀ g v, e (ρ g v) = σ g (e v))
    (hg : Coinvariants.ker ρ = ⊤) : Coinvariants.ker σ = ⊤ := by
  have h : Coinvariants.ker ρ ≤ (Coinvariants.ker σ).comap e.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    change e (ρ g v - v) ∈ Coinvariants.ker σ
    rw [map_sub, he]
    exact Coinvariants.sub_mem_ker g (e v)
  apply top_unique
  intro v _
  have hh := h (hg.symm ▸ (Submodule.mem_top : e.symm v ∈ (⊤ : Submodule (ZMod 2) E)))
  change e (e.symm v) ∈ Coinvariants.ker σ at hh
  simpa only [e.apply_symm_apply] using hh
end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors.ChiefGeneration

end
