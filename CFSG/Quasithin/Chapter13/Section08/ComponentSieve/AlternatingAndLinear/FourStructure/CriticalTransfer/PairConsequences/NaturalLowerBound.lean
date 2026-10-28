module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.Section
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Basic

/-!
# The same-natural-action case of the irreducible lower bound

When the irreducible submodule and the head have equivariant natural
identifications for the same actor, their fixed codimensions agree. The
nonsplitting hyperplane exclusion on the head therefore supplies the missing
reason why the centralized intersection has codimension at least two.
The final lemma applies this argument to the actual image of Source.DH,
using the established intersection-centralizer theorem. The contragredient
case needs a separate argument and is not claimed here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.25,
printed pp.961–962, using the nonsplitting deduction from B.4.9(1).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
open Representation.BinaryOffender Subgroup
variable {K U E : Type*} [Group K] [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) U] [FiniteDimensional (ZMod 2) E]

omit [FiniteDimensional (ZMod 2) U] [FiniteDimensional (ZMod 2) E] in
/-- Equivariant identification transports the fixed codimension for the same actor. -/
theorem fixedCodim_eq_of_equivariant
    (ρ : Representation (ZMod 2) K U) (τ : Representation (ZMod 2) K E)
    (e : U ≃ₗ[ZMod 2] E) (he : ∀ g u, e (ρ g u) = τ g (e u)) (B : Subgroup K) :
    fixedCodim ρ B = fixedCodim τ B := by
  have hmap : (fixedSpace ρ B).map e.toLinearMap = fixedSpace τ B := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩ b
      change τ (b : K) (e u) = e u
      rw [← he]
      exact congrArg e (hu b)
    · intro v hv
      refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
      intro b
      apply e.injective
      change e (ρ (b : K) (e.symm v)) = e (e.symm v)
      rw [he, e.apply_symm_apply]
      exact hv b
  exact (Submodule.Quotient.equiv _ _ e hmap).finrank_eq

/-- Pointwise fixation of the intersection bounds its section codimension
from below by the fixed codimension on the restricted representation. -/
theorem fixedCodim_le_section_codimension
    (ρ : Representation (ZMod 2) K U) (N : Subrepresentation ρ)
    (D : Submodule (ZMod 2) U) (B : Subgroup K)
    (hfix : N.toSubmodule ⊓ D ≤ fixedSpace ρ B) :
    fixedCodim N.toRepresentation B ≤
      Module.finrank (ZMod 2) (N.toSubmodule ⧸ D.comap N.toSubmodule.subtype) := by
  have hle : D.comap N.toSubmodule.subtype ≤ fixedSpace N.toRepresentation B := by
    intro v hv b
    exact Subtype.ext (hfix ⟨v.property, hv⟩ b)
  have hd := (D.comap N.toSubmodule.subtype).finrank_quotient_add_finrank
  have hf := fixedCodim_add_finrank N.toRepresentation B
  have hm := Submodule.finrank_mono hle
  omega

/-- The same natural action on the irreducible submodule and the head
transfers the nonsplitting hyperplane exclusion. The dual alternative is
deliberately not included in this statement. -/
theorem section_codimension_ge_two_of_same_natural_head
    (ρ : Representation (ZMod 2) K U) (N W : Subrepresentation ρ)
    (D : Submodule (ZMod 2) U) (A B : Subgroup K) (hAB : A ≤ B)
    (hA : 1 < rank A) (hfix : N.toSubmodule ⊓ D ≤ fixedSpace ρ B)
    (eK : K ≃* BinaryLinear.GL ChiefFactors.NaturalSpace)
    (hN : ChiefFactors.IsNatural N.toRepresentation eK)
    (hW : ChiefFactors.IsNatural W.quotientRepresentation eK)
    (haxis : ∀ C ≤ B, 1 < rank C → 1 < fixedCodim W.quotientRepresentation C) :
    2 ≤ Module.finrank (ZMod 2) (N.toSubmodule ⧸ D.comap N.toSubmodule.subtype) := by
  obtain ⟨eN, heN⟩ := hN
  obtain ⟨eW, heW⟩ := hW
  have he : ∀ g u, (eN.trans eW.symm) (N.toRepresentation g u) =
      W.quotientRepresentation g ((eN.trans eW.symm) u) := by
    intro g u
    apply eW.injective
    simp only [LinearEquiv.trans_apply, eW.apply_symm_apply, heN, heW]
  have hc := fixedCodim_eq_of_equivariant N.toRepresentation W.quotientRepresentation
    (eN.trans eW.symm) he A
  have hf : N.toSubmodule ⊓ D ≤ fixedSpace ρ A := by
    intro u hu a
    exact hfix hu ⟨a, hAB a.property⟩
  have hl := fixedCodim_le_section_codimension ρ N D A hf
  have ha := haxis A hAB hA
  omega

variable {G : Type*} [Group G] [Finite G]
  {H UH Z : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}

/-- The actual source denominator in the same-natural-action case. All
subgroup intersections and the central quotient are those of `Source.DH`;
the intersection-centralizer conclusion is derived from A₁ not lying in I. -/
theorem critical_section_codimension_ge_two_of_same_natural_head
    (s : ConjugationSection H UH Z ρ)
    (I J Ug Vg A : Subgroup G) (hZI : Z ≤ I) (hIU : I ≤ UH)
    (N W : Subrepresentation ρ) (hN : s.image I = N.toSubmodule)
    (hUgVg : Ug ≤ Vg) (hVgH : Vg ≤ H) (hUJ : UH ≤ J)
    (hUA : UH ≤ normalizer (A : Set G))
    (hcentralizer : ⁅J ⊓ centralizer (Ug : Set G), Vg⁆ ≤ A)
    (hA : Nat.card A = 2) (hnot : ¬ A ≤ I)
    (hrank : 1 < rank (Source.starImage H Ug))
    (eH : Source.Hstar H ≃* BinaryLinear.GL ChiefFactors.NaturalSpace)
    (hNat : ChiefFactors.IsNatural N.toRepresentation eH)
    (hHead : ChiefFactors.IsNatural W.quotientRepresentation eH)
    (haxis : ∀ B ≤ Source.starImage H Vg, 1 < rank B →
      1 < fixedCodim W.quotientRepresentation B) :
    2 ≤ Module.finrank (ZMod 2)
      (N.toSubmodule ⧸ (s.image (Source.DH UH Ug A)).comap N.toSubmodule.subtype) := by
  have hfix := (s.critical_intersection_centralizes I J Ug Vg A hZI hIU N hN
    hUgVg hVgH hUJ hUA hcentralizer hA hnot).2.2
  rw [hN] at hfix
  apply section_codimension_ge_two_of_same_natural_head ρ N W _
    (Source.starImage H Ug) (Source.starImage H Vg) _ hrank hfix eH hNat hHead haxis
  exact map_mono (fun x hx => hUgVg hx)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
