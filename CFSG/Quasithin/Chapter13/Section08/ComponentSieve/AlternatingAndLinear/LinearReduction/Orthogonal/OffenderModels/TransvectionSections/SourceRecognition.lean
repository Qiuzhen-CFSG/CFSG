module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.TransvectionSections.Recognition
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.SourceTransport

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.SourceSeed

/-!
# The actual source sections in the transvection branch of 13.8.25

The carrier is the literal binary section U_H/V₁ and the supplied
`ConjugationSection` certifies its quotient map, kernel and conjugation action.
The actor and component are the actual star images of Uγ and K. The chosen
maximal proper W, faithful section actions, natural quotient and quadratic
critical actor are earlier source inputs, independent of this recognition.

Transport the relative-index bound through that quotient map. If the critical
subspace were fixed, the local strong-offender exclusion would fail; thus A₁
lies in U_H and its image is a nonzero line. Apply the full sieve, retaining
A₁ ≤ W versus A₁ ≰ W in the genuine subgroup preimage. Intrinsic transvection
geometry and the augmentation map then construct the rank-one actor and both
compatible section models, including the literal [W,K] inclusion.

The module proves this remaining recognition branch, not the final orthogonal
contradiction or selection of the earlier source witnesses.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.21–25,
printed pp.956–960, especially pp.957–958 and p.960 (PDF p.977).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.TransvectionSections
open Representation.BinaryOffender Subgroup BinaryPermutation
open FourStructure.CriticalTransfer Orthogonal.SourceTransport FourStructure.ChiefFactors
open scoped commutatorElement IsMulCommutative

/-- Source specialization with the chosen maximal proper W in the actual
conjugation module Ũ_H. The faithful sections are the explicit 13.8.22 inputs;
the natural quotient and its compatible marking are independently supplied.
Only contained best strong offenders are excluded. This constructs the
transvection-section witnesses required by the parent's final exclusion. -/
theorem source_compatible_sections
    {G : Type*} [Group G] [Finite G] (H V₃ V₁ K Uγ A₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (τ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (s : ConjugationSection H (Source.UH H V₃) V₁ τ)
    (W : Subrepresentation τ) (_hmax : IsCoatom W)
    (eH : Source.Hstar H ≃* Perm)
    (hK : (Source.starImage H K).map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hmodelQ : IsEightNatural W.quotientRepresentation eH)
    (hW : Function.Injective W.toRepresentation)
    (hQ : Function.Injective W.quotientRepresentation)
    (hKW : ∃ k ∈ Source.starImage H K, ∃ w : W.toSubmodule,
      W.toRepresentation k w ≠ w)
    (hA : IsElementaryTwo (Source.starImage H Uγ))
    (_hq : IsQuadratic τ (Source.starImage H Uγ))
    (hb : fixedCodim τ (Source.starImage H Uγ) ≤ 2 * rank (Source.starImage H Uγ))
    (hUγ : Uγ ≤ H) (hn : Source.UH H V₃ ≤ normalizer (A₁ : Set G))
    (hA₁ : Nat.card A₁ = 2)
    (hindex : Nat.log 2 ((Source.DH (Source.UH H V₃) Uγ A₁).relIndex (Source.UH H V₃)) ≤
      rank (Source.starImage H Uγ))
    (hnoW : ¬ ∃ B ≤ Source.starImage H Uγ, IsBestOffender W.toRepresentation B ∧
      IsStrongOffender W.toRepresentation B)
    (hnoQ : ¬ ∃ B ≤ Source.starImage H Uγ, IsBestOffender W.quotientRepresentation B ∧
      IsStrongOffender W.quotientRepresentation B) :
    A₁ ≤ Source.UH H V₃ ∧ IsAtom (s.image A₁) ∧
      ⁅Source.DH (Source.UH H V₃) Uγ A₁, Uγ⁆ = A₁ ∧
      ((A₁ ≤ preimage s W.toSubmodule ∧
          W.toSubmodule ≤ s.image (Source.DH (Source.UH H V₃) Uγ A₁) ∧
          subspaceCommutator τ W.toSubmodule (Source.starImage H Uγ) = s.image A₁) ∨
        (¬ A₁ ≤ preimage s W.toSubmodule ∧
          W.toSubmodule ⊔ s.image (Source.DH (Source.UH H V₃) Uγ A₁) = ⊤ ∧
          subspaceCommutator W.quotientRepresentation ⊤ (Source.starImage H Uγ) =
            (s.image A₁).map W.toSubmodule.mkQ)) ∧
      rank (Source.starImage H Uγ) = 1 ∧
      fixedCodim W.toRepresentation (Source.starImage H Uγ) = 1 ∧
      fixedCodim W.quotientRepresentation (Source.starImage H Uγ) = 1 ∧
      fixedCodim τ (Source.starImage H Uγ) = 2 ∧
      (fixedSpace τ (Source.starImage H Uγ)).map W.toSubmodule.mkQ =
        fixedSpace W.quotientRepresentation (Source.starImage H Uγ) ∧
      ∃ g : Perm, ∃ J : Subrepresentation W.toRepresentation,
        (Source.starImage H Uγ).map (conjugateMarking eH g).toMonoidHom = transpositionGroup ∧
        (Source.starImage H K).map (conjugateMarking eH g).toMonoidHom = alternatingGroup (Fin 8) ∧
        IsEightNatural W.quotientRepresentation (conjugateMarking eH g) ∧
        J.toSubmodule = subspaceCommutator W.toRepresentation ⊤ (Source.starImage H K) ∧
        IsEightNaturalOrCover (U := J.toSubmodule) J.toRepresentation (conjugateMarking eH g) := by
  obtain ⟨hdim, _, hdisp⟩ := critical_linear_data s Uγ A₁ hUγ hn hA₁ hindex
  have hnonfixed : ¬ s.image (Source.DH (Source.UH H V₃) Uγ A₁) ≤
      fixedSpace τ (Source.starImage H Uγ) := by
    intro hfix
    exact hnoW (strong_submodule_offender_of_fixed_subspace τ W _ hQ hA hfix hdim)
  obtain ⟨hcomm, hle, hatom, _⟩ :=
    critical_commutator_of_nonfixed s Uγ A₁ hUγ hn hA₁ hnonfixed
  refine ⟨hle, hatom, hcomm, ?_, ?_⟩
  · have hpos := image_le_iff s A₁ hle W.toSubmodule
    rcases offender_alternatives_of_critical_line τ W _ (s.image A₁)
        hatom hW hQ hA hdisp hdim with
        ⟨hSW, _, _, hs | h⟩ | ⟨hSW, _, _, hs | h⟩
    · exact (hnoQ hs).elim
    · exact Or.inl ⟨hpos.mp hSW, h⟩
    · exact (hnoW hs).elim
    · exact Or.inr ⟨fun h => hSW (hpos.mpr h), h⟩
  · exact compatible_sections_of_local_exclusions τ W (Source.starImage H K) eH
      hK hmodelQ hW hQ hKW hA hb _ (Or.inr ⟨s.image A₁, hatom, hdisp⟩) hdim hnoW hnoQ

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.TransvectionSections
