module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections.Extensions
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections.SourceConstituents

/-!
# Source assemblies for the two strong-offender branches

The source wrappers retain the actual conjugation section, the chosen maximal
submodule, the marked quotient and the branch-specific offender clauses. The
quotient branch additionally takes the earlier equality
`Ũ_H = [Ũ_H,K]`; the resulting whole-H commutator is then obtained from the
proved ambient lemma, rather than from central layers in a flag. The
submodule branch keeps the `A₁` noncontainment, the absence of a quotient
strong best offender and the contained strong best offender on `W` while
recognizing the literal `[W,K]` subrepresentation.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.21–25, printed pp.956–960, PDF pp.974–977.
-/

@[expose] public section

open Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections.SourceConstituents
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections.Extensions
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections.Extensions

universe v

variable {G : Type v} [Group G] [Finite G]

variable {H V₃ V₁ Uγ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/- The quotient branch of 13.8.25, with all earlier source witnesses retained.
The supplied series and its unique natural factor are the output of the
constituent stage; `hgen` is the independent 13.8.21 commutator equality. -/
theorem source_strong_quotient_extension
    (τ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hτ : IsSourceAction H V₃ V₁ τ)
    (W : Subrepresentation τ) (hW : IsCoatom W)
    (eH : Source.Hstar H ≃* Perm) (Kstar : Subgroup (Source.Hstar H))
    (hK : Kstar.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hQ : IsEightNatural W.quotientRepresentation eH)
    (hKW : ∃ k ∈ Kstar, ∃ w : W.toSubmodule,
      W.toRepresentation k w ≠ w)
    (hA : IsElementaryTwo (Source.starImage H Uγ))
    (hq : IsQuadratic τ (Source.starImage H Uγ))
    (hb : fixedCodim τ (Source.starImage H Uγ) ≤
      2 * rank (Source.starImage H Uγ))
    (hstrong : ∃ B ≤ Source.starImage H Uγ,
      IsStrongOffender W.quotientRepresentation B)
    (hB4 : SymmetricB4.{v} Kstar eH)
    (hgen : subspaceCommutator τ ⊤ Kstar = ⊤)
    (hfactor : ∀ s : NaturalCentralSeries W.toRepresentation Kstar eH,
      ∃ i : ℕ, i < s.length ∧
        IsEightNatural
          (sectionRepresentation W.toRepresentation (s.space i) (s.space (i + 1))) eH ∧
        (∀ j < s.length,
          IsEightNatural
            (sectionRepresentation W.toRepresentation (s.space j) (s.space (j + 1))) eH →
          j = i) ∧
        IsIrreducible
          ((sectionRepresentation W.toRepresentation (s.space i) (s.space (i + 1))).comp
            Kstar.subtype)) :
    ∃ J : Subrepresentation W.toRepresentation,
      J.toSubmodule = subspaceCommutator W.toRepresentation ⊤ Kstar ∧
      IsEightNaturalOrCover (U := J.toSubmodule) J.toRepresentation eH ∧
      subspaceCommutator τ W.toSubmodule ⊤ =
        subspaceCommutator τ W.toSubmodule Kstar := by
  obtain ⟨s⟩ := source_strong_quotient_series H V₃ V₁ Uγ τ hτ W hW eH Kstar hK hQ
    hKW hA hq hb hstrong hB4
  obtain ⟨i, hi, hNi, huniq, hirr⟩ := hfactor s
  obtain ⟨hwhole, hmodel⟩ := whole_commutator_extension_of_unique_natural
    τ W eH Kstar hK hQ hgen s i hi hNi huniq hirr
  obtain ⟨J, hJ, hJmodel⟩ := hmodel
  exact ⟨J, hJ, hJmodel, hwhole⟩

/- The second strong-offender branch. The branch-specific clauses are all
arguments of this theorem, including the actual subgroup preimage condition
for `A₁`, the absence of a contained quotient strong best offender, and the
contained strong best offender on `W`. -/
theorem source_strong_submodule_extension
    (A₁ : Subgroup G)
    (τ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hτ : IsSourceAction H V₃ V₁ τ)
    (W : Subrepresentation τ) (hW : IsCoatom W)
    (eH : Source.Hstar H ≃* Perm) (Kstar : Subgroup (Source.Hstar H))
    (hK : Kstar.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (eK : Kstar ≃* BinaryLinear.GL OrthogonalQuotient.FourSpace)
    (hQ : IsEightNatural W.quotientRepresentation eH)
    (hKW : ∃ k ∈ Kstar, ∃ w : W.toSubmodule,
      W.toRepresentation k w ≠ w)
    (hA : IsElementaryTwo (Source.starImage H Uγ))
    (hq : IsQuadratic τ (Source.starImage H Uγ))
    (hb : fixedCodim τ (Source.starImage H Uγ) ≤
      2 * rank (Source.starImage H Uγ))
    (hA₁ : ¬ A₁ ≤ ((Subgroup.toAddSubgroup.symm W.toSubmodule.toAddSubgroup).comap
      (sourceProjection H V₃ V₁)).map (Source.UH H V₃).subtype)
    (hnoQ : ¬ ∃ B ≤ Source.starImage H Uγ,
      IsBestOffender W.quotientRepresentation B ∧
      IsStrongOffender W.quotientRepresentation B)
    (hstrong : ∃ B ≤ Source.starImage H Uγ,
      IsBestOffender W.toRepresentation B ∧
      IsStrongOffender W.toRepresentation B)
    (hS : SymmetricB4.{v} Kstar eH)
    (hC : ComponentB4.{v} Kstar eH eK)
    (hfactor : ∀ s : NaturalCentralSeries W.toRepresentation Kstar eH,
      ∃ i : ℕ, i < s.length ∧
        IsEightNatural
          (sectionRepresentation W.toRepresentation (s.space i) (s.space (i + 1))) eH ∧
        (∀ j < s.length,
          IsEightNatural
            (sectionRepresentation W.toRepresentation (s.space j) (s.space (j + 1))) eH →
          j = i) ∧
        IsIrreducible
          ((sectionRepresentation W.toRepresentation (s.space i) (s.space (i + 1))).comp
            Kstar.subtype)) :
    ∃ J : Subrepresentation W.toRepresentation,
      J.toSubmodule = subspaceCommutator W.toRepresentation ⊤ Kstar ∧
      IsEightNaturalOrCover (U := J.toSubmodule) J.toRepresentation eH := by
  obtain ⟨s⟩ := source_strong_submodule_series H V₃ V₁ Uγ A₁ τ hτ W hW eH Kstar hK eK hQ
    hKW hA hq hb hA₁ hnoQ hstrong hS hC
  obtain ⟨i, hi, hNi, huniq, hirr⟩ := hfactor s
  have hmodel := commutator_model_of_unique_natural W.toRepresentation eH Kstar hK s i hi
    hNi huniq hirr
  obtain ⟨J, hJ, hJmodel⟩ := hmodel
  exact ⟨J, hJ, hJmodel⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections.Extensions

end
