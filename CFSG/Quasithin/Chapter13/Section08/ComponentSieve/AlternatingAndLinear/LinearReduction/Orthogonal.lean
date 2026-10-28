module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalCentralizer
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.CriticalLine
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.SourceTransport

/-!
# The orthogonal branch of Aschbacher–Smith 13.8.25

The imported development proves the strong-offender contradiction from actual
orthogonal sections and the critical commutator line. The index-two critical
centralizer is derived from the distinct centers of the disjoint transpositions.
It also supplies the rank-one contradiction using actual natural/augmentation
models and the marked transposition. This file assembles those deductions with
the actual source offender alternatives: both strong branches are eliminated by
the critical-pair subspace, and the remaining rank-one branch is eliminated by
the larger critical actor from 13.8.23.

Source: *The Classification of Quasithin Groups*, combined manuscript of
1 March 2004, printed pp.959–960, PDF pp.976–977. The preceding quotient,
critical-pair and offender-model modules provide the source-specific inputs;
the theorem below performs the final branch elimination.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction

open Representation BinaryPermutation BinaryOffender
open Subgroup
open CFSG.Quasithin.ChapterB.Offenders
open FourStructure FourStructure.ChiefFactors FourStructure.CriticalTransfer
open OrthogonalQuotient.B4Extraction
open Orthogonal.SourceTransport
open OffenderModels

open scoped IsMulCommutative

universe v

variable {G : Type v} [Group G] [Finite G]

section Assembly

variable (H V₃ V₁ K Uγ A₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (τ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
  (s : ConjugationSection H (Source.UH H V₃) V₁ τ)
  (W : Subrepresentation τ) (eH : Source.Hstar H ≃* Perm)

/-- Once the actual offender alternatives have been constructed, every branch
of the source dichotomy is impossible.  In the first two branches the
`MarkedModels` witness supplies the two orthogonal sections; the actual
critical-pair data then gives the index-two centralizer and the
six-versus-five contradiction.  In the last branch `RankOneData` is the
transport of 13.8.23, and its larger actor supplies the line displacement used
by the pointwise-centralizer contradiction.

This theorem is deliberately stated at the source interfaces.  In particular,
the actor marking is shared by the quotient, the commutator section and the
critical actor, while the critical line remains the image of the actual
subgroup `A₁`.
-/
theorem orthogonal_branch_contradiction_of_models
    (hmodels : OffenderModels.SourceModelAlternatives H V₃ V₁ K Uγ A₁ τ s W eH)
    (hUγ : Uγ ≤ H) (hn : Source.UH H V₃ ≤ normalizer (A₁ : Set G))
    (hA₁ : Nat.card A₁ = 2)
    (hindex : Nat.log 2 ((Source.DH (Source.UH H V₃) Uγ A₁).relIndex
      (Source.UH H V₃)) ≤ rank (Source.starImage H Uγ))
    {F : Subgroup G}
    (hRank : ∀
      (_ : ¬ OffenderModels.HasStrongBestOffender W.quotientRepresentation
        (Source.starImage H Uγ))
      (_ : ¬ OffenderModels.HasStrongBestOffender W.toRepresentation
        (Source.starImage H Uγ)),
      RankOneData s W Uγ F A₁) : False := by
  obtain ⟨hD, hSdim, hdisp⟩ := critical_linear_data s Uγ A₁ hUγ hn hA₁ hindex
  rcases hmodels with hstrongQ | ⟨hnoQ, hrest⟩
  · obtain ⟨_, g, hm, _⟩ := hstrongQ
    obtain ⟨m⟩ := hm
    exact orthogonal_sections_critical_line_contradiction τ W m.J
      (conjugateMarking eH g) (m.model) (Or.inl m.quotient_natural)
      (Source.starImage H Uγ) m.actor_marking
      (s.image (Source.DH (Source.UH H V₃) Uγ A₁)) (s.image A₁)
      hD hSdim hdisp
  · rcases hrest with hstrongW | hrank
    · obtain ⟨_, hstrong, g, hm, _⟩ := hstrongW
      obtain ⟨m⟩ := hm
      exact orthogonal_sections_critical_line_contradiction τ W m.J
        (conjugateMarking eH g) (m.model) (Or.inl m.quotient_natural)
        (Source.starImage H Uγ) m.actor_marking
        (s.image (Source.DH (Source.UH H V₃) Uγ A₁)) (s.image A₁)
        hD hSdim hdisp
    · obtain ⟨hnoW, _, _, _, hposition, g, ht⟩ := hrank
      obtain ⟨t⟩ := ht
      let hRank' := hRank hnoQ hnoW
      exact rank_one_orthogonal_contradiction τ W t.J
        (conjugateMarking eH g) t.model (Or.inl t.quotient_natural)
        hRank'.submodule_faithful hRank'.quotient_faithful
        (Source.starImage H Uγ) (Source.starImage H F)
        hRank'.actor_ne_bot hRank'.actor_lt t.actor_marking
        hRank'.fixedCodim_eq_two.le
        (s.image A₁) hRank'.line_atom hRank'.displacements

/-- Source-facing assembly of the orthogonal exclusion.  The maximal quotient,
its marked natural action, the nontrivial component action and the earlier
B.4 inputs are used only to construct `SourceModelAlternatives`; the actual
larger critical actor is supplied by the 13.8.23 transport record.

The parabolic outcome is represented by the marked component hypothesis and
the middle-node data already consumed by the quotient-selection theorem. -/
theorem source_orthogonal_branch_exclusion
    (hW : IsCoatom W) (hK : (Source.starImage H K).map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hQ : IsEightNatural W.quotientRepresentation eH)
    (hKW : ∃ k ∈ Source.starImage H K, ∃ w : W.toSubmodule,
      W.toRepresentation k w ≠ w)
    (hKH : K ≤ H) (hfull : ⁅Source.UH H V₃, K⁆ = Source.UH H V₃)
    (hA : IsElementaryTwo (Source.starImage H Uγ))
    (hq : IsQuadratic τ (Source.starImage H Uγ))
    (hb : fixedCodim τ (Source.starImage H Uγ) ≤
      2 * rank (Source.starImage H Uγ))
    (hUγ : Uγ ≤ H) (hn : Source.UH H V₃ ≤ normalizer (A₁ : Set G))
    (hA₁ : Nat.card A₁ = 2)
    (hindex : Nat.log 2 ((Source.DH (Source.UH H V₃) Uγ A₁).relIndex
      (Source.UH H V₃)) ≤ rank (Source.starImage H Uγ))
    (hS : SymmetricB4.{v} (Source.starImage H K) eH)
    (hC : ∀ eK : Source.starImage H K ≃* BinaryLinear.GL OrthogonalQuotient.FourSpace,
      ComponentB4.{v} (Source.starImage H K) eH eK)
    {F : Subgroup G}
    (hRank : ∀
      (_ : ¬ OffenderModels.HasStrongBestOffender W.quotientRepresentation
        (Source.starImage H Uγ))
      (_ : ¬ OffenderModels.HasStrongBestOffender W.toRepresentation
        (Source.starImage H Uγ)),
      RankOneData s W Uγ F A₁) : False := by
  have halt := source_offender_model_alternatives H V₃ V₁ K Uγ A₁ τ s W hW eH
    hK hQ hKW hKH hfull hA hq hb hUγ hn hA₁ hindex hS hC
  exact orthogonal_branch_contradiction_of_models H V₃ V₁ K Uγ A₁ τ s W eH
    halt hUγ hn hA₁ hindex hRank

end Assembly

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction
