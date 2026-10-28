module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections.Constituents
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections.Models
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections.SourceConstituents
public import Theory.Representation.BinaryNaturalDual.FourActors.Model

/-!
# Recognition in both strong orthogonal offender branches

For a classified series in the actual maximal submodule, the strong-quotient
branch gives a unique natural constituent under the same coordinates as the
quotient and the whole actor. In the strong-submodule branch, a natural
constituent identifies the whole actor first, giving fixed codimension three
and the same uniqueness conclusion.

The source assemblies construct the series, prove uniqueness and component
irreducibility of its natural factor, and recognize the literal commutator.
Its natural-or-augmentation-core identification uses the same marking as the
actor and quotient. The earlier ambient commutator equality identifies its
image with [W,H]. Only the explicitly permitted universal B.4 inputs remain;
the extension and cohomology deductions are proved. In the second branch we
retain A₁ noncontainment and the absence of a strong best quotient offender.

Source: Aschbacher–Smith 13.8.21–25, especially printed p.960, PDF p.977
(1 March 2004 manuscript). Final offender-alternative assembly is separate.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.Offenders

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- Multiplicity in the strong-quotient branch, after classifying the
constituents. Actor, component, quotient and factors share one marking. -/
theorem strong_quotient_constituent_multiplicity
    (ρ : Representation (ZMod 2) H U) (W : Subrepresentation ρ)
    (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hQ : IsEightNatural W.quotientRepresentation eH)
    (s : NaturalCentralSeries W.toRepresentation K eH)
    (A : Subgroup H) (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hstrong : ∃ B ≤ A, IsStrongOffender W.quotientRepresentation B) :
    ∃ g : Perm, A.map (conjugateMarking eH g).toMonoidHom = D 8 ∧
      K.map (conjugateMarking eH g).toMonoidHom = alternatingGroup (Fin 8) ∧
      IsEightNatural W.quotientRepresentation (conjugateMarking eH g) ∧
      rank A = 4 ∧ fixedCodim W.quotientRepresentation A = 3 ∧
      fixedCodim W.toRepresentation A ≤ 5 ∧
      ∃! i : ℕ, i < s.length ∧ IsEightNatural
        (sectionRepresentation W.toRepresentation (s.space i) (s.space (i + 1)))
        (conjugateMarking eH g) := by
  obtain ⟨g, hg, hQg, hr, hq, hw⟩ :=
    strong_quotient_marking_and_bounds ρ W eH hQ A hA hbound hstrong
  refine ⟨g, hg, alternating_marking_conjugate eH K hK g, hQg, hr, hq, hw, ?_⟩
  exact (s.conjugate W.toRepresentation K eH g).exists_unique_natural
    W.toRepresentation K (conjugateMarking eH g) A hg hw

/-- Multiplicity in the strong-submodule branch. Strongness passes to a
natural constituent; enlargement then marks the whole actor, not only B. -/
theorem strong_submodule_constituent_multiplicity
    (ρ : Representation (ZMod 2) H U) (W : Subrepresentation ρ)
    (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hQ : IsEightNatural W.quotientRepresentation eH)
    (s : NaturalCentralSeries W.toRepresentation K eH)
    (A : Subgroup H) (hA : IsElementaryTwo A)
    (hstrong : ∃ B ≤ A, IsStrongOffender W.toRepresentation B) :
    ∃ g : Perm, A.map (conjugateMarking eH g).toMonoidHom = D 8 ∧
      K.map (conjugateMarking eH g).toMonoidHom = alternatingGroup (Fin 8) ∧
      IsEightNatural W.quotientRepresentation (conjugateMarking eH g) ∧
      rank A = 4 ∧ fixedCodim W.toRepresentation A = 3 ∧
      ∃! i : ℕ, i < s.length ∧ IsEightNatural
        (sectionRepresentation W.toRepresentation (s.space i) (s.space (i + 1)))
        (conjugateMarking eH g) := by
  obtain ⟨i, _, hNi⟩ := s.natural_exists
  obtain ⟨B, hBA, hB⟩ := hstrong
  obtain ⟨_, g, hg, _, hr, hw⟩ := strong_constituent_actor_marking
    W.toRepresentation eH (s.space i) (s.space (i + 1)) hNi A B hA hBA hB
  refine ⟨g, hg, alternating_marking_conjugate eH K hK g,
    hQ.conjugate _ eH g, hr, hw, ?_⟩
  exact (s.conjugate W.toRepresentation K eH g).exists_unique_natural
    W.toRepresentation K (conjugateMarking eH g) A hg (by omega)

open SourceConstituents FourStructure.ChiefFactors
open OrthogonalQuotient.B4Extraction
open scoped IsMulCommutative

universe v

/-- The strong-quotient branch on the actual conjugation section. The chosen
maximal W, natural quotient and earlier ambient commutator equality are
supplied source witnesses. The series, multiplicity and extension conclusions
are all derived, and the literal [W,H] model shares the whole-actor marking. -/
theorem source_strong_quotient_models
    {G : Type v} [Group G] [Finite G] (H V₃ V₁ Uγ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (τ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hτ : IsSourceAction H V₃ V₁ τ)
    (W : Subrepresentation τ) (hW : IsCoatom W)
    (eH : Source.Hstar H ≃* Perm) (Kstar : Subgroup (Source.Hstar H))
    (hK : Kstar.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hQ : IsEightNatural W.quotientRepresentation eH)
    (hKW : ∃ k ∈ Kstar, ∃ w : W.toSubmodule, W.toRepresentation k w ≠ w)
    (hgen : subspaceCommutator τ ⊤ Kstar = ⊤)
    (hA : IsElementaryTwo (Source.starImage H Uγ))
    (hq : IsQuadratic τ (Source.starImage H Uγ))
    (hb : fixedCodim τ (Source.starImage H Uγ) ≤ 2 * rank (Source.starImage H Uγ))
    (hstrong : ∃ B ≤ Source.starImage H Uγ,
      IsBestOffender W.quotientRepresentation B ∧
      IsStrongOffender W.quotientRepresentation B)
    (hB4 : SymmetricB4.{v} Kstar eH) :
    ∃ g : Perm,
      Nonempty (MarkedModels τ W Kstar (Source.starImage H Uγ) (conjugateMarking eH g)) ∧
      fixedCodim W.toRepresentation (Source.starImage H Uγ) ≤ 5 := by
  have hs : ∃ B ≤ Source.starImage H Uγ, IsStrongOffender W.quotientRepresentation B := by
    obtain ⟨B, hBA, _, hB⟩ := hstrong
    exact ⟨B, hBA, hB⟩
  obtain ⟨s⟩ := source_strong_quotient_series H V₃ V₁ Uγ τ hτ W hW eH Kstar hK
    hQ hKW hA hq hb hs hB4
  obtain ⟨g, hg, hKg, hQg, _, _, hw, _⟩ :=
    strong_quotient_constituent_multiplicity τ W eH Kstar hK hQ s
      (Source.starImage H Uγ) hA hb hs
  exact ⟨g, marked_models_of_series τ W (conjugateMarking eH g) Kstar
    (Source.starImage H Uγ) hKg hg hQg hgen
    (s.conjugate W.toRepresentation Kstar eH g) hw, hw⟩

/-- The strong-submodule branch of 13.8.22(2). The actual A₁ noncontainment,
absence of a strong best quotient offender, and contained strong best
offender on W are retained. Constituent extraction marks the whole actor;
recognition preserves the commutator subrepresentation and both inclusions.
No model for all of W is assumed or asserted. -/
theorem source_strong_submodule_models
    {G : Type v} [Group G] [Finite G] (H V₃ V₁ Uγ A₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (τ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hτ : IsSourceAction H V₃ V₁ τ)
    (W : Subrepresentation τ) (hW : IsCoatom W)
    (eH : Source.Hstar H ≃* Perm) (Kstar : Subgroup (Source.Hstar H))
    (hK : Kstar.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hQ : IsEightNatural W.quotientRepresentation eH)
    (hKW : ∃ k ∈ Kstar, ∃ w : W.toSubmodule, W.toRepresentation k w ≠ w)
    (hgen : subspaceCommutator τ ⊤ Kstar = ⊤)
    (hA : IsElementaryTwo (Source.starImage H Uγ))
    (hq : IsQuadratic τ (Source.starImage H Uγ))
    (hb : fixedCodim τ (Source.starImage H Uγ) ≤ 2 * rank (Source.starImage H Uγ))
    (hA₁ : ¬ A₁ ≤ ((Subgroup.toAddSubgroup.symm W.toSubmodule.toAddSubgroup).comap
      (sourceProjection H V₃ V₁)).map (Source.UH H V₃).subtype)
    (hnoQ : ¬ ∃ B ≤ Source.starImage H Uγ, IsBestOffender W.quotientRepresentation B ∧
      IsStrongOffender W.quotientRepresentation B)
    (hstrong : ∃ B ≤ Source.starImage H Uγ, IsBestOffender W.toRepresentation B ∧
      IsStrongOffender W.toRepresentation B)
    (hS : SymmetricB4.{v} Kstar eH)
    (hC : ∀ eK : Kstar ≃* BinaryLinear.GL OrthogonalQuotient.FourSpace,
      ComponentB4.{v} Kstar eH eK) :
    ∃ g : Perm,
      Nonempty (MarkedModels τ W Kstar (Source.starImage H Uγ) (conjugateMarking eH g)) ∧
      fixedCodim W.toRepresentation (Source.starImage H Uγ) = 3 := by
  -- The genuine A₈/GL₄(2) comparison is the attributed ATLAS port reused in
  -- FourActors.Model; no additional component-isomorphism witness is assumed.
  let eK : Kstar ≃* BinaryLinear.GL OrthogonalQuotient.FourSpace :=
    ((eH.subgroupMap Kstar).trans (MulEquiv.subgroupCongr hK)).trans
      BinaryNaturalDual.FourActors.linearAlternatingEquiv.symm
  obtain ⟨s⟩ := source_strong_submodule_series H V₃ V₁ Uγ A₁ τ hτ W hW eH Kstar hK
    eK hQ hKW hA hq hb hA₁ hnoQ hstrong hS (hC eK)
  have hs : ∃ B ≤ Source.starImage H Uγ, IsStrongOffender W.toRepresentation B := by
    obtain ⟨B, hBA, _, hB⟩ := hstrong
    exact ⟨B, hBA, hB⟩
  obtain ⟨g, hg, hKg, hQg, _, hw, _⟩ :=
    strong_submodule_constituent_multiplicity τ W eH Kstar hK hQ s
      (Source.starImage H Uγ) hA hs
  exact ⟨g, marked_models_of_series τ W (conjugateMarking eH g) Kstar
    (Source.starImage H Uγ) hKg hg hQg hgen
    (s.conjugate W.toRepresentation Kstar eH g) (by omega), hw⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections
