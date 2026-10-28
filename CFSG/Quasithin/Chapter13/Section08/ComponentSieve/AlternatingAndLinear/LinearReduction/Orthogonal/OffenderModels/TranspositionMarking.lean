module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.Marking
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalCentralizer

/-!
# Compatible transposition markings

The exhaustive degree-eight offender list shows that only the single-swap
family has fixed codimension one on the natural module or augmentation cover.
The exceptional group, all hyperplanes, the even part and the regular eight
groups have larger fixed codimension. This identifies the actor itself with
the marked transposition group and proves its rank is one.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, B.3.2(5–6), printed pp.83–84, and its use in
13.8.25, printed p.960, PDF p.977. Recognition of the model inside an arbitrary
faithful section is a separate obligation; it is not inferred from dimension.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels
open Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders
open CFSG.Quasithin.ChapterB.Offenders.Eight

private theorem transpositionGroup_eq : transpositionGroup = disjointTranspositions 8 1 := by
  unfold transpositionGroup disjointTranspositions
  congr 1
  ext g
  constructor
  · intro hg
    exact ⟨0, by decide, hg⟩
  · rintro ⟨i, hi, rfl⟩
    have he : i = 0 := Fin.ext (by change i.val = 0; omega)
    subst i
    rfl

private theorem caseB_codim_one (A : Subgroup Perm) (hA : CaseBFamily 8 (by decide) A)
    (hc : fixedCodim (naturalRepresentation (Fin 8)) A = 1 ∨
      fixedCodim (coreRepresentation (Fin 8)) A = 1) :
    IsConjugateTo A transpositionGroup := by
  rcases hA with ⟨m, hm0, hm, hmconj⟩ | he | he | ⟨B, hBD, _, he⟩
  · have hcod := fixedCodim_disjointTranspositions hm0 hm
    have hm1 : m = 1 := by
      rw [hmconj.fixedCodim_eq, hmconj.fixedCodim_eq] at hc
      rcases hc with hc | hc <;> split_ifs at hcod <;> omega
    subst m
    rwa [transpositionGroup_eq]
  · rw [he.fixedCodim_eq, he.fixedCodim_eq,
      fixedCodim_exceptional.2.2.2, fixedCodim_exceptional.2.2.1] at hc
    omega
  · rw [he.fixedCodim_eq, he.fixedCodim_eq,
      fixedCodim_evenPart.2.2.2, fixedCodim_evenPart.2.2.1] at hc
    omega
  · rw [he.fixedCodim_eq, he.fixedCodim_eq,
      (fixedCodim_hyperplane hBD).2, (fixedCodim_hyperplane hBD).1] at hc
    omega

/-- An elementary actor of fixed codimension one on the natural module
is a conjugate of the transposition group. All B.3.2(6) alternatives are checked. -/
theorem natural_codim_one_conjugate_transposition (A : Subgroup Perm)
    (hA : IsElementaryTwo A) (hc : fixedCodim (naturalRepresentation (Fin 8)) A = 1) :
    IsConjugateTo A transpositionGroup := by
  have hp := hA.rank_pos
  rcases EightExhaustion.caseBFamily_or_isRegularEight_of_isOffender_natural
      (show IsOffender (naturalRepresentation (Fin 8)) A from ⟨hA, by omega⟩) with hb | hr
  · exact caseB_codim_one A hb (Or.inl hc)
  · have he := fixedCodim_natural_regularEight hr
    omega

/-- The augmentation-cover calculation gives the same transposition marking. -/
theorem core_codim_one_conjugate_transposition (A : Subgroup Perm)
    (hA : IsElementaryTwo A) (hc : fixedCodim (coreRepresentation (Fin 8)) A = 1) :
    IsConjugateTo A transpositionGroup := by
  have hp := hA.rank_pos
  exact caseB_codim_one A
    (EightExhaustion.caseBFamily_of_isOffender_core ⟨hA, by omega⟩) (Or.inr hc)

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

/-- On either permitted model, fixed codimension one forces actor rank one
and gives a compatible transposition marking. Both modules can subsequently
be transported by this same inner coordinate change. -/
theorem codim_one_actor_marking (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (hmodel : IsEightNaturalOrCover ρ eH)
    (A : Subgroup H) (hA : IsElementaryTwo A) (hc : fixedCodim ρ A = 1) :
    rank A = 1 ∧ ∃ g : Perm,
      A.map (conjugateMarking eH g).toMonoidHom = transpositionGroup ∧
      IsEightNaturalOrCover ρ (conjugateMarking eH g) := by
  have ha := elementary_map eH.toMonoidHom eH.injective hA
  have hconj : IsConjugateTo (A.map eH.toMonoidHom) transpositionGroup := by
    rcases hmodel with ⟨e, he⟩ | ⟨e, he⟩
    · apply natural_codim_one_conjugate_transposition _ ha
      rw [← fixedCodim_map_equivariant ρ (naturalRepresentation (Fin 8))
        eH.toMonoidHom e he]
      exact hc
    · apply core_codim_one_conjugate_transposition _ ha
      rw [← fixedCodim_map_equivariant ρ (coreRepresentation (Fin 8))
        eH.toMonoidHom e he]
      exact hc
  have hr : rank A = 1 := by
    rw [← rank_map_injective eH.toMonoidHom eH.injective A,
      hconj.rank_eq, transpositionGroup_eq]
    exact rank_disjointTranspositions 1
  obtain ⟨g, hg⟩ := exists_conjugate_marking eH A transpositionGroup hconj
  exact ⟨hr, g, hg, naturalOrCover_conjugate ρ eH hmodel g⟩
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels
