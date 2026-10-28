module

public import Theory.Representation.BinaryPermutation.SevenPoint
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.StrictCentralizer

/-!
# The faithful-module inputs and their original source consumer

The seven-point transvection-center construction and elementary-actor argument
prove both universal inputs for arbitrary faithful binary modules, including
reducible modules. Transport preserves the supplied permutation marking.

For the literal source submodule W and quotient Ũ_H/W, the component marking
and supplement supply faithfulness. The rank-one displacement bound then gives
transvections on both sections, so recognition constructs both natural
embeddings. The critical-line displacement estimate supplies the strict
centralizer and gives the actual terminal contradiction of 13.8.24.

The final source assembly still has to prove rank one and nontrivial action
on W through the two partition branches, and the preceding geometric estimate.
No natural-module or arbitrary-module recognition callback remains here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, 13.8.23–24,
printed pp.958–959/PDF pp.975–976 (1 March 2004 manuscript).
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
open PairsBranch.ModuleSelection

universe u

/-- No arbitrary faithful binary module between A₇ and S₇ has a strong offender. -/
theorem sevenPointNoStrongInput : SevenPointNoStrongInput.{u} := by
  intro J hJ F _ _ _ σ hf
  exact BinaryPermutation.SevenPoint.no_strong J hJ σ hf

/-- Transvection centers recognize the natural submodule with the same marking. -/
theorem sevenPointRecognitionInput : SevenPointRecognitionInput.{u} := by
  intro J hJ F _ _ _ σ hf a ha ha2 hc
  exact BinaryPermutation.SevenPoint.exists_core_embedding J hJ σ hf a ha ha2 hc

variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- A faithful section with a nontrivial elementary actor of fixed codimension
one contains the natural module for its original seven-point action. -/
theorem natural_of_fixedCodim_one
    (ρ : Representation (ZMod 2) H E) (hf : Function.Injective ρ)
    (φ : H →* Equiv.Perm (Fin 7)) (hφ : Function.Injective φ)
    (K : Subgroup H) (hK : K.map φ = alternatingGroup (Fin 7))
    (A : Subgroup H) (hA : IsElementaryTwo A) (hc : fixedCodim ρ A = 1) :
    HasNaturalSubmodule ρ φ := by
  obtain ⟨a, ha, hne⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  let : IsElementaryAbelian 2 A := hA.2
  apply recognition_of_permutation_input ρ φ hφ K hK sevenPointRecognitionInput hf a hne
    (elemPow_eq_one_of_isElementaryAbelian a ha)
  have hle := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr ha))
  have hdimA := fixedCodim_add_finrank ρ A
  have hdima := fixedCodim_add_finrank ρ (zpowers a)
  have hp := fixedCodim_pos_of_faithful ρ hf (by simpa using hne : zpowers a ≠ ⊥)
  omega

open TransvectionRecognition.Component.ModelExtension CriticalGeometry PairsBranch

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ J C : Subgroup G}

/-- Apply the proved arbitrary-module inputs to both literal source sections.
The permutation action is constructed from the original component quotient. -/
theorem source_sections_no_strong
    (hJ : J ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hCJ : C ≤ J) (hC : (C.subgroupOf J).IsCComponent)
    (hCn : (C.subgroupOf J).Normal) (hCT : C ⊔ (T : Subgroup G) = J)
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7))
    [IsElementaryAbelian 2 (Source.UH J V₃)]
    [(V₁.subgroupOf (Source.UH J V₃)).Normal]
    (ρ : Representation (ZMod 2) (Source.Hstar J) (Additive (Source.Utilde J V₃ V₁)))
    (W : Subrepresentation ρ)
    (hCW : ∃ k ∈ Source.starImage J C, ∃ w : W.toSubmodule,
      W.toRepresentation k w ≠ w)
    (hCQ : ∃ k ∈ Source.starImage J C,
      ∃ q : Additive (Source.Utilde J V₃ V₁) ⧸ W.toSubmodule,
        W.quotientRepresentation k q ≠ q) :
    ¬ IsStrongFFModule W.toRepresentation ∧ ¬ IsStrongFFModule W.quotientRepresentation := by
  obtain ⟨φ, hi, hm, _⟩ := LocalGeometry.source_action_exists J C (T : Subgroup G)
    hCJ (le_sup_right.trans hJ.1.2) hC hCn T.isPGroup' hCT e
  have hmono := (source_structure hJ hCJ hC hCn hCT e).2.2
  exact ⟨noStrong_of_permutation_input W.toRepresentation φ hi (Source.starImage J C) hm
      sevenPointNoStrongInput (faithful_of_nontrivial_on_monolith _ _ hmono hCW),
    noStrong_of_permutation_input W.quotientRepresentation φ hi (Source.starImage J C) hm
      sevenPointNoStrongInput (faithful_of_nontrivial_on_monolith _ _ hmono hCQ)⟩

/-- The original rank-one terminal contradiction, with both natural embeddings
constructed rather than supplied. The remaining displacement premise is the
preceding geometric assertion [C̃_H,Vγ] ≤ Ã₁. -/
theorem source_no_rank_one_configuration_of_displacement
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hJ : J ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hCJ : C ≤ J) (hC : (C.subgroupOf J).IsCComponent)
    (hCn : (C.subgroupOf J).Normal) (hCT : C ⊔ (T : Subgroup G) = J)
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7))
    [IsElementaryAbelian 2 (Source.UH J V₃)]
    [(V₁.subgroupOf (Source.UH J V₃)).Normal]
    (ρ : Representation (ZMod 2) (Source.Hstar J) (Additive (Source.Utilde J V₃ V₁)))
    (W : Subrepresentation ρ) (c : CriticalPair L (T : Subgroup G) J V)
    (hCW : ∃ k ∈ Source.starImage J C, ∃ w : W.toSubmodule,
      W.toRepresentation k w ≠ w)
    (hCQ : ∃ k ∈ Source.starImage J C,
      ∃ q : Additive (Source.Utilde J V₃ V₁) ⧸ W.toSubmodule,
        W.quotientRepresentation k q ≠ q)
    (hA : IsElementaryTwo (Source.starImage J (c.Ugamma V₃)))
    (hrank : rank (Source.starImage J (c.Ugamma V₃)) = 1)
    (hbound : fixedCodim ρ (Source.starImage J (c.Ugamma V₃)) ≤
      2 * rank (Source.starImage J (c.Ugamma V₃)))
    (hVrank : 1 < rank (Source.starImage J c.Vgamma))
    (hdisp : ∀ b ∈ Source.starImage J c.Vgamma,
      ∀ v ∈ fixedSpace ρ (Source.starImage J (c.Ugamma V₃)),
        ρ b v - v ∈ sourceImage J V₃ V₁ (c.Aone V₁)) : False := by
  obtain ⟨φ, hi, hm, _⟩ := LocalGeometry.source_action_exists J C (T : Subgroup G)
    hCJ (le_sup_right.trans hJ.1.2) hC hCn T.isPGroup' hCT e
  obtain ⟨hfW, hfQ, hcW, hcQ, _, _⟩ := source_rank_one_sections hJ hCJ hC hCn hCT e
    ρ W (Source.starImage J (c.Ugamma V₃)) hCW hCQ hA.1 hrank hbound
  exact source_no_rank_one_configuration d hJ hCJ hC hCn hCT e ρ W c hCW hCQ hA.1
    hrank hbound hVrank hdisp φ hi hA.2
    (natural_of_fixedCodim_one W.toRepresentation hfW φ hi (Source.starImage J C) hm _ hA hcW)
    (natural_of_fixedCodim_one W.quotientRepresentation hfQ φ hi
      (Source.starImage J C) hm _ hA hcQ)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
