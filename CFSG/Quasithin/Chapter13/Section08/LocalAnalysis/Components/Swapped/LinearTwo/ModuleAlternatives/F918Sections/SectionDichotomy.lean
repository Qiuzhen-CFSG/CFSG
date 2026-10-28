module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FactorSpaces
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FaithfulSections
public import Theory.Representation.BinaryOffender.IrreducibleExistence

/-!
# Maximal sections for the exchanged component orbit

In a commutator-generated module, a maximal proper ambient submodule W
either has nontrivial component-orbit action or is centralized by that orbit.
In the first case the F.9.18 fixed-codimension argument applies directly to
W and its literal quotient: the common elementary actor stays faithful on
both, by the component-kernel dichotomy. Excluding strong offenders gives
the two FF sections. In the second case every Irr⁺ section generates the
whole module under the ambient group. Neither argument asserts irreducibility
under the component orbit from ambient maximality.

The bounded actor and the two strong-offender exclusions are explicit
intermediate hypotheses. This module does not prove their B.4.2/F.9.18
source assembly or the homogeneous refinement Irr⁺(K₀,V,T).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.16(1), printed p.952, and the proof of F.9.18(6), pp.325–326.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections

open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

/-- An ambient subrepresentation is invariant under every subgroup. -/
theorem subrepresentation_stable (W : Subrepresentation ρ) (L : Subgroup D) :
    L ≤ subspaceStabilizer ρ W.toSubmodule :=
  le_subspaceStabilizer ρ _ (fun g _ _ hv => W.apply_mem_toSubmodule g hv)

/-- The seed belongs to its actual ambient orbit span. -/
theorem le_seedSpan (I : Submodule (ZMod 2) V) : I ≤ (seedSpan ρ I).toSubmodule := by
  intro v hv
  exact Submodule.subset_span ⟨1, v, hv, by simp⟩

/-- Centrality of the maximal submodule replaces the unsupported assertion
that its quotient is irreducible under the smaller component orbit. -/
theorem orbitSpan_eq_top_of_central_maximal (L : Subgroup D)
    (hfull : subspaceCommutator ρ ⊤ L = ⊤)
    (W : Subrepresentation ρ) (_hW : W ≠ ⊤)
    (hmax : ∀ Y : Subrepresentation ρ, W ≤ Y → Y ≠ ⊤ → Y = W)
    (hcentral : W.toSubmodule ≤ fixedSpace ρ L)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ L I) : seedSpan ρ I = ⊤ := by
  have hIW : ¬ I ≤ W.toSubmodule := fun h => hI.not_le_fixedSpace ρ (h.trans hcentral)
  have hsum : W ⊔ seedSpan ρ I = ⊤ := by
    by_contra hn
    have he := hmax _ le_sup_left hn
    exact hIW ((le_seedSpan ρ I).trans (he ▸ (show seedSpan ρ I ≤ W ⊔ seedSpan ρ I
      from le_sup_right)))
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  rw [← hfull]
  apply subspaceCommutator_le_of_le_sup_fixedSpace ρ (subrepresentation_stable ρ _ L)
  have he : W.toSubmodule ⊔ (seedSpan ρ I).toSubmodule = ⊤ := by
    rw [← Subrepresentation.toSubmodule_sup, hsum]
    rfl
  rw [← he, sup_comm]
  exact sup_le_sup_left hcentral _

/-- Noncentrality of W is precisely nontriviality of its restricted action. -/
theorem subrepresentation_nontrivial_of_not_central (L : Subgroup D)
    (W : Subrepresentation ρ) (hW : ¬ W.toSubmodule ≤ fixedSpace ρ L) :
    ¬ ∀ l ∈ L, ∀ w, W.toRepresentation l w = w := by
  intro ht
  apply hW
  intro v hv l
  exact congrArg (fun w : W => (w : V)) (ht l l.property ⟨v, hv⟩)

/-- A proper quotient of a commutator-generated module is noncentral. -/
theorem quotient_nontrivial_of_moved_eq_top (L : Subgroup D)
    (hfull : subspaceCommutator ρ ⊤ L = ⊤)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤) :
    ¬ ∀ l ∈ L, ∀ w, W.quotientRepresentation l w = w := by
  intro ht
  apply hW
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  rw [← hfull]
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, v, _, rfl⟩
  exact (Submodule.Quotient.eq W.toSubmodule).mp (ht l hl (W.toSubmodule.mkQ v))

/-- The actor from F.9.18(2) is faithful on each of the two sections whenever
both have nontrivial orbit action. No irreducibility of either is needed. -/
theorem actor_faithful_on_sections (K T A : Subgroup D)
    (hK : Theory.GroupTheory.IsComponent D K)
    (hfaith : A ⊓ centralizer (conjugateSpanBy K T : Set D) = ⊥)
    (hfull : subspaceCommutator ρ ⊤ (conjugateSpanBy K T) = ⊤)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (hcentral : ¬ W.toSubmodule ≤ fixedSpace ρ (conjugateSpanBy K T)) :
    (∀ a ∈ A, (∀ w, W.toRepresentation a w = w) → a = 1) ∧
      (∀ a ∈ A, (∀ w, W.quotientRepresentation a w = w) → a = 1) := by
  have hwker := action_kernel_le_centralizer_of_component_orbit
    W.toRepresentation K T hK (subrepresentation_nontrivial_of_not_central ρ _ W hcentral)
  have hqker := action_kernel_le_centralizer_of_component_orbit
    W.quotientRepresentation K T hK (quotient_nontrivial_of_moved_eq_top ρ _ hfull W hW)
  constructor
  · intro a ha hv
    exact mem_bot.mp (hfaith ▸ (show a ∈ A ⊓ centralizer (conjugateSpanBy K T : Set D) from
      ⟨ha, hwker ((actionHom_eq_one_iff W.toRepresentation a).mpr hv)⟩))
  · intro a ha hv
    exact mem_bot.mp (hfaith ▸ (show a ∈ A ⊓ centralizer (conjugateSpanBy K T : Set D) from
      ⟨ha, hqker ((actionHom_eq_one_iff W.quotientRepresentation a).mpr hv)⟩))

/-- The precise FF output on the two faithful action images, obtained from
the common actor bound. W need not equal [W,K₀]. -/
theorem two_ff_sections_of_noncentral [FiniteDimensional (ZMod 2) V]
    (K T A : Subgroup D) (hK : Theory.GroupTheory.IsComponent D K)
    (hA : IsElementaryTwo A) (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hfaith : A ⊓ centralizer (conjugateSpanBy K T : Set D) = ⊥)
    (hfull : subspaceCommutator ρ ⊤ (conjugateSpanBy K T) = ⊤)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (hcentral : ¬ W.toSubmodule ≤ fixedSpace ρ (conjugateSpanBy K T))
    (hnW : ¬ IsStrongFFModule (imageRepresentation W.toRepresentation))
    (hnQ : ¬ IsStrongFFModule (imageRepresentation W.quotientRepresentation)) :
    IsFFModule (imageRepresentation W.toRepresentation) ∧
      IsFFModule (imageRepresentation W.quotientRepresentation) := by
  obtain ⟨hw, hq⟩ := actor_faithful_on_sections ρ K T A hK hfaith hfull W hW hcentral
  rcases faithful_image_ff_alternative ρ W hA hbound hw hq with h | h | h
  · exact h
  · exact (hnW h).elim
  · exact (hnQ h).elim

/-- The valid maximal-section dichotomy, with the classification-dependent
no-strong conditions exposed. In the central case every actual Irr⁺ member
has full ambient orbit span, a useful stronger generation conclusion. -/
theorem maximal_section_dichotomy [FiniteDimensional (ZMod 2) V]
    (K T A : Subgroup D) (hK : Theory.GroupTheory.IsComponent D K)
    (hA : IsElementaryTwo A) (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hfaith : A ⊓ centralizer (conjugateSpanBy K T : Set D) = ⊥)
    (hfull : subspaceCommutator ρ ⊤ (conjugateSpanBy K T) = ⊤)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (hmax : ∀ Y : Subrepresentation ρ, W ≤ Y → Y ≠ ⊤ → Y = W)
    (hnW : ¬ W.toSubmodule ≤ fixedSpace ρ (conjugateSpanBy K T) →
      ¬ IsStrongFFModule (imageRepresentation W.toRepresentation))
    (hnQ : ¬ IsStrongFFModule (imageRepresentation W.quotientRepresentation)) :
    (IsFFModule (imageRepresentation W.toRepresentation) ∧
      IsFFModule (imageRepresentation W.quotientRepresentation)) ∨
    (subspaceCommutator ρ W.toSubmodule (conjugateSpanBy K T) = ⊥ ∧
      ∀ I, IsIrrPlus ρ (conjugateSpanBy K T) I → seedSpan ρ I = ⊤) := by
  by_cases hc : W.toSubmodule ≤ fixedSpace ρ (conjugateSpanBy K T)
  · exact Or.inr ⟨(subspaceCommutator_eq_bot_iff ρ _ _).mpr hc,
      fun I hI => orbitSpan_eq_top_of_central_maximal ρ _ hfull W hW hmax hc I hI⟩
  · exact Or.inl (two_ff_sections_of_noncentral ρ K T A hK hA hbound hfaith hfull
      W hW hc (hnW hc) hnQ)

/-- In the central case the Irr⁺ witness is constructed by the perfect-actor
existence theorem, not supplied as part of the desired dichotomy. Homogeneity
relative to T is a separate refinement. -/
theorem exists_generating_irrPlus_of_central_maximal [FiniteDimensional (ZMod 2) V]
    [Nontrivial V] (L : Subgroup D) [Group.IsPerfect L]
    (hfull : subspaceCommutator ρ ⊤ L = ⊤)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (hmax : ∀ Y : Subrepresentation ρ, W ≤ Y → Y ≠ ⊤ → Y = W)
    (hc : W.toSubmodule ≤ fixedSpace ρ L) :
    ∃ I, IsIrrPlus ρ L I ∧ seedSpan ρ I = ⊤ := by
  have hn : ¬ (⊤ : Submodule (ZMod 2) V) ≤ fixedSpace ρ L := by
    intro hf
    have hb := (subspaceCommutator_eq_bot_iff ρ _ _).mpr hf
    rw [hfull] at hb
    exact top_ne_bot hb
  obtain ⟨I, hI⟩ := exists_isIrrPlus_of_not_fixed ρ L hn
  exact ⟨I, hI, orbitSpan_eq_top_of_central_maximal ρ L hfull W hW hmax hc I hI⟩

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections
