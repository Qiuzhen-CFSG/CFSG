module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
public import Theory.Representation.SixLetterTransvections

/-!
# Transvections select the symmetric six-letter extension

A nontrivial binary transvection has square one and one-dimensional
displacement. The intrinsic A₆ obstruction therefore rules out A₆ for
any faithful actor containing such an element. Applied to the checked
normalizer theorem for the natural A₆ module, this selects S₆ and retains
the same actor identification and module coordinates.

These are conditional extension deductions. Constructing the natural
component section and extending it to the entire source module, including
the augmentation case, remain obligations of the 13.8.5 assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.5,
printed p.947, using 13.7.6(3) and I.1.6(1).
-/

public section

open Subgroup Representation

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component

variable {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]

/-- Faithfulness makes a nontrivial binary transvection an involution in the actor. -/
theorem transvection_square {ρ : Representation (ZMod 2) A E} {t : A}
    (hρ : Function.Injective ρ) (ht : IsTransvection ρ t) : t ^ 2 = 1 := by
  obtain ⟨f, v, _, _, hfv, he⟩ := ht
  apply hρ
  ext w
  simp only [pow_two, map_one, Module.End.one_apply]
  simp [he, hfv, add_assoc, ZModModule.add_self]

/-- The actual displacement image of a nontrivial binary transvection has dimension one. -/
theorem transvection_displacement_rank {ρ : Representation (ZMod 2) A E} {t : A}
    (ht : IsTransvection ρ t) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) = 1 := by
  obtain ⟨f, v, hf, hv, _, he⟩ := ht
  have hfv : ∃ w, f w ≠ 0 := by
    by_contra! h
    apply hf
    ext w
    exact h w
  obtain ⟨w, hw⟩ := hfv
  have hw1 : f w = 1 := by
    have hbin : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    exact (hbin (f w)).resolve_left hw
  have hr : LinearMap.range (ρ t - LinearMap.id) = Submodule.span (ZMod 2) {v} := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      change ρ t x - x ∈ Submodule.span (ZMod 2) {v}
      rw [he, add_sub_cancel_left]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))
    · apply Submodule.span_le.mpr
      rintro x rfl
      exact ⟨w, by simp [he, hw1]⟩
  rw [hr, finrank_span_singleton hv]

/-- The presence of a transvection excludes an actual A₆ acting-group identification. -/
theorem not_alternatingSix {ρ : Representation (ZMod 2) A E}
    [Module.Finite (ZMod 2) E] (hρ : Function.Injective ρ)
    {t : A} (ht : IsTransvection ρ t) : ¬ Nonempty (A ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨e⟩
  have ht' : IsTransvection (ρ.comp e.symm.toMonoidHom) (e t) := by
    obtain ⟨f, v, hf, hv, hfv, hact⟩ := ht
    refine ⟨f, v, hf, hv, hfv, ?_⟩
    intro w
    change ρ (e.symm (e t)) w = _
    rw [e.symm_apply_apply]
    exact hact w
  have he := Representation.SixLetterTransvections.alternating_eq_one_of_displacement_le_one
    (ρ.comp e.symm.toMonoidHom) (hρ.comp e.symm.injective) (e t)
    (transvection_displacement_rank ht').le
  exact ht.ne_one (e.injective (by simpa using he))

/-- A faithful normal extension of the specified natural A₆ action containing a transvection is S₆. Both its restriction and its full module action retain the original coordinates. -/
theorem symmetricSix_of_natural_extension
    {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    [Module.Finite (ZMod 2) E]
    (K : Subgroup A) [K.Normal]
    (ρ : Representation (ZMod 2) A E) (hρ : Function.Injective ρ)
    (eK : K ≃* alternatingGroup (Fin 6))
    (eV : E ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (he : ∀ k : K, ∀ v, eV (ρ k v) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 6) (eK k) (eV v))
    (t : A) (ht : IsTransvection ρ t) :
    ∃ e : A ≃* Equiv.Perm (Fin 6),
      (∀ k : K, e k = (eK k).val) ∧
      ∀ a v, eV (ρ a v) = BinaryPermutation.naturalRepresentation (Fin 6) (e a) (eV v) := by
  obtain ⟨f, _, hfK, hfV, hAlt | hSym⟩ :=
    ComponentSieve.SixAndG2.NaturalSix.faithful_extension K ρ hρ eK eV he
  · exact (not_alternatingSix hρ ht ⟨hAlt.choose⟩).elim
  · obtain ⟨e, he⟩ := hSym
    exact ⟨e, fun k => (he k).trans (hfK k), fun a v => by rw [he]; exact hfV a v⟩

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component
