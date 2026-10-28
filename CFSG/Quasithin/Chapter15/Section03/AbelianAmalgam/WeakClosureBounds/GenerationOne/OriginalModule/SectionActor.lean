module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FaithfulSections
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.QuadraticImageBound
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.QuadraticFourGroup.Basic

/-!
# The common actor on actual component-orbit sections

A representation kernel on a noncentral orbit of components centralizes
that orbit. Thus the original quadratic actor remains faithful on every
noncentral whole-group section. Its rank and quadratic codimension bound
survive passage to the faithful image. The final theorem applies this to
literal irreducible subquotients, without restricting to only one factor.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
F.9.18(3), printed p.325, and 15.3.65, printed p.1152.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule
open RepresentationReduction.SourceRestrictions Representation.QuadraticFourGroup
variable {D V W : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

omit [Finite D] in
/-- The common actor retains its rank on every noncentral representation
of the whole component orbit. The individual component need not be normal. -/
theorem component_orbit_actor_faithful
    (σ : Representation (ZMod 2) D W) (K T A : Subgroup D)
    (hK : IsComponent D K)
    (hn : ¬ ∀ k ∈ conjugateSpanBy K T, ∀ w, σ k w = w)
    (hAC : A ⊓ centralizer (conjugateSpanBy K T : Set D) = ⊥) :
    ∀ a ∈ A, (∀ w, σ a w = w) → a = 1 := by
  have hk := action_kernel_le_centralizer_of_component_orbit σ K T hK hn
  intro a ha hw
  exact mem_bot.mp (hAC ▸ (show a ∈ A ⊓ centralizer (conjugateSpanBy K T : Set D) from
    ⟨ha,hk ((actionHom_eq_one_iff σ a).mpr hw)⟩))

/-- The original quadratic actor, with unchanged rank, witnesses the ratio
bound in this representation's actual faithful image. -/
theorem component_orbit_image_quadratic_bound
    (σ : Representation (ZMod 2) D W) (K T A : Subgroup D)
    (hK : IsComponent D K)
    (hn : ¬ ∀ k ∈ conjugateSpanBy K T, ∀ w, σ k w = w)
    (hAC : A ⊓ centralizer (conjugateSpanBy K T : Set D) = ⊥)
    (hA : IsElementaryTwo A) (hq : IsQuadratic σ A)
    (hc : fixedCodim σ A ≤ 2 * rank A) :
    (∀ a ∈ A, (∀ w, σ a w = w) → a = 1) ∧
      quadraticRatio (imageRepresentation σ) ≤ 2 := by
  have hf := component_orbit_actor_faithful σ K T A hK hn hAC
  refine ⟨hf,(quadraticRatio_le_two_iff _).mpr ?_⟩
  refine ⟨actionSubgroup σ A,hA.actionSubgroup σ hf,quadratic_actionSubgroup σ hq,?_⟩
  rwa [fixedCodim_actionSubgroup,actionSubgroup_rank σ A hf]

omit [Finite D] in
/-- Actual invariant subquotients inherit quadraticity and the original
fixed-codimension bound, before any actor is replaced by its image. -/
theorem irreducible_section_quadratic_bound
    [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D V) (σ : Representation (ZMod 2) D W)
    (hs : IsIrreducibleSection ρ σ) {A : Subgroup D}
    (hq : IsQuadratic ρ A) (hc : fixedCodim ρ A ≤ 2 * rank A) :
    IsQuadratic σ A ∧ fixedCodim σ A ≤ 2 * rank A := by
  obtain ⟨_,S,N,⟨e⟩⟩ := hs
  have hS := quadratic_subrepresentation ρ S hq
  have hN := quadratic_of_equivariant_surjection S.toRepresentation N.quotientRepresentation
    N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective (fun _ _ => rfl) A hS
  have hcod : fixedCodim N.quotientRepresentation A ≤ fixedCodim ρ A :=
    (fixedCodim_le_of_equivariant_surjection S.toRepresentation N.quotientRepresentation
      N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective (fun _ _ => rfl) A).trans
        (fixedCodim_subrepresentation_le ρ S A)
  constructor
  · exact quadratic_of_equivariant_surjection N.quotientRepresentation σ e.toLinearEquiv.toLinearMap
      e.toLinearEquiv.surjective (fun g v => DFunLike.congr_fun (e.toIntertwiningMap.isIntertwining' g) v) A hN
  · have he := fixedCodim_map_equivariant N.quotientRepresentation σ (MonoidHom.id D)
      e.toLinearEquiv (fun g v => DFunLike.congr_fun (e.toIntertwiningMap.isIntertwining' g) v) A
    simp only [Subgroup.map_id] at he
    exact he ▸ hcod.trans hc

/-- The F.9.18 common actor remains faithful and has ratio at most two
on every actual irreducible section where the residual component orbit acts. -/
theorem irreducible_section_component_orbit_bound
    [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D V) (σ : Representation (ZMod 2) D W)
    (hs : IsIrreducibleSection ρ σ) (K T A : Subgroup D)
    (hK : IsComponent D K)
    (hn : ¬ ∀ k ∈ conjugateSpanBy K T, ∀ w, σ k w = w)
    (hAC : A ⊓ centralizer (conjugateSpanBy K T : Set D) = ⊥)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A) :
    IsQuadratic σ A ∧ fixedCodim σ A ≤ 2 * rank A ∧
      (∀ a ∈ A, (∀ w, σ a w = w) → a = 1) ∧
        quadraticRatio (imageRepresentation σ) ≤ 2 := by
  obtain ⟨hqs,hcs⟩ := irreducible_section_quadratic_bound ρ σ hs hq hc
  exact ⟨hqs,hcs,component_orbit_image_quadratic_bound σ K T A hK hn hAC hA hqs hcs⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule
