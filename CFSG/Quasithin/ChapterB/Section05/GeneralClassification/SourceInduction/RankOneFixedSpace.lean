module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.RankOneComparison
public import Theory.Representation.BinarySylowFixedSpace
public import Theory.Representation.BinaryPermutation.CubicFixedSpace.Five
public import Theory.Representation.SpecialLinearNatural.CubicFixedSpace

/-!
# Cubic fixers through rank-one B.5 moved sections

Odd Sylow-coset averaging lifts a Sylow-fixed vector through a trivial
quotient. A cubic actor also lifts through a central kernel in characteristic
two. Applying these facts to the literal B.5 moved section gives a cubic
fixer for the alternating-five, natural SL₃, and repeated SL₃ rows, without
requiring either extension to split. Only the natural SL₂ row remains.

The original residual-normalizer action in 14.7.67 is the consumer: its point
stabilizer is a two-group, which excludes each cubic-fixer row.
Source: Aschbacher–Smith B.5.1 and 14.7.67(4), printed pp.99–103 and1070.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.BinarySylowFixedSpace
namespace CFSG.Quasithin.ChapterB.SourceInduction.RankOneFixedSpace
open QuasisimpleSource
universe u v w z
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {L : Subgroup D}

def CubicFixed (σ : Representation (ZMod 2) D V) : Prop :=
  ∀ S : Sylow 2 D, ∃ d : D, d ∉ S ∧ d ^ 3 = 1 ∧
    ∀ v ∈ fixedSpace σ (S : Subgroup D), σ d v = v

private theorem transport {A : Type w} [Group A]
    {M : Type z} [AddCommGroup M] [Module (ZMod 2) M]
    {σ : Representation (ZMod 2) A M} (e : ActionEquiv ρ σ)
    (h : ∀ T : Sylow 2 A, ∃ d : A, d ∉ T ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace σ (T : Subgroup A), σ d v = v) : CubicFixed ρ := by
  intro S
  exact sylow_fixedSpace_enlargement_equivariant ρ σ (S : Subgroup D)
    e.groupEquiv e.linearEquiv e.intertwines (h (S.mapSurjective e.groupEquiv.surjective))

private theorem section_lift (s : MovedSection ρ L)
    (h : CubicFixed (s.action.comp L.subtype)) : CubicFixed (ρ.comp L.subtype) := by
  let U : Subrepresentation (ρ.comp L.subtype) :=
    ⟨s.space.toSubmodule, fun g _ hv => s.space.apply_mem_toSubmodule g hv⟩
  intro S
  apply sylow_fixedSpace_enlargement_of_central_section
    (ρ.comp L.subtype) (s.action.comp L.subtype) U s.central.toSubmodule.mkQ
    (fun _ _ => rfl) ?_ ?_ S (h S)
  · intro g u hu
    have hm := (Submodule.Quotient.mk_eq_zero _).mp hu
    rw [s.central_eq] at hm
    exact hm g
  · intro g v
    change ρ g v - v ∈ s.space.toSubmodule
    rw [s.space_eq]
    exact Submodule.subset_span ⟨g, g.property, v, Submodule.mem_top, rfl⟩

private theorem space_lift (s : MovedSection ρ L)
    (h : CubicFixed (s.space.toRepresentation.comp L.subtype)) :
    CubicFixed (ρ.comp L.subtype) := by
  let U : Subrepresentation (ρ.comp L.subtype) :=
    ⟨s.space.toSubmodule, fun g _ hv => s.space.apply_mem_toSubmodule g hv⟩
  let i : U.toRepresentation.IntertwiningMap (ρ.comp L.subtype) :=
    { toLinearMap := U.toSubmodule.subtype
      isIntertwining' _ := by ext; rfl }
  intro S
  obtain ⟨d, hd, h3, hf⟩ := h S
  refine ⟨d, hd, h3, fixes_of_trivial_quotient (ρ.comp L.subtype)
    U.toRepresentation i Subtype.val_injective ?_ S hf⟩
  intro g v
  refine ⟨⟨_, ?_⟩, rfl⟩
  change ρ g v - v ∈ s.space.toSubmodule
  rw [s.space_eq]
  exact Submodule.subset_span ⟨g, g.property, v, Submodule.mem_top, rfl⟩

/-- All rank-one B.5 rows except the natural SL₂ row fix every Sylow-fixed
vector through the literal moved section, even when its extensions do not split. -/
theorem linearTwo_or_cubic {s : MovedSection ρ L}
    (h : ComponentReduction.PreliminaryActions.RankOneActionCase ρ L s) :
    (∃ F : BinaryField, Nonempty (ActionEquiv (s.action.comp L.subtype)
      (linearNatural F 2))) ∨ CubicFixed (ρ.comp L.subtype) := by
  cases h with
  | irreducible hi hf hir cases he =>
    cases cases with
    | linearTwo F hg e ho hq => exact Or.inl ⟨F, ⟨e⟩⟩
    | linearThree F ho hg e hq =>
      apply Or.inr
      apply section_lift s
      apply transport e
      intro T
      exact sylow_fixedSpace_enlargement_of_cubic _ _ SL3BinaryCubic.klein_two
        _ SL3BinaryCubic.cycle_pow SL3BinaryCubic.cycle_ne_one
        SL3BinaryCubic.cycle_fixes_natural T
    | symmetricFive e ho hq =>
      apply Or.inr
      apply section_lift s
      let a : ActionEquiv (s.action.comp L.subtype) (alternatingNatural 5) := {
        groupEquiv := e.subgroupEquiv
        linearEquiv := e.action.linearEquiv
        intertwines := by
          intro g v
          have hh := e.action.intertwines (⟨g, e.contained g.property⟩ : _) v
          rw [e.compatible] at hh
          exact hh }
      apply transport a
      intro T
      exact sylow_fixedSpace_enlargement_of_cubic _ _
        BinaryPermutation.CubicFixedSpace.Five.klein_isPGroup _
        BinaryPermutation.CubicFixedSpace.Five.cycle_pow
        BinaryPermutation.CubicFixedSpace.Five.cycle_ne_one
        BinaryPermutation.CubicFixedSpace.Five.cycle_fixes_natural T
  | doubleThree F ho ht e hoff hq =>
    apply Or.inr
    apply space_lift s
    apply transport e
    intro T
    apply sylow_fixedSpace_enlargement_of_cubic _ _ SL3BinaryCubic.klein_two
      _ SL3BinaryCubic.cycle_pow SL3BinaryCubic.cycle_ne_one _ T
    intro v hv
    funext i
    exact SL3BinaryCubic.cycle_fixes_natural (v i) (fun a => congrFun (hv a) i)

end CFSG.Quasithin.ChapterB.SourceInduction.RankOneFixedSpace
