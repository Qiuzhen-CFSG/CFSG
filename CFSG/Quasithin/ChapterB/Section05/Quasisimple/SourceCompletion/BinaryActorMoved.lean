module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.BinaryActorCases
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedCover
public import Theory.Representation.FirstCohomologyDuality.OneDimensionalCover
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.CohomologyReduction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.Alternating
/-!
# The actual moved module for binary degree-four/five components

The natural and exterior rows have no central attachment, by the proved
cohomology calculations. The orthogonal row has central kernel of dimension
at most one, so the original moved space has dimension six or seven. This
passes from the B.5.1 central quotient to the actual moved module without
assuming a direct splitting with its fixed part.

Source: Aschbacher--Smith 15.1.27 and I.1.6, pp.1102--1103,408.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion.BinaryActor
open ExtensionConsequences
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) D V} {L : Subgroup D}

private noncomputable def splitEquiv (s : MovedSection ρ L)
    (hc : IsCompl s.space.toSubmodule (fixedSpace ρ L)) :
    ActionEquiv (s.action.comp L.subtype) (s.space.toRepresentation.comp L.subtype) := by
  have hz : s.central.toSubmodule = ⊥ := by
    rw [s.central_eq]
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact (disjoint_iff.mp hc.disjoint).le ⟨v.property,fun g => congrArg Subtype.val (hv g)⟩
  exact ⟨MulEquiv.refl _,s.central.toSubmodule.quotEquivOfEqBot hz, fun g v => by
    induction v using Submodule.Quotient.induction_on with | _ v => rfl⟩

private theorem orthogonal_dimension (s : MovedSection ρ L)
    (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (e : ActionEquiv (s.action.comp L.subtype) (alternatingNatural 8)) :
    Module.finrank (ZMod 2) s.space.toSubmodule = 6 ∨
      Module.finrank (ZMod 2) s.space.toSubmodule = 7 := by
  have hc := SourceB513.alternating_moved_central_finrank_le_one (Or.inr rfl) s hi ⟨e⟩
  have hq : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 6 := by
    rw [e.linearEquiv.finrank_eq,BinaryPermutation.finrank_natural_even (Fin 8) (by decide)]
    rfl
  have hd := s.central.toSubmodule.finrank_quotient_add_finrank
  omega

omit [Finite D] in
/-- The original moved orthogonal module is the natural six-space or the
actual seven-dimensional augmentation cover, with the same component marking. -/
theorem orthogonal_moved_model (s : MovedSection ρ L)
    (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (e : ActionEquiv (s.action.comp L.subtype) (alternatingNatural 8)) :
    IsAlternatingNatural (s.space.toRepresentation.comp L.subtype) 8 ∨
      Nonempty (ActionEquiv (s.space.toRepresentation.comp L.subtype)
        (BinaryPermutation.alternatingCoreRepresentation (Fin 8))) := by
  let p := s.coverProjection e
  have hp := s.coverProjection_isCover hi e
  by_cases hk : p.toLinearMap.ker = ⊥
  · let f := LinearEquiv.ofBijective p.toLinearMap ⟨LinearMap.ker_eq_bot.mp hk,hp.1⟩
    refine Or.inl ⟨⟨e.groupEquiv,f,?_⟩⟩
    intro g v
    have hh := LinearMap.congr_fun (p.isIntertwining' (e.groupEquiv g)) v
    change p (s.space.toRepresentation (e.groupEquiv.symm (e.groupEquiv g)) v) =
      alternatingNatural 8 (e.groupEquiv g) (p v) at hh
    rw [e.groupEquiv.symm_apply_apply] at hh
    exact hh
  · obtain ⟨f,hf⟩ := Representation.OneCohomology.equiv_of_cover_of_finrank_dual_H1_eq_one
      p hp (BinaryPermutation.alternatingCoreProjection (Fin 8))
      BinaryPermutation.alternatingEight_coreProjection_isCover
      BinaryPermutation.alternatingEight_natural_dual_finrank_H1 hk (by
        rw [BinaryPermutation.finrank_core,
          BinaryPermutation.finrank_natural_even (Fin 8) (by decide)]
        rfl)
    refine Or.inr ⟨⟨e.groupEquiv,f,?_⟩⟩
    intro g v
    have hh := hf (e.groupEquiv g) v
    change f (s.space.toRepresentation (e.groupEquiv.symm (e.groupEquiv g)) v) = _ at hh
    rw [e.groupEquiv.symm_apply_apply] at hh
    exact hh

/-- Alternatives on the actual moved space. The orthogonal central quotient
retains its coordinates; its original cover has dimension six or seven. -/
inductive MovedCase (s : MovedSection ρ L) (n : ℕ) : Prop
  | natural (action : ActionEquiv (s.space.toRepresentation.comp L.subtype)
      (linearNatural BinaryField.two n))
  | orthogonal (degree : n = 4)
      (action : ActionEquiv (s.action.comp L.subtype) (alternatingNatural 8))
      (model : IsAlternatingNatural (s.space.toRepresentation.comp L.subtype) 8 ∨
        Nonempty (ActionEquiv (s.space.toRepresentation.comp L.subtype)
          (BinaryPermutation.alternatingCoreRepresentation (Fin 8))))
      (dimension : Module.finrank (ZMod 2) s.space.toSubmodule = 6 ∨
        Module.finrank (ZMod 2) s.space.toSubmodule = 7)
  | exterior (degree : n = 5) (equiv : L ≃* SL(5,ZMod 2))
      (irreducible : IsIrreducible (s.space.toRepresentation.comp L.subtype))
      (dimension : Module.finrank (ZMod 2) s.space.toSubmodule = 10)
  | naturalDual (natural : IsNaturalPlusDual (s.space.toRepresentation.comp L.subtype) n)
  | repeatedNatural (r : ℕ) (positive : 0 < r) (bound : r ≤ n - 1)
      (natural : IsRepeatedLinearNatural (s.space.toRepresentation.comp L.subtype)
        BinaryField.two n r)

theorem movedCase {s : MovedSection ρ L} {n : ℕ} (hn : n = 4 ∨ n = 5)
    (h : ActionCase ρ L s n) : MovedCase s n := by
  cases h with
  | naturalDual _ hnat => exact .naturalDual hnat
  | repeatedNatural r hp hb _ hnat => exact .repeatedNatural r hp hb hnat
  | irreducible hi hf hir hs he =>
    cases hs with
    | natural hg e hr =>
      have hc := binaryLinear_isCompl s hi (by rcases hn with rfl | rfl <;> decide) e
      let q := splitEquiv s hc
      exact .natural ⟨e.groupEquiv,q.linearEquiv.symm.trans e.linearEquiv,fun g v => by
        change e.linearEquiv (q.linearEquiv.symm (s.space.toRepresentation g v)) =
          linearNatural BinaryField.two n (e.groupEquiv g) (e.linearEquiv (q.linearEquiv.symm v))
        rw [← e.intertwines]
        congr 1⟩
    | orthogonal hd _ _ e _ _ =>
      exact .orthogonal hd e (orthogonal_moved_model s hi e) (orthogonal_dimension s hi e)
    | symmetricEight hd _ e _ =>
      let eL := markedRestriction e
      exact .orthogonal hd eL (orthogonal_moved_model s hi eL) (orthogonal_dimension s hi eL)
    | exterior hd hg hw e hdim ho hr =>
      have hc := exteriorFive_isCompl s ⟨hi,hf,hir,.exteriorFive hg hw e hdim ho hr,he⟩ e hdim
      let q := splitEquiv s hc
      let a : ActionEquiv (s.space.toRepresentation.comp L.subtype) (s.action.comp L.subtype) :=
        ⟨MulEquiv.refl _,q.linearEquiv.symm,fun g v => by
          apply q.linearEquiv.injective
          rw [q.linearEquiv.apply_symm_apply]
          change (s.space.toRepresentation.comp L.subtype) g v =
            q.linearEquiv ((s.action.comp L.subtype) g (q.linearEquiv.symm v))
          rw [q.intertwines]
          exact congrArg ((s.space.toRepresentation.comp L.subtype) g) (q.linearEquiv.apply_symm_apply v).symm⟩
      exact .exterior hd e (irreducible_of_equiv a hir)
        (q.linearEquiv.finrank_eq.symm.trans hdim)
end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion.BinaryActor
