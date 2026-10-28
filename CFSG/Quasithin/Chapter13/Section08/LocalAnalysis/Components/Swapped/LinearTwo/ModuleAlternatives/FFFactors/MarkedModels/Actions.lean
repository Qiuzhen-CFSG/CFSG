module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.Conclusions
public import Theory.Representation.BinaryPermutationNaturalStructure

/-!
# The marked alternating action and its canonical moved space

An action equivalence can be restricted along the actual image of a marked
subgroup. Full generation by displacements then identifies an invariant
summand with the original component commutator, via its literal inclusion.
For the natural S₅ action, irreducibility under A₅ and one moving vector give
full generation. The odd-degree core-to-natural quotient equivalence
identifies the restricted action with the four-dimensional even-weight core.

The final helper assumes the marked subgroup image in S₅; `Groups.lean`
proves that image equality from the component and PSL₂ hypotheses. No
recognized module or canonical moved-space equality is an input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.3.1,
B.5.6(3a), printed pp.83, 105, and proof of 13.8.16(1), p.952 (PDF p.969).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.MarkedModels
noncomputable section
variable {D E V W : Type*} [Group D] [Group E]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) D V)

/-- Identifying an invariant space with the literal component commutator does not change its action. -/
def commutatorActionEquiv (X : Subrepresentation ρ) (A : Subgroup D)
    (hX : X.toSubmodule = subspaceCommutator ρ ⊤ A) :
    ActionEquiv (factorRepresentation ρ A) (X.toRepresentation.comp A.subtype) where
  groupEquiv := MulEquiv.refl A
  linearEquiv := LinearEquiv.ofEq _ _ hX.symm
  intertwines _ _ := rfl

/-- Restriction follows the actual image of the marked subgroup. -/
def restrictActionEquiv (X : Subrepresentation ρ) {A C : Subgroup D} (hAC : A ≤ C)
    {σ : Representation (ZMod 2) E W}
    (e : ActionEquiv (X.toRepresentation.comp C.subtype) σ)
    (B : Subgroup E) (hB : (A.subgroupOf C).map e.groupEquiv.toMonoidHom = B) :
    ActionEquiv (X.toRepresentation.comp A.subtype) (σ.comp B.subtype) where
  groupEquiv := ((subgroupOfEquivOfLe hAC).symm.trans
    (e.groupEquiv.subgroupMap (A.subgroupOf C))).trans (MulEquiv.subgroupCongr hB)
  linearEquiv := e.linearEquiv
  intertwines a v := e.intertwines ⟨a, hAC a.property⟩ v

/-- Full commutator generation is invariant under an action equivalence. -/
theorem actionEquiv_full_commutator {σ : Representation (ZMod 2) E W}
    (e : ActionEquiv ρ σ) (hσ : subspaceCommutator σ ⊤ ⊤ = ⊤) :
    subspaceCommutator ρ ⊤ ⊤ = ⊤ := by
  have h := subspaceCommutator_map_embedding ρ σ e.groupEquiv.toMonoidHom
    e.linearEquiv.symm.toLinearMap (fun g w => by
      apply e.linearEquiv.injective
      change e.linearEquiv (ρ g (e.linearEquiv.symm w)) =
        e.linearEquiv (e.linearEquiv.symm (σ (e.groupEquiv g) w))
      rw [e.intertwines, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]) ⊤ ⊤
  simpa only [Submodule.map_top, LinearEquiv.range, Subgroup.map_top_of_surjective e.groupEquiv.toMonoidHom
    e.groupEquiv.surjective, hσ] using h

/-- Full generation inside an invariant summand identifies its canonical ambient moved space. -/
theorem moved_eq_of_full_restriction (X : Subrepresentation ρ) (A : Subgroup D)
    (hle : subspaceCommutator ρ ⊤ A ≤ X.toSubmodule)
    (hfull : subspaceCommutator (X.toRepresentation.comp A.subtype) ⊤ ⊤ = ⊤) :
    X.toSubmodule = subspaceCommutator ρ ⊤ A := by
  apply le_antisymm _ hle
  intro x hx
  have hmap : (subspaceCommutator (X.toRepresentation.comp A.subtype) ⊤ ⊤).map
      X.toSubmodule.subtype ≤ subspaceCommutator ρ ⊤ A := by
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, _, v, _, rfl⟩
    exact Submodule.subset_span ⟨a, a.property, v, Submodule.mem_top, rfl⟩
  apply hmap
  rw [hfull, Submodule.map_top, Submodule.range_subtype]
  exact hx

private theorem full_commutator_of_irreducible [ρ.IsIrreducible]
    (hmove : ∃ g v, ρ g v ≠ v) : subspaceCommutator ρ ⊤ ⊤ = ⊤ := by
  let S : Subrepresentation ρ :=
    { toSubmodule := subspaceCommutator ρ ⊤ ⊤
      apply_mem_toSubmodule g v hv :=
        (subspaceCommutator_invariant ρ ⊤ ⊤ (mem_top g) v).mpr hv }
  rcases eq_bot_or_eq_top S with hs | hs
  · obtain ⟨g, v, hgv⟩ := hmove
    have hm : ρ g v - v ∈ S :=
      Submodule.subset_span ⟨g, mem_top g, v, Submodule.mem_top, rfl⟩
    rw [hs] at hm
    exact (hgv (sub_eq_zero.mp hm)).elim
  · exact congrArg Subrepresentation.toSubmodule hs

/-- The restricted natural S₅-module is the actual even-weight A₅-core. -/
def alternatingNaturalCoreEquiv :
    ActionEquiv (BinaryPermutation.alternatingNaturalRepresentation (Fin 5))
      (BinaryPermutation.alternatingCoreRepresentation (Fin 5)) where
  groupEquiv := MulEquiv.refl _
  linearEquiv := (BinaryPermutation.coreEquivNatural (Fin 5) (by decide)).symm
  intertwines g v := by
    let e := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
    apply e.injective
    change e (e.symm (BinaryPermutation.naturalRepresentation (Fin 5) g.val v)) =
      e (BinaryPermutation.coreRepresentation (Fin 5) g.val (e.symm v))
    rw [LinearEquiv.apply_symm_apply, BinaryPermutation.coreEquivNatural_equivariant,
      LinearEquiv.apply_symm_apply]

/-- A₅ generates the whole four-dimensional natural section by displacements. -/
theorem alternatingNatural_full_commutator :
    subspaceCommutator (BinaryPermutation.alternatingNaturalRepresentation (Fin 5)) ⊤ ⊤ = ⊤ := by
  let _ := BinaryPermutation.alternatingNatural_isIrreducible (Ω := Fin 5) (by decide)
  apply full_commutator_of_irreducible
  let g : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
      apply Equiv.Perm.mem_alternatingGroup.mpr
      decide⟩
  let v : BinaryPermutation.core (Fin 5) := ⟨![1, 1, 0, 0, 0], by
    apply BinaryPermutation.mem_core _ _ |>.mpr
    decide⟩
  let e := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  refine ⟨g, e v, ?_⟩
  intro h
  have hc : BinaryPermutation.coreRepresentation (Fin 5) g.val v = v := by
    apply e.injective
    rw [BinaryPermutation.coreEquivNatural_equivariant]
    exact h
  have hh := congrArg (fun x : BinaryPermutation.core (Fin 5) => x.val 0) hc
  change (0 : ZMod 2) = 1 at hh
  exact zero_ne_one hh

/-- From a marked symmetric actor to the canonical component module. -/
theorem symmetricFive_module (hfix : ρ.invariants = ⊥) (X : Subrepresentation ρ)
    {A C : Subgroup D} (hAC : A ≤ C)
    (hm : X.toSubmodule = subspaceCommutator ρ ⊤ C)
    (e : ActionEquiv (((fixed ρ).quotientImage X).toRepresentation.comp C.subtype)
      (BinaryPermutation.naturalRepresentation (Fin 5)))
    (hA : (A.subgroupOf C).map e.groupEquiv.toMonoidHom = alternatingGroup (Fin 5)) :
    X.toSubmodule = subspaceCommutator ρ ⊤ A ∧
      FactorModule (factorRepresentation ρ A) 2 := by
  let eX := composeActionEquiv (fixedQuotientActionEquiv ρ hfix X C) e
  let eA := restrictActionEquiv ρ X hAC eX (alternatingGroup (Fin 5)) hA
  have hfull := actionEquiv_full_commutator _ eA alternatingNatural_full_commutator
  have hle : subspaceCommutator ρ ⊤ A ≤ X.toSubmodule := by
    rw [hm]
    apply Submodule.span_mono
    rintro _ ⟨a, ha, v, hv, rfl⟩
    exact ⟨a, hAC ha, v, hv, rfl⟩
  have hX := moved_eq_of_full_restriction ρ X A hle hfull
  refine ⟨hX, .orthogonal rfl ?_⟩
  exact composeActionEquiv (commutatorActionEquiv ρ X A hX)
    (composeActionEquiv eA alternatingNaturalCoreEquiv)
end
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.MarkedModels
