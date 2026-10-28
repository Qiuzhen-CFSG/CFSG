module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.CentralFactors
public import Theory.Representation.BinaryOffender.GeneratedCore

/-!
# Literal invariant chief flags for the natural-component argument

A flag records actual L-invariant subspaces with irreducible successive
quotients and separately records the A-stability needed for the quotient
A-actions. Its noncentral count is exactly `noncentralFactors` from
`CentralFactors`, and its factor actions are restrictions of the original
representation to LA. The generic telescope converts local factor estimates
into an ambient fixed-codimension bound.

This module specifies the flag data and proves the telescope; existence of
such flags and the sharp local factor estimates are still to be proved.
No existence, irreducibility, numerical estimate or factor count is taken
as a source theorem merely by defining this output structure.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.108, inequality (!).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
open QuasisimpleSource
set_option backward.isDefEq.respectTransparency false
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

structure InvariantChiefFlag (A L : Subgroup G) (S : Submodule (ZMod 2) V) where
  length : ℕ
  term : ℕ → Subrepresentation (ρ.comp L.subtype)
  monotone : Monotone term
  start : term 0 = ⊥
  stop : (term length).toSubmodule = S
  stable : ∀ i, A ≤ subspaceStabilizer ρ (term i).toSubmodule
  chief : ∀ i < length, IsIrreducible
    (sectionRepresentation (ρ.comp L.subtype) (term i) (term (i + 1)))

namespace InvariantChiefFlag
variable {ρ} {A L : Subgroup G} {S : Submodule (ZMod 2) V}
  (f : InvariantChiefFlag ρ A L S)

noncomputable def termOver (i : ℕ) : Subrepresentation (ρ.comp (L ⊔ A).subtype) where
  toSubmodule := (f.term i).toSubmodule
  apply_mem_toSubmodule g v hv := by
    have hl : L ≤ subspaceStabilizer ρ (f.term i).toSubmodule :=
      le_subspaceStabilizer ρ _ (fun l hl v hv => (f.term i).apply_mem_toSubmodule ⟨l, hl⟩ hv)
    have h := sup_le hl (f.stable i)
    exact (h g.property v).2 hv

theorem termOver_monotone : Monotone f.termOver := fun _ _ h => f.monotone h

noncomputable def noncentral : Finset ℕ :=
  noncentralFactors (ρ.comp L.subtype) f.term f.length

noncomputable def factorAction (i : ℕ) :=
  sectionRepresentation (ρ.comp (L ⊔ A).subtype) (f.termOver i) (f.termOver (i + 1))

noncomputable def factorCodim (i : ℕ) : ℕ :=
  fixedCodim (f.factorAction i) (A.subgroupOf (L ⊔ A))

noncomputable def factorDimension (i : ℕ) : ℕ :=
  Module.finrank (ZMod 2) ((f.term (i + 1)).toSubmodule ⧸
    (sectionLower (ρ.comp L.subtype) (f.term i) (f.term (i + 1))).toSubmodule)

theorem noncentral_mem {i : ℕ} : i ∈ f.noncentral ↔
    i < f.length ∧ ¬ ∀ l v,
      sectionRepresentation (ρ.comp L.subtype) (f.term i) (f.term (i + 1)) l v = v := by
  classical
  simp [noncentral, noncentralFactors]

theorem count_mul_le_fixedCodim [Module.Finite (ZMod 2) V] (m : ℕ)
    (h : ∀ i ∈ f.noncentral, m ≤ f.factorCodim i) :
    f.noncentral.card * m ≤ fixedCodim ρ A := by
  classical
  have hsub : f.noncentral ⊆ Finset.range f.length := by
    intro i hi
    exact Finset.mem_range.mpr ((f.noncentral_mem).mp hi).1
  have hfirst : f.noncentral.card * m ≤ ∑ i ∈ f.noncentral, f.factorCodim i := by
    calc
      _ = ∑ _i ∈ f.noncentral, m := by simp
      _ ≤ _ := Finset.sum_le_sum h
  have hsum := Finset.sum_le_sum_of_subset (f := f.factorCodim) hsub
  have hlast := sum_fixedCodim_flag_le (ρ.comp (L ⊔ A).subtype)
    f.termOver f.termOver_monotone f.length (A.subgroupOf (L ⊔ A))
  rw [fixedCodim_subgroupOf ρ le_sup_right] at hlast
  exact hfirst.trans (hsum.trans hlast)

end InvariantChiefFlag
end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
