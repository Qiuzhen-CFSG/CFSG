module

public import Theory.Representation.BinaryOffender.Basic
public import Theory.SpecificGroups.Frobenius21.Model
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!+# Contracts for the regular cyclic normal-closure theorem

The input is a faithful binary representation with a cyclic subgroup acting
regularly on its moved space. This subgroup is normal in the stabilizer of
its fixed space, and its moved dimension is smaller than every involution
codimension. The output describes the actual normal closure, its internal
factors and compatible summands. All conjugation and module maps use the
given representation. The exceptional factor is the concrete C₇ ⋊ C₃.

These are interfaces, not an assertion of existence of a decomposition.
The required theorem is the extension of O'Nan's lemma cited as Aschbacher,
*Weak closure in finite groups of even characteristic*, J. Algebra 70
(1981), 10.4, in Aschbacher–Smith E.6.24, printed p.255. The narrower
Goldschmidt–O'Nan result is transcribed in `refs/KGroup/GLS2/ChapterC.tex`,
Proposition 14.2; it has an additional TI assumption and is not substituted
for the extension here.
-/

@[expose] public section

namespace Representation.RegularCyclicNormalClosure

open Subgroup BinaryOffender

variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]

/-- The span of displacements of vectors in S by elements of C. -/
def displacementSpan (ρ : Representation (ZMod 2) A W) (C : Subgroup A)
    (S : Submodule (ZMod 2) W) : Submodule (ZMod 2) W :=
  Submodule.span (ZMod 2) {w | ∃ c ∈ C, ∃ v ∈ S, ρ c v - v = w}

/-- The module-theoretic hypotheses used by E.6.24. The normality clause
concerns the setwise stabilizer of the fixed space. -/
structure Input (ρ : Representation (ZMod 2) A W) (C : Subgroup A) : Prop where
  faithful : Function.Injective ρ
  nontrivial : C ≠ ⊥
  cyclic : IsCyclic C
  fixed_nontrivial : fixedSpace ρ C ≠ ⊥
  split : IsCompl (fixedSpace ρ C) (displacementSpan ρ C ⊤)
  regular : ∀ v ∈ displacementSpan ρ C ⊤, v ≠ 0 →
    ∀ w ∈ displacementSpan ρ C ⊤, w ≠ 0 → ∃! c : C, ρ c v = w
  normal_in_stabilizer : ∀ a : A,
    (fixedSpace ρ C).map (ρ a) = fixedSpace ρ C →
    C.map (MulAut.conj a).toMonoidHom = C
  moved_dimension_gt_one : 1 < Module.finrank (ZMod 2) (displacementSpan ρ C ⊤)
  no_small_involutions : ∀ a : A, orderOf a = 2 →
    Module.finrank (ZMod 2) (displacementSpan ρ C ⊤) < fixedCodim ρ (zpowers a)

/-- The complete internal group and module decomposition required by E.6.24.
Existence of this record is the theorem still to be proved. -/
structure Decomposition (ρ : Representation (ZMod 2) A W) (C : Subgroup A) where
  size : ℕ
  positive : 0 < size
  factor : Fin size → Subgroup A
  summand : Fin size → Submodule (ZMod 2) W
  distinguished : Fin size
  contained : C ≤ factor distinguished
  group_eq : (⨆ i, factor i) = normalClosure (C : Set A)
  group_independent : iSupIndep factor
  commuting : Pairwise fun i j => ∀ a ∈ factor i, ∀ b ∈ factor j, Commute a b
  split : IsCompl (fixedSpace ρ (normalClosure (C : Set A)))
    (displacementSpan ρ (normalClosure (C : Set A)) ⊤)
  moved_eq : displacementSpan ρ (normalClosure (C : Set A)) ⊤ = ⨆ i, summand i
  summands_independent : iSupIndep summand
  self_moved : ∀ i, displacementSpan ρ (factor i) (summand i) = summand i
  cross_fixed : ∀ i j, i ≠ j → ∀ a ∈ factor i, ∀ v ∈ summand j, ρ a v = v
  permuted : ∀ a : A, ∃ σ : Equiv.Perm (Fin size), ∀ i,
    (factor i).map (MulAut.conj a).toMonoidHom = factor (σ i) ∧
      (summand i).map (ρ a) = summand (σ i)
  transitive : ∀ i j, ∃ a : A,
    (factor i).map (MulAut.conj a).toMonoidHom = factor j ∧
      (summand i).map (ρ a) = summand j
  alternatives : C = factor distinguished ∨
    (Nat.card C = 3 ∧ Nonempty (factor distinguished ≃* Frobenius21.Model) ∧
      normalClosure (C.subgroupOf (factor distinguished) : Set (factor distinguished)) = ⊤ ∧
      ∀ i, Module.finrank (ZMod 2) (summand i) = 3)

end Representation.RegularCyclicNormalClosure
