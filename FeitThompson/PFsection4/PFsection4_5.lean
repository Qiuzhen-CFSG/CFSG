module

public import FeitThompson.PFsection4.Basic
public import FeitThompson.PFsection4.PFsection4_4
public import FeitThompson.PFsection2.Basic
public import FeitThompson.PFsection1.PFsection1_2
public import FeitThompson.PFsection1.PFsection1_5
public import FeitThompson.PFsection1.PFsection1_6
public import FeitThompson.HallSubgroups.Core

/-!
# Peterfalvi, Section 4: Theorem (4.5)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section4Scratch
universe u
universe v
open Section2 Section3 Section4

/-! ## (4.5) -/

@[expose] public def theorem_4_5_a_statement
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    (piChar : I → J → _root_.ClassFunction L)
    (xChar : J → _root_.ClassFunction K) : Prop :=
  (∀ i j, Section1.subgroupRestriction K (piChar i j) = xChar j) ∧
    (∀ j, Section1.IsIrreducibleCharacterOnGroup (xChar j)) ∧
    ∀ j, Section1.inducedCF K (xChar j) = piColumn piChar j

@[expose] public def theorem_4_5_b_statement
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    (piChar : I → J → _root_.ClassFunction L)
    (xChar : J → _root_.ClassFunction K) : Prop :=
  (∀ X : _root_.ClassFunction K,
      Section1.IsIrreducibleCharacterOnGroup X →
        X ∉ Set.range xChar →
          Section1.IsIrreducibleCharacterOnGroup (Section1.inducedCF K X) ∧
            Section1.inducedCF K X ∉ Set.range (fun p : I × J => piChar p.1 p.2)) ∧
    ∀ ψ : _root_.ClassFunction L,
      Section1.IsIrreducibleCharacterOnGroup ψ →
        ψ ∈ Set.range (fun p : I × J => piChar p.1 p.2) ∨
          ∃ X : _root_.ClassFunction K,
            Section1.IsIrreducibleCharacterOnGroup X ∧
              X ∉ Set.range xChar ∧
                ψ = Section1.inducedCF K X

@[expose] public def theorem_4_5_statement
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    (piChar : I → J → _root_.ClassFunction L) : Prop :=
  ∃ xChar : J → _root_.ClassFunction K,
    theorem_4_5_a_statement K piChar xChar ∧
      theorem_4_5_b_statement K piChar xChar

end Section4Scratch
