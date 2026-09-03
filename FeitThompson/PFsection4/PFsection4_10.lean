module

public import FeitThompson.PFsection4.Basic
public import FeitThompson.PFsection2.Basic
public import FeitThompson.PFsection1.PFsection1_2
public import FeitThompson.PFsection1.PFsection1_5
public import FeitThompson.PFsection1.PFsection1_6
public import FeitThompson.HallSubgroups.Core

/-!
# Peterfalvi, Section 4: Theorem (4.10)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section4Scratch
universe u
universe v
open Section2 Section3 Section4

/-! ## (4.10) -/

@[expose] public def theorem_4_10_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    {W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    (i0 : I) (j0 : J)
    (ω : I → J → _root_.ClassFunction W)
    (σ : _root_.ClassFunction W →ₗ[ℂ] _root_.ClassFunction G)
    (piChar : I → J → _root_.ClassFunction L)
    (deltaSign : J → ℂ)
    (τ : _root_.ClassFunction L →ₗ[ℂ] _root_.ClassFunction G) : Prop :=
  ∀ i j,
    τ (deltaSign j • piChar i j - deltaSign j • piChar i0 j - piChar i j0 + piChar i0 j0) =
      (σ (ω i j) - σ (ω i0 j)) - (σ (ω i j0) - σ (ω i0 j0))

end Section4Scratch
