module

public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.TwoPowerActors

/-!
# Intrinsic two-power actors on the symplectic Borel

For Sp₄(F), with |F| = 2^n and n > 1, let S be a specified Sylow
two-subgroup and B = O²(N(S)). A two-group of automorphisms stabilizing S
and containing its inner image fixes O³(B)O₂(B)/O₂(B) precisely through
that inner image, unless n = 2 or 6. In both exceptional degrees every
outer actor has |[B,α]/O₂([B,α])| > 3, including over F₄.

The proof instantiates the actual Borel-action transfer with the arithmetic
of arbitrary two-power actors in the exceptional graph-generated torus
group. Thus neither a torus-fixer premise nor a displacement-bound premise
remains. The only classification input is the explicitly typed earlier
description of diagram-preserving automorphisms as inner times field.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954 (PDF p.971).
These are intrinsic calculations in Aut(Sp₄(F)); an ambient lift must also
retain the kernel of its action on Sp₄(F).
-/

public section

open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.IntrinsicActors
open DiagramAutomorphisms

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Away from degrees two and six, the residual fixer is the inner Sylow image. -/
theorem fixes_residualAt_iff_mem_innerSylow {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (hn2 : n ≠ 2) (hn6 : n ≠ 6)
    (S : Sylow 2 (Sp F)) (A : Subgroup (MulAut (Sp F))) (hA : IsPGroup 2 A)
    (hI : (S : Subgroup (Sp F)).map (MulAut.conj : Sp F →* MulAut (Sp F)) ≤ A)
    (hS : ∀ a ∈ A, (S : Subgroup (Sp F)).map a.toMonoidHom = S)
    {a : MulAut (Sp F)} (ha : a ∈ A) :
    (∀ b ∈ (pResidual 3 (residualAt S)).map (residualAt S).subtype ⊔
        (residualAt S).pCoreIn 2,
      b⁻¹ * a b ∈ (residualAt S).pCoreIn 2) ↔
    a ∈ (S : Subgroup (Sp F)).map (MulAut.conj : Sp F →* MulAut (Sp F)) :=
  ActorReduction.fixes_residualAt_iff_mem_innerSylow hF hn hclass
    (two_power_fixed_residual_degree hn hF) hn2 hn6 S A hA hI hS ha

/-- The exceptional-degree commutator bound holds for every outer two-power actor. -/
theorem three_lt_commutator_quotient {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (hsmall : n = 2 ∨ n = 6)
    (S : Sylow 2 (Sp F)) (A : Subgroup (MulAut (Sp F))) (hA : IsPGroup 2 A)
    (hS : ∀ a ∈ A, (S : Subgroup (Sp F)).map a.toMonoidHom = S)
    {a : MulAut (Sp F)} (ha : a ∈ A) (houter : a ∉ MulAut.innerSubgroup (Sp F)) :
    3 < Nat.card (commutatorSubgroup (zpowers a) (Sp F) (residualAt S) ⧸
      pCore 2 (commutatorSubgroup (zpowers a) (Sp F) (residualAt S))) :=
  ActorReduction.three_lt_commutator_quotient hF hn hclass
    (two_power_displacement_gt_three hF) hsmall S A hA hS ha houter

end Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.IntrinsicActors
