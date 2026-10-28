module

public import CFSG.Quasithin.ChapterE.Section05.GenerationFromCenter.OddMinimal.Defs
public import CFSG.Quasithin.ChapterE.Section05.GenerationFromCenter.OddMinimal.Structure

/-!
# Quotient pieces for the reducible odd E-member argument

In Q = K/O₂(K), a piece J contains the prescribed Sylow image S, is proper,
and has a nontrivial normal p-subgroup N with two-group quotient and
N = [N,a]. These concrete conditions can be constructed from invariant
subspaces of the odd Frattini section. They do not assert E-membership:
`Lifting` proves the E1 conditions using the lift's intrinsic two-core.

Source: Aschbacher–Smith, E.5.2, printed p.243, and E.1.2(E1), printed p.210
(combined manuscript, 1 March 2004).
-/

open Subgroup
namespace CFSG.Quasithin.ChapterE

/-- A proper quotient subgroup containing the specified Sylow image, with a genuine
normal odd subgroup before removal of its own two-core. -/
@[expose] public def OddQuotientPiece {Q : Type*} [Group Q] [Finite Q]
    (p : ℕ) (a S J : Subgroup Q) : Prop :=
  S ≤ J ∧ J ≠ ⊤ ∧ ∃ N : Subgroup J, ∃ _ : N.Normal,
    IsPGroup p N ∧ IsPGroup 2 (J ⧸ N) ∧ N ≠ ⊥ ∧
    N = ⁅N, a.subgroupOf J⁆

end CFSG.Quasithin.ChapterE
