module

public import CFSG.Quasithin.ChapterE.Section05.Defs

/-!
# The odd Frattini section in E.5.2

The source sets Q = K/O₂(K), F = F*(Q), and R/O₂(K) = Φ(F).
In case E1, F is an odd prime core. Irreducibility of conjugation on
F/Φ(F) says that every Q-normal subgroup contained in F has either
zero or full image on that section. The definition below records this
normal-subgroup formulation, without assuming it for E-members.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.5.2,
printed p.243. See `Structure` for the identification of F with the
image of O²(K).
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE

/-- Irreducibility on the odd Frattini section, expressed using normal
subgroups of the actual quotient K/O₂(K). -/
@[expose] public def OddFrattiniIrreducible (K : Type*) [Group K] : Prop :=
  let Q := K ⧸ pCore 2 K
  let F := generalizedFitting Q
  ∀ N : Subgroup Q, N.Normal → N ≤ F →
    N ≤ (frattini F).map F.subtype ∨ N ⊔ (frattini F).map F.subtype = F

end CFSG.Quasithin.ChapterE
