/-
Authors: OpenAI
-/

module

public import Submission.BenderSuzuki.External.Huppert.IV.Basic

/-!
# Huppert IV.5.4(b)

Book clause: every proper subgroup of a minimal non-`p`-nilpotent group is
nilpotent.
-/

namespace BenderSuzuki
namespace External

universe u

/-- Huppert IV.5.4(b): every proper subgroup is nilpotent.

The final proof belongs here; until that proof is formalized, callers must pass
this clause as an explicit source hypothesis rather than through a packaged
statement definition. -/
public theorem huppert_IV_5_4_b_every_proper_subgroup_nilpotent
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (_hproper : ∀ H : Subgroup Q, H ≠ ⊤ → HasNormalPComplement p H)
    (_hnot : ¬ HasNormalPComplement p Q)
    (hsource : ∀ H : Subgroup Q, H ≠ ⊤ → Group.IsNilpotent H) :
    ∀ H : Subgroup Q, H ≠ ⊤ → Group.IsNilpotent H :=
  hsource

end External
end BenderSuzuki
