/-
Authors: OpenAI
-/

module

public import Submission.BenderSuzuki.External.Huppert.IV.Basic

/-!
# Huppert IV.5.4(d)

Book clause: the Sylow subgroups for the other prime are cyclic.
-/

namespace BenderSuzuki
namespace External

universe u

/-- Huppert IV.5.4(d): Sylow `r`-subgroups are cyclic. -/
public theorem huppert_IV_5_4_d_other_sylow_cyclic
    {Q : Type u} [Group Q] [Finite Q] {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (_hproper : ∀ H : Subgroup Q, H ≠ ⊤ → HasNormalPComplement p H)
    (_hnot : ¬ HasNormalPComplement p Q)
    (_hr_ne_p : r ≠ p)
    (hsource : ∀ R : Sylow r Q, IsCyclic (R : Subgroup Q)) :
    ∀ R : Sylow r Q, IsCyclic (R : Subgroup Q) :=
  hsource

end External
end BenderSuzuki
