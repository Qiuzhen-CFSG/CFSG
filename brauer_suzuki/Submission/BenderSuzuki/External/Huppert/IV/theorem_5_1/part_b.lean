/-
Authors: OpenAI
-/

module

public import Submission.BenderSuzuki.External.Huppert.IV.theorem_5_1.part_a

/-!
# Huppert IV.5.1(b)

The Burnside witness contains a `q`-subgroup; this file exposes that clause
with explicit parameters.
-/

namespace BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

universe u

/-- Huppert IV.5.1(b): the subgroup in the Burnside witness is a `q`-group. -/
public theorem huppert_IV_5_1_b_witness_subgroup_isPGroup
    {Q : Type u} [Group Q] {q : ℕ} (A : Subgroup Q)
    (A_p : IsPGroup q A) :
    IsPGroup q A :=
  A_p

end External
end BenderSuzuki
