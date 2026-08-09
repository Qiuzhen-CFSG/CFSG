/-
Comparator solution.  The definitions come from `Defs.lean`, shared with the challenge; the
statement is the challenge's, proved.  Nobody needs to read this file.

It does not import `Challenge`, so nothing here can influence what the challenge asks for.

The challenge's definitions are the repository's, transcribed; the two agree definitionally,
so the proof is the repository's theorem with its conclusion re-tagged.
-/
module
public import Comparator.BenderSuzukiTheorem.Defs
import BenderSuzuki.FinalTheorem

universe u

namespace BSTheorem

public theorem bender_suzuki {X : Type u} [Group X] [Finite X] [IsSimpleGroup X] (M : Subgroup X)
    (hM : IsStronglyEmbedded M) : IsSimpleBenderGroup X := by
  rcases _root_.bender_suzuki M hM with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · exact .isPSL2 n hn e
  · exact .isSuzuki n hn e
  · exact .isPSU3 n hn e

end BSTheorem
