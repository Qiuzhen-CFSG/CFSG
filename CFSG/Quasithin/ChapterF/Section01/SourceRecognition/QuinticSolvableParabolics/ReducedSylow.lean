module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.QuinticSolvableParabolics.LocalStructure
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.SuzukiContainment.ReducedPair

/-!
# The quintic reduction has no original-to-reduced Sylow gap

For the F.1.1 pair `![K,R]` with `S ≤ K`, the local Sylow contained in the
first endpoint is already the whole original `S`.  Since the reduced Sylow is
the two-core of the common Borel and is squeezed between the original local
Sylow and `S`, it equals `S`.  This identity is the transport step needed by
the DGS reduced catalogue: all reduced endpoint and parabolic quotients are
then literal subgroups of the original pair.

Source: Aschbacher--Smith F.1.1 and F.1.12, printed pp.259--264; the reduced
pair construction in DGS, *Groups and Graphs* (1985), pp.95--96.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source
open SuzukiContainment

variable {G : Type*} [Group G] {K R S : Subgroup G}

/-- In the index-five branch the reduced Sylow is the literal original `S`.
The proof uses only the first local containment, so no Sylow hypothesis on the
generated group is introduced. -/
theorem HypothesisF11.quintic_reducedSylow_eq
    (h : HypothesisF11 ![K,R] S) (hSK : S ≤ K) :
    reducedSylow ![K,R] S = S := by
  apply le_antisymm (reducedSylow_le h)
  have hs := localSylow_le_reducedSylow h 0
  simpa only [Matrix.cons_val_zero, inf_eq_left.mpr hSK] using hs

end CFSG.Quasithin.ChapterF.Source
