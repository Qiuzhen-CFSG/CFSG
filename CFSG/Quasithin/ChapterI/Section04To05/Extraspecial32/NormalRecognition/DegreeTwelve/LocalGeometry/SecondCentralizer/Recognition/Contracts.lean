module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.Models
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.Recognition.ModelFacts

/-!
# Transfer and extension interfaces for the second centralizer

TransferKernel requests a normal subgroup of index four whose intersection
with the given local model is exactly its A₄ factor. It assumes no global
fusion, involution-centralizer theorem or model recognition. The two Thompson
transfers must construct this subgroup from LocalSeed.

LocalExtension requests an actual isomorphism of the whole centralizer,
agreeing on the given local subgroup with the literal first-four-letters
inclusion. Global ambient class preservation is proved separately.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemma 4.2.
-/

@[expose] public section
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
open Subgroup Equiv Equiv.Perm
variable {G : Type*} [Group G] {z t : G}

/-- The exact index-four kernel to be constructed by the two transfers. -/
structure TransferKernel (s : LocalSeed z t) where
  K : Subgroup (Centralizer t)
  normal : K.Normal
  index : K.index = 4
  local_mem : ∀ x : Model 4, s.embed x ∈ K ↔ x.1 = 1 ∧ sign x.2 = 1

/-- A full-centralizer equivalence extending the literal first-four-letters inclusion. -/
structure LocalExtension (s : LocalSeed z t) (n : ℕ) (hn : 4 ≤ n) where
  equiv : Centralizer t ≃* Model n
  agrees_on_local : ∀ x : Model 4, equiv (s.embed x) = modelInclusion n hn x

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
end
