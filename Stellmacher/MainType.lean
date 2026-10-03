module

public import Stellmacher.MainType.EightSix
public import Stellmacher.MainType.NineOne
public import Stellmacher.MainType.TenOne

/-!
# The eight local types in Stellmacher's first theorem

The first four alternatives use the unchanged exceptional local types. The
remaining alternatives retain the exact configurations (10.1)(a), (9.1),
(8.6)(b), and (8.6)(c), including their ambient Sylow pairs and normalizer or
centralizer obstructions. The final source type is Omega-eight-plus-three.
The supplied Sylow argument is retained in the main public interface; the
local types themselves are properties of the ambient group.

These are the paper's precise definitions following (8.2), (8.6), (9.1), and
(10.1), not an assertion of identification with a concrete ambient group.
The separate `HasMainModelAmalgam` interface retains the earlier model-level
question. Source: Stellmacher, Journal of Algebra 190 (1997), Theorem 1 and
the type definitions on printed pp.38,45,48,65.
-/

namespace Stellmacher
universe u

/-- The eight source-local alternatives in Theorem 1. -/
@[expose] public def IsOfEightLocalTypes
    (H : Type u) [Group H] [Finite H] : Prop :=
  IsOfExceptionalType H ∨ IsOfMathieuTwelveType H ∨
    IsOfOmegaSixPlusTwoType H ∨ IsOfOmegaSixMinusThreeType H ∨
      IsOfOmegaEightPlusThreeType H

/-- The source-local type conclusion for the supplied Sylow of Theorem 1. -/
@[expose] public def IsOfMainTheoremType
    {H : Type u} [Group H] [Finite H] (_S0 : Sylow 2 H) : Prop :=
  IsOfEightLocalTypes H

end Stellmacher
