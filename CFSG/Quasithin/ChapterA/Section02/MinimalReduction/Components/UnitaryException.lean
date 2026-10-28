module

public import CFSG.Quasithin.ChapterA.Section02.Statements.UnitaryPairTransport
public import CFSG.Quasithin.ChapterA.Section02.OddCenterCovers.UnitaryCentralProduct.Source

/-!
# The full exceptional conclusion from the actual unitary central product

The proved source model calculation supplies rank three and the gcd condition.
Transport to the ambient top subgroup yields every field of the literal
Theorem A exception. Its ordinary-rank implication is vacuous because the
ambient three-rank is three. This closes the exceptional alternative once
the component-product argument supplies its two source components and the
actual central quotient marking.

Source: Aschbacher–Smith A.2.12(II), printed p.37.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
    [Group G] [Group S] [Finite G] [Finite S]

theorem CounterexampleToTheoremA.not_unitary_central_product
    (h : CounterexampleToTheoremA K G S 3)
    (d : OddCenterCovers.UnitaryCentralProductData G)
    (hfirst : IsComponent G d.first) (hsecond : IsComponent G d.second)
    (e : S ≃* G ⧸ center G) : False := by
  have hr := d.source_threeRank_eq_three h.1
  have dp := d.source_TheoremAUnitaryPair h.1 hfirst hsecond
  apply h.2.2.2.2.2.2
  exact ⟨.inr (dp.exception_of_centerQuotient hr e), fun hh => (by omega)⟩

end CFSG.Quasithin.ChapterA.Section02
