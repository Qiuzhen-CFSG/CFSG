module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.ThompsonExtension.Application

/-!
# The Thompson extension in 15.3.68(5)

`apply_F611_B216` works intrinsically in `H = G₀`. Its inputs `V`, `Y`,
`F`, and `M` are the restrictions of the original ambient subgroups to
`H`; in particular its normalizer bound is `N_H(J) ≤ M ∩ H`. The input
`U` is an actual Sylow subgroup of `H`. The transport lemmas below tie it
to its prescribed ambient image `T_E`, and identify the extension Sylow
subgroup with `T_E ∩ X` in that original ambient group.

The proof constructs `X = J(U)O_{3'}(H)` and the genuine `R₂(X)` from
normal elementary abelian subgroups with two-reduced centralizer quotient.
B.2.16 applies to the smaller normal closure of the Sylow omega-center.
That closure is characteristic in `X` and contains `F`. Its centralizer
is a normal two-group by prime support; Thompson heredity then makes
`J(U)` normal in `X`. This establishes the literal product through the
full `R₂(X)` without changing B.2.16's statement. The existing
`CoreReduction` endpoints give the product in `P` and `P = O₂(H)`.

This is a completed conditional application. The parent retains the
local hypotheses, clauses (1)–(4), and discharge of the explicitly named
F.6.11(1) and B.2.16 witnesses. No unconditional numbered source theorem
is asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
15.3.68, printed pp.1154–1155; F.6.11(1), p.306; B.2.11–16, pp.77–79.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.ThompsonExtension
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- An actual Sylow witness with ambient image `T_E` has exactly the
source Thompson subgroup after inclusion into the original group. -/
theorem thompson_ambient_image (H T_E : Subgroup G) (U : Sylow 2 H)
    (hU : (U : Subgroup H).map H.subtype = T_E) :
    (elementaryAbelianMaxJ (U : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ T_E := by
  rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective, hU]

/-- The constructed Sylow subgroup is precisely the source intersection
`T_E ∩ X`, with all subgroups mapped into the original ambient group. -/
theorem sylow_ambient_intersection (H T_E : Subgroup G) (U : Sylow 2 H)
    (hU : (U : Subgroup H).map H.subtype = T_E)
    (hQ : IsSylowSubgroupIn (pCore 2 H) (pPrimeCore 3 H)) :
    (sylowImage U).map H.subtype = T_E ⊓ (extension U).map H.subtype := by
  rw [sylowImage_eq_inf U hQ, map_inf _ _ _ H.subtype_injective, hU]

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.ThompsonExtension
