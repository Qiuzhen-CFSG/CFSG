module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.NaturalAction
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# Earlier-source inputs for the local calculation in 15.3.49

The ordinary input retains the actual E₉ quotient, the two-core centralizer,
and the prime-to-three residual. The extraspecial input retains the actual
order-27, exponent-three quotient, its central inverse image, and θ(M).
These are precisely the clauses of 15.3.7 used here; its cyclicity clauses
are not needed by these local calculations. Neither input asserts 15.3.49.

All cores and residuals are formed inside the indicated subgroup. In
particular `twoCenter Y` is O₂,Z(Y), not an ambient center or normal subgroup.
The parent must obtain these inputs from the genuine earlier theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.7, printed p.1122, and 15.3.49, printed pp.1142–1143.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

open Subgroup

variable {G : Type*} [Group G]

/-- O₂,Z(Y), the inverse image of the center of the actual two-core quotient. -/
def twoCenter (Y : Subgroup G) : Subgroup G :=
  ((center (Y ⧸ pCore 2 Y)).comap (QuotientGroup.mk' (pCore 2 Y))).map Y.subtype

/-- The complete ordinary alternative of 15.3.7, as an earlier-source input. -/
structure OrdinaryCase (M Y V : Subgroup G) : Prop where
  quotient_equiv : Nonempty ((Y ⧸ pCore 2 Y) ≃* Multiplicative (Fin 2 → ZMod 3))
  centralizer_eq : Y ⊓ centralizer (V : Set G) = Y.pCoreIn 2
  residual_eq : Y = (primeToResidual 3 M).map M.subtype

/-- The clauses of the extraspecial alternative used in the local calculation.
These contain no conclusion about H, its two-core, or either conjugate span. -/
structure ExtraspecialCase (M Y V : Subgroup G) : Prop where
  extraspecial : IsExtraspecial 3 (Y ⧸ pCore 2 Y)
  quotient_card : Nat.card (Y ⧸ pCore 2 Y) = 27
  quotient_exponent : Monoid.exponent (Y ⧸ pCore 2 Y) = 3
  centralizer_eq : Y ⊓ centralizer (V : Set G) = twoCenter Y
  theta_eq : Y = theta M

/-- Every clause of 15.3.49(3), before the later extraspecial exclusion. -/
def OrdinaryConclusion (M Y V Z : Subgroup G) : Prop :=
  OrdinaryCase M Y V ∧ Y ⊓ centralizer (V : Set G) = Y ⊓ centralizer (Z : Set G)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

end
