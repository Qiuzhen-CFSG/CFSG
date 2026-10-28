module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.Action
public import Theory.Mathieu.M12.Basic
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!+# The three residual-centralizer cases in 16.4.9(1)

The starred groups are actual images in H* = N_G(L)/C_G(L). The S₈ case
identifies L*T* with the permutation group, carries L* onto A₈, and marks
the image of the given outer involution with cycle type 2³1². The M₁₂ case
identifies both L* and the image of the actual two-residual O²(C_L(r)).

These predicates specify the model calculations still needed for the order
argument. They do not prove that the alternatives are exhaustive or exclude
either exceptional case. In particular the elementary order-four assertion
is a conclusion to be established by the model calculation.

For case (I) we ask for a Sylow two-subgroup of the residual centralizer of
order two. This is the sufficient intrinsic bound: the literal full-centralizer
equality on p.1189 would exclude odd centralizer elements, even though the
later graph-field case has the abelian residual E₉ (p.1191). The stronger full
bound remains usable through `Reductions` wherever the actual model supplies it.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 16.4.9(1), printed p.1189, cases (I)–(III).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo

open Subgroup OuterResidual

variable {G : Type*} [Group G]

/-- The outer-involution consequence of 16.4.8, with its actual residual and
conjugate component. It is an earlier-source input, not asserted here. -/
def OuterResidualTransfer (L : Subgroup G) (g : G) (R : Subgroup G) : Prop :=
  ∀ s ∈ R, orderOf s = 2 → s ∉ centralizer (L : Set G) ⊔ L →
    involutionResidual L s ≤ L.conjBy g

/-- Source case (II), including the marking of L* and of r* in L*T*.
The fixed points are implicit in the degree eight and cycle type {2,2,2}. -/
def SymmetricEightCase (T : Sylow 2 G) (L : Subgroup G) (r : G) : Prop :=
  ∃ e : actionImage L (L ⊔ (T : Subgroup G)) ≃* Equiv.Perm (Fin 8),
    ((actionImage L L).subgroupOf (actionImage L (L ⊔ (T : Subgroup G)))).map
      e.toMonoidHom = alternatingGroup (Fin 8) ∧
    ∃ hr : r ∈ normalizer (L : Set G),
      ∃ rStar : actionImage L (L ⊔ (T : Subgroup G)),
        (rStar : ActionQuotient L) = actionElement L r hr ∧
        (e rStar).cycleType = {2, 2, 2}

/-- Source case (III). These are isomorphisms of the actual quotient images;
they do not identify a nontrivial cover L with M₁₂. -/
def MathieuTwelveCase (L : Subgroup G) (r : G) : Prop :=
  Nonempty (actionImage L L ≃* Sporadic.Mathieu.M12) ∧
    Nonempty (actionImage L (involutionResidual L r) ≃* alternatingGroup (Fin 5))

/-- A sufficient intrinsic alternative for 16.4.9(1). The first branch
controls the two-part of the centralizer order, allowing odd elements.
The exceptional branches retain the whole E₄ centralizer in H*, not just
the centralizer inside L*T*. This is a proof target, not an asserted table. -/
def ResidualCentralizerAlternative (T : Sylow 2 G) (L : Subgroup G) (r : G) : Prop :=
  (∃ S : Sylow 2 (residualCentralizer L r), Nat.card S = 2) ∨
    (Nat.card (residualCentralizer L r) = 4 ∧
      IsElementaryAbelian 2 (residualCentralizer L r) ∧
      (SymmetricEightCase T L r ∨ MathieuTwelveCase L r))

end CFSG.Quasithin.Chapter16.Intersections.OrderTwo
