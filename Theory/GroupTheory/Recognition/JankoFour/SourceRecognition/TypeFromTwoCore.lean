module

public import Theory.GroupTheory.Recognition.JankoFour.LocalHypotheses
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The type-J₄ hypotheses from a characteristic-two centralizer

The quasithin application first identifies the two-core of the involution
centralizer. Self-centralization identifies this subgroup with the generalized
Fitting subgroup. Transport along that equality retains the actual cubic
quotient, and the returning conjugate is taken in the original ambient group.

This is the input conversion for recognition, not the uniqueness theorem.
Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*, Invent.
Math. 105 (1991), 589–607, definition on p.589 and Hypothesis J₄ on p.597;
Aschbacher–Smith, 8.2.12–14, printed pp.722–723.
-/

public section

namespace Theory.GroupTheory.Recognition.JankoFour

private theorem cubicQuotient_congr {H : Type*} [Group H]
    (A B : Subgroup H) [A.Normal] [B.Normal] (h : A = B)
    (e : Nonempty (CubicAutomorphismQuotient (H ⧸ A))) :
    Nonempty (CubicAutomorphismQuotient (H ⧸ B)) := by
  subst B
  exact e

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Convert the literal two-core data to the source definition, retaining the
order-three kernel and the ambient returning conjugator. -/
theorem isTypeJ4_of_twoCore
    (hz : orderOf z = 2)
    (hself : Subgroup.centralizer
      (pCore 2 (centralizer z) : Set (centralizer z)) ≤ pCore 2 (centralizer z))
    (hextra : IsExtraspecial 2 (pCore 2 (centralizer z)))
    (hcard : Nat.card (pCore 2 (centralizer z)) = 2 ^ 13)
    (hquot : Nonempty (CubicAutomorphismQuotient
      ((centralizer z) ⧸ pCore 2 (centralizer z))))
    (hfusion : ∃ g : G,
      g * z * g⁻¹ ∈ (pCore 2 (centralizer z)).map (centralizer z).subtype ∧
      g * z * g⁻¹ ≠ z) : IsTypeJ4 z := by
  have hcore : core z = pCore 2 (centralizer z) :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2 hself
  refine ⟨hz, hcore ▸ hextra, ?_, ?_, ?_⟩
  · simpa only [hcore] using hcard
  · exact cubicQuotient_congr _ _ hcore.symm hquot
  · apply (fusion_iff_exists_conjugator z).mpr
    simpa only [ambientCore, hcore] using hfusion

end Theory.GroupTheory.Recognition.JankoFour

end
