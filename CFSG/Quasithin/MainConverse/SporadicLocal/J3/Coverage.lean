module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.LocalReduction
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.SylowEnumeration
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.Fusion
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.InvolutionCentralizer
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.RepresentativeCalculations
public import Theory.GroupTheory.CharacteristicCentralizerFusion
import Mathlib.Tactic.FinCases

/-!
# Assembly of the J₃ elementary-normalizer cover

Conjugation transports the normalizer of a subgroup to the normalizer of its
conjugate. Thus exhaustive fusion to the five fixed representatives reduces
the requested cover to five ambient normalizer calculations. Two of those
reduce further: if a representative's centralizer is the fixed elementary
candidate E, its normalizer normalizes E. The involution case is its ordinary
element centralizer. The remaining cases are N(E) and the normalizer of the
second order-four representative.

Source: GLS, Number 3, Table 5.3h, printed p.269, listing C(2A),
F₄² ⋊ GL₂(4), and N(J(S₂)) among all maximal local subgroups. The imported
certificates prove exhaustive Sylow fusion, the ambient involution centralizer,
and the remaining finite local calculations for the fixed model words.
`elementary_normalizer_cover` combines them using only the orders of the
ambient model, Sylow candidate, and involution-centralizer candidate. It
establishes the requested cover by conjugates of the three concrete candidates;
their remaining structure and the final QT/E assembly belong to the parent
J3 task.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage
open Subgroup Sporadic.Janko3 Sporadic.Janko3.TwoLocal

/-- The normalizer of the first representative is the centralizer of the
standard involution, with no ambient order assumption. -/
public theorem elementaryRepresentative_zero_normalizer :
    normalizer (elementaryRepresentative 0 : Set Model) =
      centralizer ({a} : Set Model) :=
  normalizer_zpowers_eq_centralizer_of_order_two a
    (orderOf_eq_prime a_sq a_ne_one)

/-- Five concrete ambient calculations give the representative bounds.
The two small-class centralizer equalities force their normalizers into N(E). -/
public theorem representative_normalizer_bounds_of_local_calculations
    (hC : centralizer ({a} : Set Model) ≤ localFamily 0)
    (hFour : normalizer (elementaryRepresentative 2 : Set Model) ≤ localFamily 2)
    (hE : normalizer (elementaryCandidate : Set Model) ≤ localFamily 1)
    (hCOne : centralizer (elementaryRepresentative 1 : Set Model) = elementaryCandidate)
    (hCThree : centralizer (elementaryRepresentative 3 : Set Model) = elementaryCandidate) :
    ∀ i : Fin 5, normalizer (elementaryRepresentative i : Set Model) ≤
      localFamily (representativeLocal i) := by
  have hOne := normalizer_le_normalizer_centralizer (elementaryRepresentative 1)
  have hThree := normalizer_le_normalizer_centralizer (elementaryRepresentative 3)
  rw [hCOne] at hOne
  rw [hCThree] at hThree
  intro i
  fin_cases i
  · exact elementaryRepresentative_zero_normalizer ▸ hC
  · exact hOne.trans hE
  · exact hFour
  · exact hThree.trans hE
  · exact hE

/-- Actual conjugacy witnesses transport the five normalizer bounds to every
nontrivial elementary subgroup in the fixed Sylow candidate. -/
public theorem elementary_normalizer_cover_of_fusion
    (hfusion : ∀ A : Subgroup Model, A ≤ sylowCandidate → A ≠ ⊥ →
      IsElementaryAbelian 2 A → ∃ (i : Fin 5) (g : Model),
        A = (elementaryRepresentative i).map (MulAut.conj g).toMonoidHom)
    (hN : ∀ i : Fin 5, normalizer (elementaryRepresentative i : Set Model) ≤
      localFamily (representativeLocal i)) :
    ∀ A : Subgroup Model, A ≤ sylowCandidate → A ≠ ⊥ →
      IsElementaryAbelian 2 A → ∃ (i : Fin 3) (g : Model),
        normalizer (A : Set Model) ≤ (localFamily i).map (MulAut.conj g).toMonoidHom := by
  intro A hAS hA hEA
  obtain ⟨i, g, rfl⟩ := hfusion A hAS hA hEA
  refine ⟨representativeLocal i, g, ?_⟩
  rw [← map_equiv_normalizer_eq]
  exact map_mono (hN i)

/-- The assembly route from Sylow fusion and centralizer/normalizer
calculations, with their inputs kept explicit for reuse. -/
public theorem elementary_normalizer_cover_of_fusion_and_local_calculations
    (hfusion : ∀ A : Subgroup Model, A ≤ sylowCandidate → A ≠ ⊥ →
      IsElementaryAbelian 2 A → ∃ (i : Fin 5) (g : Model),
        A = (elementaryRepresentative i).map (MulAut.conj g).toMonoidHom)
    (hC : centralizer ({a} : Set Model) ≤ localFamily 0)
    (hFour : normalizer (elementaryRepresentative 2 : Set Model) ≤ localFamily 2)
    (hE : normalizer (elementaryCandidate : Set Model) ≤ localFamily 1)
    (hCOne : centralizer (elementaryRepresentative 1 : Set Model) = elementaryCandidate)
    (hCThree : centralizer (elementaryRepresentative 3 : Set Model) = elementaryCandidate) :
    ∀ A : Subgroup Model, A ≤ sylowCandidate → A ≠ ⊥ →
      IsElementaryAbelian 2 A → ∃ (i : Fin 3) (g : Model),
        normalizer (A : Set Model) ≤ (localFamily i).map (MulAut.conj g).toMonoidHom :=
  elementary_normalizer_cover_of_fusion hfusion
    (representative_normalizer_bounds_of_local_calculations hC hFour hE hCOne hCThree)

/-- Every nontrivial elementary abelian two-subgroup of the fixed Sylow
candidate has its ambient normalizer in a conjugate of one of the three
fixed local candidates. Only the permitted numerical orders remain premises;
fusion and all ambient normalizer calculations are discharged. -/
public theorem elementary_normalizer_cover
    (hG : Nat.card Model = 50232960)
    (hS : Nat.card sylowCandidate = 128)
    (h0 : Nat.card (localFamily 0) = 1920) :
    ∀ A : Subgroup Model, A ≤ sylowCandidate → A ≠ ⊥ →
      IsElementaryAbelian 2 A → ∃ (i : Fin 3) (g : Model),
        normalizer (A : Set Model) ≤ (localFamily i).map (MulAut.conj g).toMonoidHom := by
  have hC := involution_centralizer_le_localFamily_zero hG h0
  exact elementary_normalizer_cover_of_fusion_and_local_calculations
    (elementary_fusion hS) hC
    (RepresentativeCalculations.normalizer_representative_two_le hS hC)
    (RepresentativeCalculations.normalizer_elementary_le hS hC)
    (RepresentativeCalculations.centralizer_representative_one_eq hS hC)
    (RepresentativeCalculations.centralizer_representative_three_eq hS hC)

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage
