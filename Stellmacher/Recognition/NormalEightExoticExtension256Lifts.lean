module

public import Stellmacher.Recognition.NormalEightExoticExtension256Setup
public import Theory.GroupTheory.PGroup.C4SquareCentralizerFrattini
public import Theory.GroupTheory.PGroup.NormalEightCentralizerFusion
public import Theory.SpecificGroups.ExoticTwoGroup.LiftSwapCompletion
public import Theory.SpecificGroups.ExoticTwoGroup.LiftInversionNondegenerate
public import Theory.SpecificGroups.ExoticTwoGroup.LiftInversionNormalization
public import Theory.SpecificGroups.ExoticTwoGroup.LiftInversionSquare

/-!
# Lift correction for the order-256 extension

After normalizing the inversion lift, the basis-swap lift can be made an
involution without changing the inversion relations. Commutation of these
lifts and the swap action on the first inner generator then suffice for the
exact exotic presentation; the action on the second generator follows.

The remaining structural obligations are that the inversion square is one
and its first inner-generator commutator lies outside W. From these two facts,
the inversion basis and every swap relation can be normalized intrinsically,
with the inner generators remaining in the specified B.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.4(c), printed p.386,
applied on p.395.
-/

open Subgroup

namespace Stellmacher.Recognition.NormalEightExoticExtension256

/-- Once the inversion relations hold, the swap square can be normalized
using only the self-centralizing C₄-square base. -/
public theorem exists_involutory_swap_frame
    {P : Type*} [Group P] (D W B : Subgroup P)
    [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hmodel : Nonempty (D ≃* C4SquareExtension.Model))
    (f : ExoticTwoGroup.ActionFrame D W B) (hz : f.InversionRelations) :
    ∃ f' : ExoticTwoGroup.ActionFrame D W B,
      f'.InversionRelations ∧ f'.t ^ 2 = 1 := by
  obtain ⟨e⟩ := hmodel
  have hD : Nat.card D = 16 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  exact f.exists_involutory_t_frame hDC hD hz

/-- Assemble the marked presentation from the inversion stage and the
three independent swap relations. -/
public theorem exists_presentation_of_inversion_and_swap
    {P : Type*} [Group P] {D W B : Subgroup P}
    (f : ExoticTwoGroup.ActionFrame D W B) (hz : f.InversionRelations)
    (ht : f.t ^ 2 = 1) (htz : Commute f.t f.z₀)
    (htg : f.t * f.g₁ * f.t⁻¹ = f.g₂) (hcard : Nat.card P = 256) :
    ∃ d : ExoticTwoGroup.Presentation P,
      W = closure ({d.a ^ 2, d.b ^ 2} : Set P) :=
  f.exists_presentation (f.liftRelations_of_inversion_and_swap hz ht htz htg) hcard

/-- Once inversion is normalized, all swap corrections and the exact marked
presentation follow from the self-centralizing base and W ≤ B. -/
public theorem exists_presentation_of_inversion
    {P : Type*} [Group P] {D W B : Subgroup P}
    [D.Normal] [IsMulCommutative D] [IsMulCommutative B]
    (hDC : centralizer (D : Set P) ≤ D)
    (hmodel : Nonempty (D ≃* C4SquareExtension.Model)) (hWB : W ≤ B)
    (f : ExoticTwoGroup.ActionFrame D W B) (hz : f.InversionRelations)
    (hcard : Nat.card P = 256) :
    ∃ d : ExoticTwoGroup.Presentation P,
      W = closure ({d.a ^ 2, d.b ^ 2} : Set P) := by
  obtain ⟨e⟩ := hmodel
  have hD : Nat.card D = 16 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  obtain ⟨f', hf'⟩ := f.exists_liftRelations_of_inversion hDC hD hWB hz
  exact f'.exists_presentation hf' hcard

/-- The complete algebraic lift stage. The two remaining structural inputs
are the inversion square and nondegeneracy of its first commutator modulo W. -/
public theorem exists_presentation_of_inversion_square_and_commutator
    {P : Type*} [Group P] {D W B : Subgroup P}
    [D.Normal] [IsMulCommutative D] [IsMulCommutative B]
    (hDC : centralizer (D : Set P) ≤ D)
    (hmodel : Nonempty (D ≃* C4SquareExtension.Model)) (hWB : W ≤ B)
    (f : ExoticTwoGroup.ActionFrame D W B) (hz : f.z₀ ^ 2 = 1)
    (hn : f.z₀ * f.g₁ * f.z₀⁻¹ * f.g₁⁻¹ ∉ W) (hcard : Nat.card P = 256) :
    ∃ d : ExoticTwoGroup.Presentation P,
      W = closure ({d.a ^ 2, d.b ^ 2} : Set P) := by
  have hD : Nat.card D = 16 := by
    obtain ⟨e⟩ := hmodel
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  obtain ⟨f', hf'⟩ := f.exists_inversionRelations_of_square_and_commutator hDC hD hz hn
  exact exists_presentation_of_inversion hDC hmodel hWB f' hf' hcard

/-- The ambient order-256 hypotheses supply the two structural inputs needed by
the lift correction.  The centralizer fusion gives transitivity on the marked
four, the Frattini identification forces the inversion lift to square to one,
and the same identification excludes a degenerate inversion commutator. -/
public theorem exists_presentation_of_ambient
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hcard : Nat.card S = 256)
    (hZ : Nat.card (omega₁ (Subgroup.center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧
      8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (D B : Subgroup S) [D.Normal] [IsMulCommutative D]
    [IsElementaryAbelian 2 B]
    (hWD : W ≤ D) (hWB : W ≤ B)
    (hDC : Subgroup.centralizer (D : Set S) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* C4SquareExtension.Model))
    (f : ExoticTwoGroup.ActionFrame D W B) :
    ∃ d : ExoticTwoGroup.Presentation S,
      W = Subgroup.closure ({d.a ^ 2, d.b ^ 2} : Set S) := by
  have htrans : ∀ x y : Subgroup.centralizer (W : Set S),
      (x : S) ∈ W → (y : S) ∈ W → orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut (Subgroup.centralizer (W : Set S)), a x = y := by
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
      (G := omega₁ (Subgroup.center S) (p := 2)) 2 (by rw [hZ])
    have hzS : orderOf ((z : Subgroup.center S) : S) = 2 := by
      simpa only [orderOf_coe] using hz
    apply S.centralizer_four_automorphism_transitive_of_no_normal_eight
      hno hZ W hW hunique ((z : Subgroup.center S) : S) hzS
        (z : Subgroup.center S).property
    intro x y hx hy
    apply hfused x y x.property y.property
    · exact orderOf_eq_prime
        (elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : S) x.property)
        (fun h => hx (Subtype.ext h))
    · exact orderOf_eq_prime
        (elemPow_eq_one_of_isElementaryAbelian (p := 2) (y : S) y.property)
        (fun h => hy (Subtype.ext h))
  have hD : Nat.card D = 16 := by
    obtain ⟨e⟩ := hmodel
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  have hPhi : D = (frattini (Subgroup.centralizer (W : Set S))).map
      (Subgroup.centralizer (W : Set S)).subtype :=
    C4SquareExtension.base_eq_frattini_centralizer S.isPGroup' hcard hZ hno W hW
      htrans D hWD hDC hDO hmodel
  have hz : f.z₀ ^ 2 = 1 :=
    f.z_sq_eq_one_of_frattini hW hWD hDC hDO htrans hPhi
  have hn : f.z₀ * f.g₁ * f.z₀⁻¹ * f.g₁⁻¹ ∉ W :=
    f.inversion_commutator_not_mem_four_of_frattini S.isPGroup' hD hW hWD hWB
      hDC hDO hPhi
  exact exists_presentation_of_inversion_square_and_commutator hDC hmodel hWB f hz hn hcard

end Stellmacher.Recognition.NormalEightExoticExtension256
