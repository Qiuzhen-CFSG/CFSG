module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Stellmacher.Recognition.NormalEightExoticInnerStructure
public import Stellmacher.Recognition.NormalEightExoticOuterAlternatives
public import Theory.GroupTheory.PGroup.NormalAbelianIndexFour
public import Theory.GroupTheory.InvolutionCounting
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Theory.SpecificGroups.ExoticTwoGroup.Presentation

/-!
# Reduction of exotic Sylow recognition to the MacWilliams inputs

An elementary sixteen rules out a bound of three on Sylow involutions. The
N₂ hypothesis excludes a nonsolvable involution centralizer. Thus the
nontrivial-normalizer alternatives of JT 1.3 and 1.5, when supplied, force
the Sylow normalizer to induce only inner automorphisms.

For JT 1.4, the first two alternatives have normal abelian bases of index at
most four. The intrinsic theorem `four_lt_index_of_normal_abelian_of_elementary_sixteen`
excludes these bases using central omega of order two and the absence of a
normal elementary eight. The remaining alternative supplies the exotic
presentation, including the identification of the specified normal four.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.3–1.5, printed p.386, and
the final paragraph of p.395. The two structural alternatives are explicit
inputs below; their construction is still required for unconditional
recognition. Neither fusion nor presentation existence is assumed as an axiom.
-/

namespace Stellmacher.Recognition.NormalEightExoticRecognition

open Subgroup

/-- The involution-count and nonsolvable-centralizer alternatives are both
impossible in the presence of an elementary sixteen in an N₂ group. -/
public theorem false_of_outer_alternatives
    {G : Type*} [Group G] [Finite G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (W : Subgroup S) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16)
    (hcases : Nat.card {x : (S : Subgroup G) // orderOf x = 2} ≤ 3 ∨
      ∃ z : G, orderOf z = 2 ∧ ¬ Group.IsSolvable (centralizer ({z} : Set G))) :
    False := by
  rcases hcases with hcount | ⟨z, hz, hns⟩
  · have hBW : B ≤ W := by
      intro b hb
      by_cases hone : b = 1
      · exact hone ▸ W.one_mem
      · exact involution_mem_of_card_le (P := S) W
          (by simpa only [hW, Nat.reduceSub] using hcount) (x := b)
          (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian b hb) hone)
    have hc := card_le_of_le hBW
    omega
  · exact hns (hN _ (Theory.GroupTheory.isTwoLocal_involution_centralizer hz))

/-- Supplying JT 1.3 and 1.5 settles the normalizer alternative. -/
public theorem normalizer_eq_of_outer_alternatives
    {G : Type*} [Group G] [Finite G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (W : Subgroup S) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16)
    (houter : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G) →
      Nat.card {x : (S : Subgroup G) // orderOf x = 2} ≤ 3 ∨
        ∃ z : G, orderOf z = 2 ∧ ¬ Group.IsSolvable (centralizer ({z} : Set G))) :
    normalizer (S : Set G) = (S : Subgroup G) ⊔ centralizer (S : Set G) := by
  by_contra hne
  exact false_of_outer_alternatives hN S W hW B hB (houter hne)

/-- Discharge the abelian-base alternatives in JT 1.4. Recognition supplies
these alternatives; the elementary sixteen excludes bases of index at most four. -/
public theorem presentation_of_inner_alternatives
    {P : Type*} [Group P] [Finite P]
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W B : Subgroup P) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16)
    (hcases : (∃ D : Subgroup P, D.Normal ∧ IsMulCommutative D ∧ D.index ≤ 4) ∨
      ∃ d : ExoticTwoGroup.Presentation P,
        W = closure ({d.a ^ 2, d.b ^ 2} : Set P)) :
    ∃ d : ExoticTwoGroup.Presentation P,
      W = closure ({d.a ^ 2, d.b ^ 2} : Set P) := by
  rcases hcases with ⟨D, hDn, hDa, hDi⟩ | hexotic
  · let : D.Normal := hDn
    let : IsMulCommutative D := hDa
    have hlt := four_lt_index_of_normal_abelian_of_elementary_sixteen hZ hno B hB D
    omega
  · exact hexotic

/-- Final assembly after the two MacWilliams structural inputs are proved.
Fusion and the normal-image hypotheses belong to the construction of these
inputs, not to the intrinsic elimination of their non-exotic alternatives. -/
public theorem presentation_of_macwilliams_inputs
    {G : Type*} [Group G] [Finite G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16)
    (houter : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G) →
      Nat.card {x : (S : Subgroup G) // orderOf x = 2} ≤ 3 ∨
        ∃ z : G, orderOf z = 2 ∧ ¬ Group.IsSolvable (centralizer ({z} : Set G)))
    (hinner : normalizer (S : Set G) = (S : Subgroup G) ⊔ centralizer (S : Set G) →
      (∃ D : Subgroup S, D.Normal ∧ IsMulCommutative D ∧ D.index ≤ 4) ∨
        ∃ d : ExoticTwoGroup.Presentation S,
          W = closure ({d.a ^ 2, d.b ^ 2} : Set S)) :
    ∃ d : ExoticTwoGroup.Presentation S,
      W = closure ({d.a ^ 2, d.b ^ 2} : Set S) :=
  presentation_of_inner_alternatives hZ hno W B hB
    (hinner (normalizer_eq_of_outer_alternatives hN S W hW B hB houter))

/-- The marked central-omega-two configuration has the exotic Sylow
presentation.  If the Sylow normalizer induces only inner automorphisms, the
JT 1.4 alternatives are reduced by the inner-structure theorem.  Otherwise
the JT 1.3/1.5 alternatives contradict the elementary sixteen and the N₂
hypothesis. -/
public theorem exists_presentation
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A : Subgroup S) [IsElementaryAbelian 2 A]
    (_hA : 8 ≤ Nat.card A) (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧
      8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(NormalFourCentralOmegaTwo.fourImage S W).Normal]
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16)
    (hWB : W ≤ B) :
    ∃ d : ExoticTwoGroup.Presentation S,
      W = closure ({d.a ^ 2, d.b ^ 2} : Set S) := by
  by_cases hnorm : normalizer (S : Set G) =
      (S : Subgroup G) ⊔ centralizer (S : Set G)
  · exact NormalEightExoticInnerStructure.exists_presentation
      hns hN S hnonab hZ hno W hW hunique hfused B hB hWB hnorm
  · exact (false_of_outer_alternatives hN S W hW B hB
      (NormalEightExoticOuterAlternatives.outer_alternatives
        hns hN S hnonab hZ hno W hW hunique hfused B hB hWB hnorm)).elim

end Stellmacher.Recognition.NormalEightExoticRecognition
