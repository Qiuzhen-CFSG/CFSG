module

public import Theory.GroupTheory.PGroup.CentralInvolutionCoreOrder
public import Theory.GroupTheory.PGroup.CriticalSixteenAction
public import Stellmacher.Recognition.NormalEightExoticCriticalSixteen

/-!
# Numerical assembly for the central-two exotic Sylow branch

A critical subgroup of order sixteen, with center of order four and all
involutions central in that subgroup, gives a lower bound of 128 using the
supplied elementary sixteen. Its conjugation image of order at most 32
provides the matching upper bound.

The existence of this critical subgroup under the nontrivial Sylow
normalizer hypothesis, and the bound on its action image, are separate
structural inputs. This module currently assembles those inputs; it does
not assert the unconditional order theorem.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3, printed p.386,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`;
MacWilliams, DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace Stellmacher.Recognition.NormalEightExoticSylowOrder

open Subgroup

/-- The critical-sixteen construction and its action bound give the exact
order required by Hall–Janko recognition. -/
public theorem card_eq_128_of_critical_sixteen
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16)
    (C : Subgroup S) (hcrit : IsCriticalPSubgroup 2 C)
    (hC : Nat.card C = 16) (hCZ : Nat.card (center C) = 4)
    (hinv : ∀ x : C, x ^ 2 = 1 → x ∈ center C)
    (himage : letI : C.Characteristic := hcrit.characteristic
      Nat.card (MulAut.conjNormal : S →* MulAut C).range ≤ 32) :
    Nat.card S = 128 := by
  let : C.Characteristic := hcrit.characteristic
  have hlower := S.isPGroup'.card_ge_128_of_normal_sixteen hZ B hB C hC hCZ hinv
  have horder := hcrit.card_eq_center_card_mul_conj_image
  rw [hCZ] at horder
  omega

set_option linter.unusedVariables false in
/-- The central-two exotic normalizer branch has Sylow order `128`.

The structural critical-sixteen theorem supplies a core of order sixteen with
elementary center of order four.  The intrinsic action estimate bounds its
conjugation image by thirty-two, and the preceding numerical assembly gives
the claimed equality.  The ambient simplicity, nonsolvability, `N₂`, and
fusion hypotheses are retained because they are part of the recognition
interface; the local order calculation only uses the normalizer branch and
the central-two data.
-/
public theorem card_eq_128
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G)
    (hnorm : normalizer (S : Set G) ≠
      (S : Subgroup G) ⊔ centralizer (S : Set G))
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧
      8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(Stellmacher.Recognition.NormalFourCentralOmegaTwo.fourImage S W).Normal]
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 →
      orderOf v = 2 → IsConj (u : G) (v : G))
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) :
    Nat.card S = 128 := by
  obtain ⟨C, hcrit, hC, hCZ, hcenter, hinv⟩ :=
    NormalEightExoticCriticalSixteen.exists_critical_subgroup_order_sixteen
      S hnorm hZ hno W hW hunique B hB
  let : IsElementaryAbelian 2 (center C) := hcenter
  apply card_eq_128_of_critical_sixteen S hZ B hB C hcrit hC hCZ hinv
  exact IsCriticalPSubgroup.card_conjNormal_range_le_thirtytwo
    S.isPGroup' hcrit hC hCZ

end Stellmacher.Recognition.NormalEightExoticSylowOrder
