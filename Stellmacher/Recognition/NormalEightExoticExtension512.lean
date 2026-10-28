module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.GroupAction.C4SquareMaximalTwoAction
public import Theory.GroupTheory.PGroup.NormalFourCentralAction
public import Theory.GroupTheory.PGroup.C4SquareMaximalExtension

/-!
# The maximal C₄-square extension branch

For an order-512 Sylow group with a self-centralizing normal C₄-square D,
the conjugation image has order 32. Its central transvection fixes the omega
four and inverts only elements of square one. An involution lifting this
transvection therefore generates a normal elementary eight together
with the omega four.

The lift is supplied by the commuting-action obstruction in
`C4SquareMaximalExtension`. Thus the intrinsic hypotheses already exclude
this order, and the final theorem retains the full ambient branch interface.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.4 and the final paragraph of
printed p.395, in `refs/original/n-group-global/odd-core-rank-two-source/`.
-/

namespace Stellmacher.Recognition.NormalEightExoticExtension512

open Subgroup

variable {G : Type*} [Group G]

/-- The order-512 branch gives the maximal two-action on its abelian base. -/
public theorem card_conj_range_eq_thirty_two (S : Sylow 2 G)
    (D : Subgroup S) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set S) ≤ D)
    (hmodel : Nonempty (D ≃* C4SquareExtension.Model)) (hcard : Nat.card S = 512) :
    Nat.card (MulAut.conjNormal : S →* MulAut D).range = 32 := by
  have hD : Nat.card D = 16 := by
    obtain ⟨e⟩ := hmodel
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  have hi := D.card_mul_index
  rw [hD, hcard] at hi
  rw [← index_ker, conjNormal_ker_eq_of_selfCentralizing_abelian D hDC]
  omega

/-- There is a nontrivial central binary action in the order-512 branch. -/
public theorem exists_central_binary_action_of_card_eq_512 (S : Sylow 2 G)
    (D : Subgroup S) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set S) ≤ D)
    (hmodel : Nonempty (D ≃* C4SquareExtension.Model)) (hcard : Nat.card S = 512) :
    ∃ a : MulAut D, a ∈ (MulAut.conjNormal : S →* MulAut D).range ∧
      a ≠ 1 ∧ a ^ 2 = 1 ∧
      (∀ d : D, d ^ 2 = 1 → a d = d) ∧
      (∀ g : S, Commute (MulAut.conjNormal (H := D) g) a) ∧
      (∀ d : D, a d = d⁻¹ → d ^ 2 = 1) := by
  let f : S →* MulAut D := MulAut.conjNormal
  have hp : IsPGroup 2 f.range :=
    S.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨a, ha, hne, hsq, hfix, hcomm, hinv⟩ :=
    C4SquareExtension.exists_central_binary_action hmodel f.range hp
      (card_conj_range_eq_thirty_two S D hDC hmodel hcard)
  exact ⟨a, ha, hne, hsq, hfix, fun g => hcomm _ ⟨g, rfl⟩, hinv⟩

variable [Finite G]

/-- An involution lift of the central binary action contradicts absence of
normal elementary eights. This is the final assembly interface for the lift. -/
public theorem false_of_central_binary_action_lift (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W D : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    [D.Normal] [IsMulCommutative D]
    (hW : Nat.card W = 4) (hDC : centralizer (D : Set S) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W)
    (a : MulAut D) (hne : a ≠ 1)
    (hfix : ∀ d : D, d ^ 2 = 1 → a d = d)
    (hcomm : ∀ g : S, Commute (MulAut.conjNormal (H := D) g) a)
    (hinv : ∀ d : D, a d = d⁻¹ → d ^ 2 = 1)
    (x : S) (hx : x ^ 2 = 1) (hxa : MulAut.conjNormal (H := D) x = a) : False := by
  have hxD : x ∉ D := by
    intro hxD
    have hk : x ∈ (MulAut.conjNormal : S →* MulAut D).ker := by
      rwa [conjNormal_ker_eq_of_selfCentralizing_abelian D hDC]
    exact hne (hxa ▸ MonoidHom.mem_ker.mp hk)
  have hWD : W ≤ D := hDO ▸ map_subtype_le _
  have hxW : x ∈ centralizer (W : Set S) := by
    intro w hw
    let d : D := ⟨w, hWD hw⟩
    have hd : d ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian w hw)
    have hh := congrArg (fun d : D => (d : S)) (hfix d hd)
    rw [← hxa] at hh
    change x * w * x⁻¹ = w at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  apply hno
  apply exists_normal_eight_of_involution_central_action W D hW hDC hDO x hx hxD hxW
  · intro g
    rw [hxa]
    exact hcomm g
  · intro d hd hi
    have hh : a (⟨d, hd⟩ : D) = (⟨d, hd⟩ : D)⁻¹ := by
      rw [← hxa]
      exact Subtype.ext hi
    exact congrArg Subtype.val (hinv ⟨d, hd⟩ hh)


/-- Intrinsic exclusion of an order-512 group with the supplied normal four
and self-centralizing C₄-square base. -/
public theorem false_of_card_eq_512_intrinsic (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W D : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    [D.Normal] [IsMulCommutative D]
    (hW : Nat.card W = 4) (hDC : centralizer (D : Set S) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* C4SquareExtension.Model)) (hcard : Nat.card S = 512) :
    False := by
  obtain ⟨x, hx2, hxD, hfix, hcomm, hinv⟩ :=
    C4SquareExtension.exists_involution_central_binary_action S.isPGroup' D hDC hmodel
      (card_conj_range_eq_thirty_two S D hDC hmodel hcard)
  have hne : MulAut.conjNormal (H := D) x ≠ 1 := by
    intro h
    apply hxD
    rw [← conjNormal_ker_eq_of_selfCentralizing_abelian D hDC]
    exact MonoidHom.mem_ker.mpr h
  exact false_of_central_binary_action_lift S hno W D hW hDC hDO
    (MulAut.conjNormal (H := D) x) hne hfix hcomm hinv x hx2 rfl

set_option linter.unusedVariables false in
/-- The order-512 branch is impossible under the complete exotic-extension
hypotheses. The stronger intrinsic exclusion supplies the contradiction. -/
public theorem false_of_card_eq_512 [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G) (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(NormalFourCentralOmegaTwo.fourImage S W).Normal]
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (B : Subgroup S) [IsElementaryAbelian 2 B]
    (hB : Nat.card B = 16) (hWB : W ≤ B)
    (hnorm : normalizer (S : Set G) = (S : Subgroup G) ⊔ centralizer (S : Set G))
    (D : Subgroup S) [D.Normal] [IsMulCommutative D]
    (hWD : W ≤ D) (hDC : centralizer (D : Set S) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))))
    (hcard : Nat.card S = 512) : False :=
  false_of_card_eq_512_intrinsic S hno W D hW hDC hDO hmodel hcard

end Stellmacher.Recognition.NormalEightExoticExtension512
