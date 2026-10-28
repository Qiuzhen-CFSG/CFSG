module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Family
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Quotients
public import Theory.ElementaryAbelian.ExtraspecialNormalCommutator

/-!
# Lifting the natural tensor commutator calculation

The map `tilde` is the literal projection to U/Z(U). The earlier source bound
[Wᵍ,W]≤E bounds the constituent commutator after its preimage is placed in W.
T-invariance and extraspecial normal-subgroup theory put the central line
inside every nontrivial moved subgroup, supplying the factor two in its order.

Source: Aschbacher–Smith, Lemma 14.4.10, printed pp.1010–1011, using
12.8.11(1). The model plane and root calculations are separate inputs here;
these conditional transports do not assert the full source theorem.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural
variable {G : Type*} [Group G]

/-- The literal image in U/Z(U), as distinct from the actor image H/O₂(H). -/
def tilde (U A : Subgroup G) : Subgroup (U ⧸ center U) :=
  (A.subgroupOf U).map (QuotientGroup.mk' (center U))

/-- A quotient containment lifts when the actual target contains the central
kernel. No ambient normality of E is required. -/
theorem le_of_tilde_le {U A E : Subgroup G} (hAU : A ≤ U)
    (hZE : center U ≤ E.subgroupOf U) (h : tilde U A ≤ tilde U E) : A ≤ E := by
  have hh := (map_le_iff_le_comap.mp h)
  rw [tilde, comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hZE] at hh
  intro a ha
  exact hh (show (⟨a, hAU ha⟩ : U) ∈ A.subgroupOf U from ha)

/-- The commutator bound in 12.8.11(1), restricted to the constituent's full
preimage, gives the required bound in the central quotient. -/
theorem constituent_commutator_tilde_le {U D W Wg E : Subgroup G}
    (hDW : D ≤ W) (hsource : ⁅Wg, W⁆ ≤ E) :
    tilde U ⁅D, Wg⁆ ≤ tilde U E := by
  apply map_mono
  apply subgroupOf_mono
  exact (commutator_mono hDW le_rfl).trans ((commutator_comm W Wg).trans_le hsource)

/-- An actor preserving a hyperplane has trivial action on its order-two
quotient. This proves the source inclusion [Ũ,x]≤W̃ without assuming it. -/
theorem commutator_le_of_invariant_index_two {U W A : Subgroup G}
    (hindex : W.relIndex U = 2)
    (hAU : A ≤ normalizer (U : Set G)) (hAW : A ≤ normalizer (W : Set G)) :
    ⁅U, A⁆ ≤ W := by
  apply commutator_le.mpr
  intro u hu a ha
  let uU : U := ⟨u, hu⟩
  let vU : U := ⟨a * u⁻¹ * a⁻¹,
    le_normalizer_iff.mp hAU a ha _ (U.inv_mem hu)⟩
  have he : uU ∈ W.subgroupOf U ↔ vU ∈ W.subgroupOf U := by
    change u ∈ W ↔ a * u⁻¹ * a⁻¹ ∈ W
    rw [← (mem_normalizer_iff.mp (hAW ha) u⁻¹), inv_mem_iff]
  have hm := (mul_mem_iff_of_index_two hindex).mpr he
  change u * (a * u⁻¹ * a⁻¹) ∈ W at hm
  simpa only [commutatorElement_def, mul_assoc] using hm

/-- The full preimage of the selected constituent lies in W once its image
is [Ũ,x] and x preserves the actual hyperplane W. -/
theorem constituent_le_of_invariant_hyperplane {U D W A : Subgroup G}
    (hDU : D ≤ U) (hZW : center U ≤ W.subgroupOf U)
    (hD : tilde U D = tilde U ⁅U, A⁆) (hindex : W.relIndex U = 2)
    (hAU : A ≤ normalizer (U : Set G)) (hAW : A ≤ normalizer (W : Set G)) :
    D ≤ W := by
  apply le_of_tilde_le hDU hZW
  rw [hD]
  exact map_mono (subgroupOf_mono U (commutator_le_of_invariant_index_two hindex hAU hAW))

/-- Source normalization supplies the missing central factor in the order
calculation. In particular a quotient plane is not by itself counted as E₈. -/
theorem movedSpace_card_of_tilde [Finite G]
    {H T U V₂ X : Subgroup G} [IsExtraspecial 2 U]
    (hX : X ∈ XFamily H T) (hUT : U ≤ T)
    (hHU : H ≤ normalizer (U : Set G)) (hVU : V₂ ≤ U)
    (hZV : center U ≤ V₂.subgroupOf U) (hne : tilde U (movedSpace V₂ X) ≠ ⊥) :
    Nat.card (movedSpace V₂ X) = 2 * Nat.card (tilde U (movedSpace V₂ X)) := by
  have hMU : movedSpace V₂ X ≤ U :=
    (commutator_mono hVU le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hX.le_H.trans hHU))
  have hZM := extraspecial_center_le_commutator_of_image_ne_bot U V₂ X hVU hZV
    (hUT.trans hX.T_normalizes) (QuotientGroup.mk' (center U)) hne
  have hh := relIndex_mul_relIndex (⊥ : Subgroup U) (center U)
    ((movedSpace V₂ X).subgroupOf U) bot_le hZM
  rw [relIndex_bot_left, relIndex_bot_left,
    ← QuotientGroup.ker_mk' (center U), relIndex_ker,
    QuotientGroup.ker_mk', IsExtraspecial.center_order_p 2 U] at hh
  rw [Nat.card_congr (subgroupOfEquivOfLe hMU).toEquiv] at hh
  exact hh.symm

/-- Application to the literal X₂: a calculated quotient plane lying in
[Ũ₁,Wᵍ] yields an actual member of Y, using precisely [Wᵍ,W]≤E. -/
theorem second_mem_Y_of_tilde_plane [Finite G]
    {H T U V₂ E D W Wg : Subgroup G} [IsExtraspecial 2 U]
    (hX : second H T ∈ XFamily H T) (hUT : U ≤ T)
    (hHU : H ≤ normalizer (U : Set G)) (hVU : V₂ ≤ U)
    (hZV : center U ≤ V₂.subgroupOf U) (hZE : center U ≤ E.subgroupOf U)
    (hcard : Nat.card (tilde U (movedSpace V₂ (second H T))) = 4)
    (hline : tilde U (movedSpace V₂ (second H T)) ≤ tilde U ⁅D, Wg⁆)
    (hDW : D ≤ W) (hsource : ⁅Wg, W⁆ ≤ E) :
    second H T ∈ YFamily H T V₂ E := by
  refine ⟨hX, ?_, ?_⟩
  · have hn : tilde U (movedSpace V₂ (second H T)) ≠ ⊥ := by
      intro hb
      rw [hb, card_bot] at hcard
      omega
    rw [movedSpace_card_of_tilde hX hUT hHU hVU hZV hn, hcard]
  · apply le_of_tilde_le
      ((commutator_mono hVU le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hX.le_H.trans hHU))) hZE
    exact hline.trans (constituent_commutator_tilde_le hDW hsource)

/-- The common two-member family and the natural second-member calculation
exhaust Y in the literal ambient subgroup lattice. -/
theorem families_eq_of_second_mem_Y {H T V₂ E : Subgroup G}
    (hpair : XFamily H T = {first H, second H T})
    (hfirst : first H ∈ YFamily H T V₂ E)
    (hsecond : second H T ∈ YFamily H T V₂ E) :
    XFamily H T = YFamily H T V₂ E := by
  ext X
  constructor
  · intro hX
    rw [hpair] at hX
    rcases Set.mem_insert_iff.mp hX with rfl | hX
    · exact hfirst
    · have he := Set.mem_singleton_iff.mp hX
      simpa only [he] using hsecond
  · exact fun hX => hX.1
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural
