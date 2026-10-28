module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.FullAction.ActionImage
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.ElementaryEightPlaneFullRestriction

/-!
# The extraspecial hyperplane action in 14.4.8(2)

T normalizes VX. Its U-action forces the central line Z(U) into VX, since
VX has order eight. The fixed-space clause 12.8.11(4), used in its literal
pullback form, then forces the conjugate central line into VX as well.
Their join is V₂, so both extraspecial groups normalize VX.

Restrict the actual I₂ image on VX to the four-group V₂. The earlier action
has order six, and Wg gives a nontrivial restriction kernel. The elementary-eight
restriction theorem makes the image have order 24. It is the full hyperplane
stabilizer, and the escaping Y-member makes LXT induce every automorphism.

All displayed premises concern the earlier source configuration: extraspecial
centers and commutators; the centralizer, supplement and plane-action clauses
of 12.8.9; and the elementary/fixed-space clauses of 12.8.11. The outer source
assembly must supply them from Hypothesis 14.3.10. No action or component
conclusion from 14.4.8 is a premise. Component placement is separate.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
12.8.9--12, printed pp.852--855; 14.4.8(2), printed p.1009.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
variable {G : Type*} [Group G] [Finite G]

private theorem eq_line_of_nontrivial_le {K Z : Subgroup G}
    (hle : K ≤ Z) (hZ : Nat.card Z = 2) (hne : K ≠ ⊥) : K = Z := by
  apply eq_of_le_of_card_ge hle
  have hp : 0 < Nat.card K := Nat.card_pos
  have hk : Nat.card K ≠ 1 := fun he => hne (card_eq_one.mp he)
  omega

/-- The two central lines lie in VX. The fixed-space premise is the
pullback of 12.8.11(4): C_{E/Z(U)}(Wg) = V₂/Z(U). -/
theorem movedSpace_contains_central_lines
    {H T V₂ E X U Ug Z Zg Wg : Subgroup G}
    (hX : X ∈ YFamily H T V₂ E)
    (hTV₂ : T ≤ normalizer (V₂ : Set G))
    (hUT : U ≤ T) (hWgT : Wg ≤ T) (hWgUg : Wg ≤ Ug)
    (hE : E ≤ U ⊓ Ug)
    (hU : ⁅U,U⁆ ≤ Z) (hUg : ⁅Ug,Ug⁆ ≤ Zg)
    (hZU : U ⊓ centralizer (U : Set G) = Z)
    (hZ : Nat.card Z = 2) (hZg : Nat.card Zg = 2) (hV₂ : Nat.card V₂ = 4)
    (hfixed : ∀ D : Subgroup G, D ≤ E → ⁅D,Wg⁆ ≤ Z → D ≤ V₂) :
    Z ≤ movedSpace V₂ X ∧ Zg ≤ movedSpace V₂ X := by
  let W := movedSpace V₂ X
  have hTW : T ≤ normalizer (W : Set G) := sylow_normalizes_movedSpace hX.1 hTV₂
  have hWU : W ≤ U := hX.2.2.trans (hE.trans inf_le_left)
  have hWUg : W ≤ Ug := hX.2.2.trans (hE.trans inf_le_right)
  have hUW : ⁅W,U⁆ ≤ W := le_normalizer_iff_commutator_le_left.mp (hUT.trans hTW)
  have hWgW : ⁅W,Wg⁆ ≤ W := le_normalizer_iff_commutator_le_left.mp (hWgT.trans hTW)
  have hcommZ : ⁅W,U⁆ = Z := by
    apply eq_line_of_nontrivial_le ((commutator_mono hWU le_rfl).trans hU) hZ
    intro hb
    have hWZ : W ≤ Z := by
      rw [← hZU]
      exact le_inf hWU (commutator_eq_bot_iff_le_centralizer.mp hb)
    have hc := Nat.card_le_card_of_injective (inclusion hWZ) (inclusion_injective hWZ)
    rw [hX.2.1,hZ] at hc
    omega
  have hcommZg : ⁅W,Wg⁆ = Zg := by
    apply eq_line_of_nontrivial_le ((commutator_mono hWUg hWgUg).trans hUg) hZg
    intro hb
    have hWP := hfixed W hX.2.2 (hb ▸ bot_le)
    have hc := Nat.card_le_card_of_injective (inclusion hWP) (inclusion_injective hWP)
    rw [hX.2.1,hV₂] at hc
    omega
  exact ⟨hcommZ ▸ hUW,hcommZg ▸ hWgW⟩

/-- The source plane containment and the extraspecial normalization are
consequences of the earlier centralizer clause, rather than inputs about VX. -/
theorem movedSpace_plane_and_extraspecial_action
    {H T V₂ E X U Ug Z Zg Wg : Subgroup G}
    (hX : X ∈ YFamily H T V₂ E)
    (hTV₂ : T ≤ normalizer (V₂ : Set G))
    (hUT : U ≤ T) (hWgT : Wg ≤ T) (hWgUg : Wg ≤ Ug)
    (hE : E ≤ U ⊓ Ug)
    (hU : ⁅U,U⁆ ≤ Z) (hUg : ⁅Ug,Ug⁆ ≤ Zg)
    (hZU : U ⊓ centralizer (U : Set G) = Z)
    (hZ : Nat.card Z = 2) (hZg : Nat.card Zg = 2) (hV₂ : Nat.card V₂ = 4)
    (hplane : V₂ = Z ⊔ Zg)
    (hfixed : ∀ D : Subgroup G, D ≤ E → ⁅D,Wg⁆ ≤ Z → D ≤ V₂) :
    V₂ ≤ movedSpace V₂ X ∧
      U ⊔ Ug ≤ normalizer (movedSpace V₂ X : Set G) := by
  obtain ⟨hz,hzg⟩ := movedSpace_contains_central_lines hX hTV₂ hUT hWgT hWgUg
    hE hU hUg hZU hZ hZg hV₂ hfixed
  exact ⟨hplane.le.trans (sup_le hz hzg),
    extraspecial_join_normalizes_movedSpace U Ug Z Zg V₂ X hU hUg hz hzg
      (hX.2.2.trans hE)⟩

/-- The earlier six-element action on V₂ and a nontrivial Wg-transvection
force the image on VX to have order 24. The restriction is the actual action. -/
theorem I₂_image_card_of_plane_restriction
    {I₂ V₂ W Wg : Subgroup G} [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 8) (hV₂ : Nat.card V₂ = 4) (hVW : V₂ ≤ W)
    (hIW : I₂ ≤ normalizer (W : Set G))
    (hIP : I₂ ≤ normalizer (V₂ : Set G))
    (hWgI : Wg ≤ I₂) (hWgP : Wg ≤ centralizer (V₂ : Set G))
    (hmove : ⁅W,Wg⁆ ≠ ⊥)
    (hSix : Nat.card (conjugation I₂ V₂ hIP).range = 6) :
    Nat.card (conjugation I₂ W hIW).range = 24 := by
  let f := conjugation I₂ W hIW
  let fp := conjugation I₂ V₂ hIP
  let D := V₂.subgroupOf W
  let J := f.range
  have hstable : J ≤ automorphismPairStabilizer D D := by
    rintro a ⟨i,rfl⟩
    rw [mem_automorphismPairStabilizer_iff]
    have hi : ∀ w : W, f i w ∈ D ↔ w ∈ D := by
      intro w
      change (conjugation I₂ W hIW i w : G) ∈ V₂ ↔ (w : G) ∈ V₂
      rw [conjugation_apply]
      exact (mem_normalizer_iff.mp (hIP i.property) w).symm
    exact ⟨hi,hi⟩
  let r : J →* MulAut D := (pairRestriction D D).comp (inclusion hstable)
  let e : D ≃* V₂ := subgroupOfEquivOfLe hVW
  have hcomp (i : I₂) : MulAut.congr e (r (f.rangeRestrict i)) = fp i := by
    ext v
    change (conjugation I₂ W hIW i ⟨v,hVW v.property⟩ : G) =
      (conjugation I₂ V₂ hIP i v : G)
    rw [conjugation_apply,conjugation_apply]
  have hmap : r.range.map (MulAut.congr e).toMonoidHom = fp.range := by
    ext a
    constructor
    · rintro ⟨b,⟨j,rfl⟩,rfl⟩
      obtain ⟨i,rfl⟩ := f.rangeRestrict_surjective j
      exact ⟨i,(hcomp i).symm⟩
    · rintro ⟨i,rfl⟩
      exact ⟨r (f.rangeRestrict i),⟨f.rangeRestrict i,rfl⟩,hcomp i⟩
  have hrange : Nat.card r.range = 6 := by
    rw [Nat.card_congr (r.range.equivMapOfInjective (MulAut.congr e).toMonoidHom
      (MulAut.congr e).injective).toEquiv,hmap]
    exact hSix
  have hker : r.ker ≠ ⊥ := by
    intro hb
    apply hmove
    rw [commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro a ha
    let i : I₂ := ⟨a,hWgI ha⟩
    have hfp : fp i = 1 := by
      change i ∈ fp.ker
      rw [conjugation_ker]
      exact hWgP ha
    have hr : r (f.rangeRestrict i) = 1 := by
      apply (MulAut.congr e).injective
      rw [map_one,hcomp,hfp]
    have hj : f.rangeRestrict i = 1 := by
      have hm : f.rangeRestrict i ∈ r.ker := hr
      rwa [hb,mem_bot] at hm
    have hf : f i = 1 := congrArg Subtype.val hj
    have hi : i ∈ (conjugation I₂ W hIW).ker := hf
    rw [conjugation_ker] at hi
    exact hi
  exact elementaryEight_plane_card_twentyfour_of_full_restriction hW D
    (by rw [Nat.card_congr e.toEquiv]; exact hV₂) J r (fun _ _ => rfl) hrange hker

/-- The action part of 14.4.8(2), from the precise earlier 12.8 clauses.
`hfixed` is 12.8.11(4) in pullback form, `hSix` is the actual plane action
in 12.8.9(1--2), and `hI` is its residual supplement identity. -/
theorem full_conjugation_of_earlier_extraspecial_data
    {H T V₂ E X U Ug Z Zg Wg L₂ : Subgroup G} [IsElementaryAbelian 2 E]
    (hX : X ∈ YFamily H T V₂ E)
    (hTV₂ : T ≤ normalizer (V₂ : Set G))
    (hUT : U ≤ T) (hWgT : Wg ≤ T) (hWgUg : Wg ≤ Ug)
    (hE : E ≤ U ⊓ Ug)
    (hU : ⁅U,U⁆ ≤ Z) (hUg : ⁅Ug,Ug⁆ ≤ Zg)
    (hZU : U ⊓ centralizer (U : Set G) = Z)
    (hZ : Nat.card Z = 2) (hZg : Nat.card Zg = 2) (hV₂ : Nat.card V₂ = 4)
    (hplane : V₂ = Z ⊔ Zg)
    (hfixed : ∀ D : Subgroup G, D ≤ E → ⁅D,Wg⁆ ≤ Z → D ≤ V₂)
    (hI : U ⊔ Ug = L₂ ⊔ U)
    (hIP : U ⊔ Ug ≤ normalizer (V₂ : Set G))
    (hSix : Nat.card (conjugation (U ⊔ Ug) V₂ hIP).range = 6)
    (hWgP : Wg ≤ centralizer (V₂ : Set G)) :
    V₂ ≤ movedSpace V₂ X ∧
      ∃ hIW : U ⊔ Ug ≤ normalizer (movedSpace V₂ X : Set G),
        (conjugation (U ⊔ Ug) (movedSpace V₂ X) hIW).range =
          MulAction.stabilizer (MulAut (movedSpace V₂ X))
            (V₂.subgroupOf (movedSpace V₂ X)) ∧
        IsCoatom (conjugation (U ⊔ Ug) (movedSpace V₂ X) hIW).range ∧
        ∃ hAW : localJoin L₂ X ⊔ T ≤ normalizer (movedSpace V₂ X : Set G),
          Function.Surjective
            (conjugation (localJoin L₂ X ⊔ T) (movedSpace V₂ X) hAW) := by
  let : IsElementaryAbelian 2 (movedSpace V₂ X) := IsElementaryAbelian.of_le hX.2.2
  obtain ⟨hVW,hIW⟩ := movedSpace_plane_and_extraspecial_action hX hTV₂ hUT hWgT hWgUg
    hE hU hUg hZU hZ hZg hV₂ hplane hfixed
  have hmove : ⁅movedSpace V₂ X,Wg⁆ ≠ ⊥ := by
    intro hb
    have hp := hfixed (movedSpace V₂ X) hX.2.2 (hb ▸ bot_le)
    have hc := Nat.card_le_card_of_injective (inclusion hp) (inclusion_injective hp)
    rw [hX.2.1,hV₂] at hc
    omega
  have hi := I₂_image_card_of_plane_restriction hX.2.1 hV₂ hVW hIW hIP
    (hWgUg.trans le_sup_right) hWgP hmove hSix
  obtain ⟨he,hmax⟩ := I₂_image_eq_plane_stabilizer hX hV₂ hVW hIP hIW hi
  have hAW := localJoin_normalizes_movedSpace hX.1 hTV₂ hI hUT hIW
  exact ⟨hVW,hIW,he,hmax,hAW,
    localJoin_action_surjective_of_I₂_image hX hV₂ hVW hI hUT hIP hIW hAW hi⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
