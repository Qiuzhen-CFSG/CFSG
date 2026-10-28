module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Theory.SpecificGroups.BinaryLinear.NestedRadicals
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Recovering a binary flag from its two-core

For nonzero W ≤ U < V, the two-core of the common stabilizer fixes W
pointwise and has all displacements in U. Both elementary radicals lie in
this core. The radical at W recovers W as the common fixed space; the
radical at U expresses every vector of U as a displacement. Thus the
normalizer of the core is exactly the common stabilizer.

The action on W and the action on V/U are onto: lift an automorphism of
one block with identity on the complementary quotient or subspace. Their
normal two-group images vanish since binary general linear groups have
trivial two-core. This argument includes all three-block flags needed in
Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.25, printed
p.960 (PDF p.977). It does not assert containment in the two-residual.
-/

public section

open Subgroup
namespace BinaryLinear.CubicPairNormalizers
open SmallParabolicLevi
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem radical_left_le_core {W U : Submodule (ZMod 2) V} (hWU : W ≤ U) :
    radical W ≤ (parabolic W ⊓ parabolic U).pCoreIn 2 := by
  exact le_pCoreIn_of_normalizes (radical_two W)
    (le_inf (radical_le_parabolic W) (radical_le_nested_parabolic hWU))
    (inf_le_left.trans (parabolic_le_normalizer W))

private theorem radical_right_le_core {W U : Submodule (ZMod 2) V} (hWU : W ≤ U) :
    radical U ≤ (parabolic W ⊓ parabolic U).pCoreIn 2 := by
  exact le_pCoreIn_of_normalizes (radical_two U)
    (le_inf (radical_le_smaller_parabolic hWU) (radical_le_parabolic U))
    (inf_le_right.trans (parabolic_le_normalizer U))

private theorem left_action_surjective {W U : Submodule (ZMod 2) V} (hWU : W ≤ U) :
    Function.Surjective ((subspaceAction W).comp
      (inclusion (show parabolic W ⊓ parabolic U ≤ parabolic W from inf_le_left))) := by
  intro a
  obtain ⟨g, hg⟩ := blockAction_surjective W (a, 1)
  have hga : subspaceAction W g = a := congrArg Prod.fst hg
  have hgb : quotientAction W g = 1 := congrArg Prod.snd hg
  have hd (v : V) : g.val v - v ∈ W := by
    exact (Submodule.Quotient.eq W).mp (LinearEquiv.congr_fun hgb (W.mkQ v))
  have hgU : g.val ∈ parabolic U := by
    intro v
    constructor
    · intro hv
      have := U.sub_mem hv (hWU (hd v))
      simpa using this
    · intro hv
      have := U.add_mem (hWU (hd v)) hv
      simpa using this
  exact ⟨⟨g.val, g.property, hgU⟩, hga⟩

private theorem right_action_surjective {W U : Submodule (ZMod 2) V} (hWU : W ≤ U) :
    Function.Surjective ((quotientAction U).comp
      (inclusion (show parabolic W ⊓ parabolic U ≤ parabolic U from inf_le_right))) := by
  intro a
  obtain ⟨g, hg⟩ := blockAction_surjective U (1, a)
  have hga : subspaceAction U g = 1 := congrArg Prod.fst hg
  have hgb : quotientAction U g = a := congrArg Prod.snd hg
  have hf (hv : U) : g.val hv = hv :=
    congrArg Subtype.val (LinearEquiv.congr_fun hga hv)
  have hgW : g.val ∈ parabolic W := by
    intro v
    constructor
    · intro hv
      have he := hf ⟨g.val v, hWU hv⟩
      have he' : g.val v = v := g.val.injective he
      rwa [he'] at hv
    · intro hv
      change g.val v ∈ W
      rw [hf ⟨v, hWU hv⟩]
      exact hv
  exact ⟨⟨g.val, hgW, g.property⟩, hgb⟩

private theorem core_fixes [FiniteDimensional (ZMod 2) V]
    {W U : Submodule (ZMod 2) V} (hWU : W ≤ U)
    {g : GL V} (hg : g ∈ (parabolic W ⊓ parabolic U).pCoreIn 2)
    (w : V) (hw : w ∈ W) : g w = w := by
  let P := parabolic W ⊓ parabolic U
  let f : P →* GL W := (subspaceAction W).comp (inclusion inf_le_left)
  have hle : (pCore 2 P).map f ≤ pCore 2 (GL W) :=
    le_sSup ⟨Subgroup.Normal.map inferInstance f (left_action_surjective hWU),
      pCore_isPGroup.map f⟩
  rw [linearGroup_twoCore_eq_bot] at hle
  obtain ⟨x, hx, rfl⟩ := mem_map.mp hg
  have he : f x = 1 := hle (mem_map.mpr ⟨x, hx, rfl⟩)
  exact congrArg Subtype.val (LinearEquiv.congr_fun he ⟨w, hw⟩)

private theorem core_moves [FiniteDimensional (ZMod 2) V]
    {W U : Submodule (ZMod 2) V} (hWU : W ≤ U)
    {g : GL V} (hg : g ∈ (parabolic W ⊓ parabolic U).pCoreIn 2)
    (v : V) : g v - v ∈ U := by
  let P := parabolic W ⊓ parabolic U
  let f : P →* GL (V ⧸ U) := (quotientAction U).comp (inclusion inf_le_right)
  have hle : (pCore 2 P).map f ≤ pCore 2 (GL (V ⧸ U)) :=
    le_sSup ⟨Subgroup.Normal.map inferInstance f (right_action_surjective hWU),
      pCore_isPGroup.map f⟩
  rw [linearGroup_twoCore_eq_bot] at hle
  obtain ⟨x, hx, rfl⟩ := mem_map.mp hg
  have he : f x = 1 := hle (mem_map.mpr ⟨x, hx, rfl⟩)
  exact (Submodule.Quotient.eq U).mp (LinearEquiv.congr_fun he (U.mkQ v))

private theorem normalizer_le_parabolic_of_displacements
    (Q : Subgroup (GL V)) (U : Submodule (ZMod 2) V) (hU : U ≠ ⊤)
    (hr : radical U ≤ Q) (hd : ∀ q ∈ Q, ∀ v : V, q v - v ∈ U) :
    normalizer (Q : Set (GL V)) ≤ parabolic U := by
  obtain ⟨v, _, hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hU)
  obtain ⟨f, hfv, hf⟩ := U.exists_le_ker_of_notMem hv
  have hf1 : f v = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hfv
  have stable : ∀ g ∈ normalizer (Q : Set (GL V)), ∀ w ∈ U, g w ∈ U := by
    intro g hg w hw
    let t := transvection w f (hf hw)
    have ht : t ∈ Q := hr (transvection_mem hw hf)
    have hct : g * t * g⁻¹ ∈ Q := (hg t).mp ht
    have hm := hd _ hct (g v)
    change g (t (g.symm (g v))) - g v ∈ U at hm
    rw [LinearEquiv.symm_apply_apply] at hm
    change g (v + f v • w) - g v ∈ U at hm
    simpa only [hf1, one_smul, map_add, add_sub_cancel_left] using hm
  intro g hg w
  constructor
  · intro hw
    simpa only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using
      stable g⁻¹ ((normalizer (Q : Set (GL V))).inv_mem hg) (g w) hw
  · exact stable g hg w

/-- The two-core of a two-cut stabilizer recovers both flag spaces. -/
theorem normalizer_twoCore_nested [FiniteDimensional (ZMod 2) V]
    {W U : Submodule (ZMod 2) V} (hWU : W ≤ U) (hW : W ≠ ⊥) (hU : U ≠ ⊤) :
    normalizer ((parabolic W ⊓ parabolic U).pCoreIn 2 : Set (GL V)) =
      parabolic W ⊓ parabolic U := by
  let P := parabolic W ⊓ parabolic U
  have hfixed : fixedSpace (P.pCoreIn 2) = W := by
    apply le_antisymm
    · intro v hv
      exact (mem_iff_fixed_radical hW v).mpr
        (fun g hg => hv g (radical_left_le_core hWU hg))
    · intro v hv g hg
      exact core_fixes hWU hg v hv
  apply le_antisymm
  · apply le_inf
    · simpa only [hfixed] using normalizer_le_parabolic_fixedSpace (P.pCoreIn 2)
    · exact normalizer_le_parabolic_of_displacements (P.pCoreIn 2) U hU
        (radical_right_le_core hWU) (fun _ hg v => core_moves hWU hg v)
  · exact P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
end BinaryLinear.CubicPairNormalizers

end
