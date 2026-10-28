module

public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedReduction
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedFixedWeight.Coordinates
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedFixedWeight.BlockAction
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedFixedWeight.BlockGeometry

/-!
# Connected G₂ centralizers with a nonconstant fixed weight

The literal Weyl automorphisms send every torus element with `l = 1`,
`m = 1`, or `l = m` to `torus 1 a`. For nonidentity elements, `a ≠ 1`.
Algebraic conjugation transfers connectedness back to the original
centralizer. The imported coordinate theorem reconstructs the normalized
centralizer from its invertible two-dimensional block. Every such block is
realized by an actual octonion automorphism, and the resulting regular
surjection from `SL₂ × Gₘ` proves connectedness of the normalized centralizer.

The unconditional result holds over every algebraically closed field of
characteristic two, with no restriction on the order of the nonidentity
parameter. In particular it includes parameters of order three and applies
over the algebraic closure of every finite field of characteristic two.

Source: Steinberg, 8.1/8.5 and 12.5,
`refs/KGroup/GLS3/Chapter2St2.tex`; GLS III, Sections 2.1 and 2.8,
`refs/KGroup/GLS3/chapter2.tex`. The Weyl maps use the licensed ATLAS
coordinate convention; see `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`.
-/

public section

open Theory.AlgebraicGroup
namespace Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang
variable {K : Type*} [Field K]

private theorem fixedWeight_conjR (l m : Kˣ) :
    IsConj (torus l m) (torus l (l * m⁻¹)) := by
  apply isConj_iff.mpr
  refine ⟨weylR, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;>
    simp [weylR, weylREquiv, weylRLinear, weylRApply,
      torus, torusEquiv, torusLinear, torusWeights]
  all_goals field_simp
  all_goals simp

private theorem fixedWeight_conjS (l m : Kˣ) :
    IsConj (torus l m) (torus m l) := by
  apply isConj_iff.mpr
  refine ⟨weylS, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;>
    simp [weylS, weylSEquiv, weylSLinear, weylSApply,
      torus, torusEquiv, torusLinear, torusWeights]
  all_goals field_simp
  all_goals simp

/-- The three fixed-weight cases have the same normalized torus form. -/
theorem exists_fixedWeight_normal_form (l m : Kˣ) (hne : torus l m ≠ 1)
    (hfixed : l = 1 ∨ m = 1 ∨ l = m) :
    ∃ a : Kˣ, a ≠ 1 ∧ IsConj (torus l m) (torus 1 a) := by
  have hone : torus (1 : Kˣ) 1 = 1 := torusHom.map_one
  have reduce (a : Kˣ) (hc : IsConj (torus l m) (torus 1 a)) : a ≠ 1 := by
    intro ha
    rw [ha, hone] at hc
    exact hne (isConj_one_right.mp hc.symm)
  rcases hfixed with hl | hm | he
  · subst l
    exact ⟨m, reduce m (IsConj.refl _), IsConj.refl _⟩
  · subst m
    exact ⟨l, reduce l (fixedWeight_conjS l 1), fixedWeight_conjS l 1⟩
  · subst m
    have hc : IsConj (torus l l) (torus 1 l) := by
      have hR : IsConj (torus l l) (torus l 1) := by
        simpa using fixedWeight_conjR l l
      exact hR.trans (fixedWeight_conjS l 1)
    exact ⟨l, reduce l hc, hc⟩

/-- Connectedness in the normalized case suffices for all nonconstant fixed weights. -/
theorem centralizer_connected_fixed_weight_of_normalized [IsAlgClosed K]
    (hnormalized : ∀ a : Kˣ, a ≠ 1 →
      Variety.IsConnected (centralizerVariety (torus 1 a)))
    (l m : Kˣ) (hne : torus l m ≠ 1) (hfixed : l = 1 ∨ m = 1 ∨ l = m) :
    Variety.IsConnected (centralizerVariety (torus l m)) := by
  obtain ⟨a, ha, hc⟩ := exists_fixedWeight_normal_form l m hne hfixed
  exact centralizer_connected_of_isConj hc (hnormalized a ha)

/-- The centralizer of `torus 1 a` is connected for every nonidentity parameter
over an algebraically closed field of characteristic two. -/
theorem centralizer_connected_normalized [CharP K 2] [IsAlgClosed K]
    (a : Kˣ) (ha : a ≠ 1) :
    Variety.IsConnected (centralizerVariety (torus 1 a)) := by
  exact centralizer_connected_normalized_of_block_action
    FixedWeight.exists_block_automorphism a ha

/-- Every nonidentity torus element with a nonconstant fixed octonion weight
has connected centralizer in the actual closed octonion-automorphism model. -/
theorem centralizer_connected_fixed_weight [CharP K 2] [IsAlgClosed K]
    (l m : Kˣ) (hne : torus l m ≠ 1) (hfixed : l = 1 ∨ m = 1 ∨ l = m) :
    Variety.IsConnected (centralizerVariety (torus l m)) := by
  exact centralizer_connected_fixed_weight_of_normalized
    centralizer_connected_normalized l m hne hfixed

end Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang
