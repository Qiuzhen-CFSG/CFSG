module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Basic
public import Theory.Representation.BinaryOffender.Defs
public import Theory.Alternating.theorem_5_2_1_2

/-!
# The outer-related marked natural actions of degree six

The canonical syntheme occurs in exactly pentads 2 and 4. Relabeling the
pentad action by `(2 5)` therefore sends its stabilizer `H2` to the duad
stabilizer `H1`. The embedded two-residual maps to the corrected subgroup
`K = A₄`, and the twisted action fixes the nonzero duad vector `{4,5}`.
Two within-pair transpositions have second displacement equal to that same
nonzero vector, proving that their distinguished rank-three group is not
quadratic on the twisted action.

Source: Aschbacher–Smith, Lemma 13.8.26, printed pp.962–963, and B.3.4,
printed pp.84–85. The automorphism is the actual pentad construction of
`GLS3.Chapter5.outerAut`; linear self-duality is not used for this comparison.
-/

@[expose] public section

open BinaryPermutation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open GLS3.Chapter5
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Marked

abbrev relabel : Symmetric := Equiv.swap 2 5
noncomputable def outer : MulAut Symmetric := outerAut.trans (MulAut.conj relabel)

theorem outer_apply (g : Symmetric) : outer g = relabel * outerHom g * relabel⁻¹ := rfl

private theorem base_mem_pentad (i : Fin 6) :
    baseSyntheme ∈ pentadAt i ↔ i = 2 ∨ i = 4 := by
  fin_cases i <;> decide

private theorem outerHom_preserves_base_pair {g : Symmetric} (hg : g ∈ H2)
    {i : Fin 6} (hi : i = 2 ∨ i = 4) : outerHom g i = 2 ∨ outerHom g i = 4 := by
  apply (base_mem_pentad _).mp
  change baseSyntheme ∈ pentadAt (outerAct g i)
  rw [outerAct_spec]
  have he : baseSyntheme.image (fun t => t.image g) = baseSyntheme := hg
  have hmem := (base_mem_pentad i).mpr hi
  change baseSyntheme ∈ (pentadEquiv g) (pentadAt i)
  simp only [pentadEquiv, Equiv.finsetCongr_apply]
  exact Finset.mem_map.mpr ⟨baseSyntheme, hmem, by
    change g.finsetCongr.finsetCongr baseSyntheme = baseSyntheme
    rw [Equiv.finsetCongr_apply, Finset.map_eq_image]
    convert he using 1
    congr 1
    funext t
    exact Finset.map_eq_image _ _⟩

private theorem outer_H2_le : H2.map outer.toMonoidHom ≤ H1 := by
  rintro _ ⟨g, hg, rfl⟩
  have h2 := outerHom_preserves_base_pair (i := 2) hg (Or.inl rfl)
  have h4 := outerHom_preserves_base_pair (i := 4) hg (Or.inr rfl)
  have hn : outerHom g 2 ≠ outerHom g 4 := (outerHom g).injective.ne (by decide)
  change (pair 4 5).image (outer g) = pair 4 5
  rcases h2 with h2 | h2 <;> rcases h4 with h4 | h4
  all_goals try exact False.elim (hn (h2.trans h4.symm))
  all_goals change outerAct g 2 = _ at h2
  all_goals change outerAct g 4 = _ at h4
  all_goals simp only [pair, Finset.image_insert, Finset.image_singleton]
  all_goals change {relabel (outerAct g 4), relabel (outerAct g 2)} = {4, 5}
  all_goals rw [h2, h4]
  all_goals decide

private theorem H1_card : Nat.card H1 = 48 := by
  let g : Symmetric := Equiv.swap 0 4 * Equiv.swap 1 5
  have he : pair 4 5 = g • pair 0 1 := by decide
  exact (Nat.card_congr (MulAction.stabilizerEquivStabilizer he).toEquiv).symm.trans
    duadStabilizer_order

theorem outer_H2 : H2.map outer.toMonoidHom = H1 := by
  apply Subgroup.eq_of_le_of_card_ge outer_H2_le
  rw [Subgroup.card_map_of_injective outer.injective, H1_card]
  exact synthemeStabilizer_order.ge

def residual : Subgroup Symmetric := (pResidual 2 H2).map H2.subtype

theorem outer_residual : residual.map outer.toMonoidHom = K := by
  rw [residual, Subgroup.map_embedded_pResidual, outer_H2, residual_H1]

theorem outer_alternating :
    (alternatingGroup (Fin 6)).map outer.toMonoidHom = alternatingGroup (Fin 6) := by
  exact Subgroup.characteristic_iff_map_eq.mp inferInstance outer

theorem outer_L2 : L2.map outer.toMonoidHom = L1 := by
  rw [L2, Subgroup.map_inf _ _ _ outer.injective, outer_H2, outer_alternating]
  rfl

theorem residual_le_H2 : residual ≤ H2 := Subgroup.map_subtype_le _

theorem residual_le_alternating : residual ≤ alternatingGroup (Fin 6) := by
  apply (Subgroup.map_le_map_iff_of_injective (f := outer.toMonoidHom) outer.injective).mp
  rw [outer_residual, outer_alternating]
  exact inf_le_right

/-- The alternating restriction has exactly the same embedded two-residual. -/
theorem residual_L2 : (pResidual 2 L2).map L2.subtype = residual := by
  apply Subgroup.map_injective (f := outer.toMonoidHom) outer.injective
  rw [Subgroup.map_embedded_pResidual, outer_L2, BinaryFlags.residual_L1, outer_residual]

/-- The actual isomorphism of marked parabolics. -/
noncomputable def parabolicEquiv : H2 ≃* H1 :=
  (outer.subgroupMap H2).trans (MulEquiv.subgroupCongr outer_H2)

/-- The actual isomorphism from the marked residual to the duad's embedded A₄. -/
noncomputable def residualEquiv : residual ≃* K :=
  (outer.subgroupMap residual).trans (MulEquiv.subgroupCongr outer_residual)

theorem parabolicEquiv_coe (g : H2) : (parabolicEquiv g : Symmetric) = outer g := rfl

theorem residualEquiv_coe (g : residual) : (residualEquiv g : Symmetric) = outer g := rfl

noncomputable def outerAlternating : MulAut Alternating :=
  outerAltAut.trans (MulAut.conjNormal relabel)

theorem outerAlternating_coe (g : Alternating) :
    (outerAlternating g : Symmetric) = outer g := rfl

private abbrev a : Symmetric := Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 4 5
private abbrev b : Symmetric := Equiv.swap 0 3 * Equiv.swap 1 2 * Equiv.swap 4 5

theorem outer_swap01 : outer swap01 =
    Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 4 5 := by
  have h : outerHom swap01 = Equiv.swap 0 5 * Equiv.swap 1 3 * Equiv.swap 2 4 := by
    apply Equiv.ext
    intro i
    change outerAct swap01 i = _
    apply pentadAt_injective
    rw [outerAct_spec]
    fin_cases i <;> decide
  rw [outer_apply, h]
  decide

theorem outer_swap23 : outer swap23 =
    Equiv.swap 0 3 * Equiv.swap 1 2 * Equiv.swap 4 5 := by
  have h : outerHom swap23 = Equiv.swap 0 3 * Equiv.swap 1 5 * Equiv.swap 2 4 := by
    apply Equiv.ext
    intro i
    change outerAct swap23 i = _
    apply pentadAt_injective
    rw [outerAct_spec]
    fin_cases i <;> decide
  rw [outer_apply, h]
  decide

theorem outer_swap45 : outer swap45 =
    Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 := by
  have h : outerHom swap45 = Equiv.swap 0 1 * Equiv.swap 2 4 * Equiv.swap 3 5 := by
    apply Equiv.ext
    intro i
    change outerAct swap45 i = _
    apply pentadAt_injective
    rw [outerAct_spec]
    fin_cases i <;> decide
  rw [outer_apply, h]
  decide

theorem outer_not_inner (g : Symmetric) : outer ≠ MulAut.conj g := by
  intro he
  have hc : IsConj swap01 (outer swap01) := isConj_iff.mpr ⟨g, by rw [he]; rfl⟩
  have ht := Equiv.Perm.isConj_iff_cycleType_eq.mp hc
  rw [outer_swap01] at ht
  exact (by decide : swap01.cycleType ≠ a.cycleType) ht

noncomputable def oppositeAction : Representation (ZMod 2) Symmetric Natural :=
  symmetricAction.comp outer.toMonoidHom

noncomputable def oppositeAlternatingAction : Representation (ZMod 2) Alternating Natural :=
  alternatingAction.comp outerAlternating.toMonoidHom

theorem oppositeAlternatingAction_eq_restrict : oppositeAlternatingAction =
    oppositeAction.comp (alternatingGroup (Fin 6)).subtype := rfl

theorem oppositeAction_injective : Function.Injective oppositeAction :=
  symmetricAction_injective.comp outer.injective

theorem oppositeAlternatingAction_injective : Function.Injective oppositeAlternatingAction :=
  alternatingAction_injective.comp outerAlternating.injective

theorem opposite_H2_fixes {g : Symmetric} (hg : g ∈ H2) :
    oppositeAction g (pairVector 4 5) = pairVector 4 5 := by
  have hm : outer g ∈ H1 := outer_H2 ▸ (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
  change symmetricAction (outer g) _ = _
  rw [pairVector_map]
  rcases mem_H1_cases hm with ⟨h4, h5⟩ | ⟨h4, h5⟩
  · rw [h4, h5]
  · rw [h4, h5, pairVector_comm]

theorem opposite_H2_fixed_nonzero : ∃ v : Natural, v ≠ 0 ∧
    ∀ g ∈ H2, oppositeAction g v = v :=
  ⟨pairVector 4 5, pairVector45_ne_zero, fun _ hg => opposite_H2_fixes hg⟩

theorem opposite_L2_fixed_nonzero : ∃ v : Natural, v ≠ 0 ∧
    ∀ g : Alternating, g.val ∈ L2 → oppositeAlternatingAction g v = v :=
  ⟨pairVector 4 5, pairVector45_ne_zero, fun _ hg => opposite_H2_fixes hg.1⟩

theorem opposite_double_displacement :
    oppositeAction swap01 (oppositeAction swap23 (pairVector 0 4) - pairVector 0 4) -
      (oppositeAction swap23 (pairVector 0 4) - pairVector 0 4) = pairVector 4 5 := by
  change symmetricAction (outer swap01) (symmetricAction (outer swap23) _ - _) -
    (symmetricAction (outer swap23) _ - _) = _
  rw [outer_swap01, outer_swap23, map_sub]
  simp only [symmetricAction, pairVector_map]
  apply Subtype.ext
  change (constants (Fin 6)).mkQ _ - (constants (Fin 6)).mkQ _ -
    ((constants (Fin 6)).mkQ _ - (constants (Fin 6)).mkQ _) = (constants (Fin 6)).mkQ _
  rw [← map_sub, ← map_sub, ← map_sub]
  apply (Submodule.Quotient.eq (constants (Fin 6))).mpr
  apply Submodule.mem_span_singleton.mpr
  refine ⟨1, ?_⟩
  ext i
  fin_cases i <;> decide

theorem D_not_quadratic : ¬ IsQuadratic oppositeAction D := by
  intro h
  have hh := h swap01 swap01_mem_D swap23 swap23_mem_D (pairVector 0 4)
  exact pairVector45_ne_zero (opposite_double_displacement.symm.trans (sub_eq_zero.mpr hh))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Marked
