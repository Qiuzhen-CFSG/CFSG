module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.Crossed
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.FourNatural
public import Theory.Representation.PSL3Two.FourNaturalCommuting
public import Theory.Representation.BinaryConjugationSection.CommutingConjugate

/-!
# Crossed centralization in the four-copy source row

Minimality makes the intersection of the two moved factors either zero or
the whole full module. In the first case their commutator is zero. In the
second, a nonzero component-fixed vector already gives crossed centralization;
otherwise the marking has zero kernel on the whole full module. The literal
exchanger would then give two commuting equivalent four-copy actions,
contradicting the Singer displacement on the multiplicity space.

The argument uses the original multiple-overgroup and minimality hypotheses.
It closes the four-copy small-offender exclusion, also after contained
reselection, without a crossed-centralization premise or a tensor exclusion.
Source: Aschbacher--Smith 10.1.1(6) and 10.2.12, printed pp.741,754--755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02 PointControl.Selection.ModuleChoice
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The quiet minimal full module has separated moved factors, or each moved factor is full. -/
theorem quiet_crossed_or_moved_eq_full
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) ∨
      ⁅D.fullModule,L⁆ = D.fullModule := by
  let V := D.fullModule
  let W := ⁅V,L⁆
  let B := L.map (MulAut.conj t).toMonoidHom
  let W' := W.map (MulAut.conj t).toMonoidHom
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_normalizer_componentOrbit L T
  have hV (m : G) (hm : m ∈ D.maximalLocal) :
      V.map (MulAut.conj m).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hm)
  have hpair (m : G) (hm : m ∈ D.maximalLocal) :
      W.map (MulAut.conj m).toMonoidHom = W ∨
      W.map (MulAut.conj m).toMonoidHom = W' := by
    rcases source_nonnormal_maximal_pair D hn ht htn m hm with he | he
    · left; change (⁅V,L⁆).map _ = ⁅V,L⁆; rw [map_commutator,hV m hm,he]
    · right; change (⁅V,L⁆).map _ = (⁅V,L⁆).map _
      rw [map_commutator,map_commutator,hV m hm,hV t (hTM ht),he]
  have hpair' (m : G) (hm : m ∈ D.maximalLocal) :
      W'.map (MulAut.conj m).toMonoidHom = W ∨
      W'.map (MulAut.conj m).toMonoidHom = W' := by
    have he : W'.map (MulAut.conj m).toMonoidHom =
        W.map (MulAut.conj (m*t)).toMonoidHom := by
      change (W.map _).map _ = _
      rw [map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    rw [he]
    exact hpair (m*t) (D.maximalLocal.mul_mem hm (hTM ht))
  have hUN : D.maximalLocal ≤ normalizer (↑(W ⊓ W') : Set G) := by
    intro m hm
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_inf _ _ _ (MulAut.conj m).injective]
    change W.map (MulAut.conj m).toMonoidHom ⊓
      W'.map (MulAut.conj m).toMonoidHom = W ⊓ W'
    have hinj := map_injective (f := (MulAut.conj m).toMonoidHom) (MulAut.conj m).injective
    rcases hpair m hm with ha | ha <;> rcases hpair' m hm with hb | hb
    · have he : W = W' := hinj (ha.trans hb.symm)
      rw [ha,hb,he,inf_idem]
    · rw [ha,hb]
    · rw [ha,hb,inf_comm]
    · have he : W = W' := hinj (ha.trans hb.symm)
      rw [ha,hb,he,inf_idem]
  have hLN : L ≤ normalizer (V : Set G) :=
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans D.maximalLocal_normalizes_fullModule
  have hWV : W ≤ V := le_normalizer_iff_commutator_le_left.mp hLN
  rcases source_minimal_fullModule_eq_or_le_centralizer D hmin (W ⊓ W') hUN
      (inf_le_left.trans hWV) with he | hc
  · exact Or.inr (le_antisymm hWV (he.symm.le.trans (show W ⊓ W' ≤ W from inf_le_left)))
  left
  have hz : W ⊓ W' = ⊥ := le_bot_iff.mp ((le_inf (inf_le_left.trans hWV) hc).trans_eq
    (source_fullModule_fixed_eq_bot_of_many D hmany hJ))
  have hBR : B ≤ localOrbit T L := by
    rintro _ ⟨l,hl,rfl⟩
    exact (originalConjugateOrbitInclusion ht ⟨l,hl⟩).property
  have hBL : B ≤ normalizer (L : Set G) := hBR.trans (source_nonnormal_orbit_le_normalizer D hn)
  have hBV : B ≤ normalizer (V : Set G) :=
    (hBR.trans (localOrbit T L).le_normalizer).trans D.maximalLocal_normalizes_fullModule
  have hBW : B ≤ normalizer (W : Set G) := by
    intro b hb
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅V,L⁆).map _ = ⁅V,L⁆
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hBV hb),
      mem_normalizer_iff_map_conj_eq.mp (hBL hb)]
  have hVB : ⁅V,B⁆ = W' := by
    change ⁅V,L.map _⁆ = (⁅V,L⁆).map _
    rw [map_commutator,hV t (hTM ht)]
  have hcomm : ⁅W,B⁆ = ⊥ := le_bot_iff.mp ((le_inf
    (le_normalizer_iff_commutator_le_left.mp hBW)
    ((commutator_mono hWV le_rfl).trans_eq hVB)).trans_eq hz)
  exact crossed_of_opposite_centralization D ht htn
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)

/-- The genuine source prefix supplies crossed centralization for the four-copy marking. -/
theorem four_natural_crossed_of_minimal
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule) (hrow : FourNaturalRow D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) := by
  by_cases hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)
  swap
  · exact crossed_of_local_thompson D hJ ht htn
  by_cases hz : D.fullModule ⊓ centralizer (L : Set G) = ⊥
  swap
  · exact quiet_crossed_of_component_fixed_ne_bot D hmany hmin hJ ht htn hz
  rcases quiet_crossed_or_moved_eq_full D hmany hmin hJ ht htn with hcross | hw
  · exact hcross
  obtain ⟨e,⟨d⟩⟩ := hrow
  let : IsElementaryAbelian 2 D.fullModule :=
    D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let d0 : BinaryConjugationSection L D.fullModule ⊥
      (BinaryLinearThree.FourNatural.action.comp q) := by
    simpa only [hw,hz] using d
  obtain ⟨τ,hτ⟩ := d0.exists_commuting_conjugate BinaryLinearThree.FourNatural.action q hq
    (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T ht))
    (opposite_commutator_centralizes_fullModule D ht htn)
  exact (BinaryLinearThree.FourNatural.not_commuting_conjugate τ hτ).elim

/-- The actual four-copy row is incompatible with the attained small offender. -/
theorem no_four_natural_of_configuration
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g) (hrow : FourNaturalRow D)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) : False :=
  no_four_natural_of_small_offender D c hrow
    (fun _ ht htn => four_natural_crossed_of_minimal D c.many c.minimal hrow ht htn) hNL

/-- The same exclusion holds after a contained seed reselection. -/
theorem no_contained_four_natural_of_configuration
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (E : FundamentalSetup KnownSimple.IsKnownSimple T L) (hE : E.fullModule ≤ D.fullModule)
    (hrow : FourNaturalRow E)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) : False := by
  obtain ⟨he,cE⟩ := c.reselect E hE
  exact no_four_natural_of_configuration E cE hrow hNL

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition

