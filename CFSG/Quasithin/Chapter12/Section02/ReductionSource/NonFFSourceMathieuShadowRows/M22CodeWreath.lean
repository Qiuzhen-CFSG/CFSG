module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeSolvable
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CommonChiefKernel

/-!
# The full wreath quotient of the original inside-core M22 parabolic

The completed source sieve first proves the original H solvable. Each of
its noncentral chief images is then S₃ wreath C₂, and the original minimal
parabolic identifies each kernel with the same maximal-overgroup core.
The flag-kernel and odd-normalizer argument makes this core exactly O₂(H).
Thus the entire original quotient H/O₂(H) is the wreath group, strengthening
the previously constructed quotient by the three-core.

The original inside-core assumption is still explicit. This theorem feeds
the Xi construction in `M22CodeXi`; it does not assert the later M22-code
exclusion or same-orbit M24-cocode selection. Source: Aschbacher--Smith
3.1.9(6), B.6.8--9 and 8.2.2(1), printed pp.113--116,577--578,715,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource MathieuCode Sporadic.Mathieu
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open ChapterD Chapter8.MathieuShadowRows
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

omit [Finite G] in
private theorem code_mathieu
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation) : HasMathieuCentralQuotient D.orbitComponent := by
  have hz : center D.orbitComponent = ⊥ := by
    have hh := FixedElementary.map_center d.componentEquiv
    rw [m22_center_eq_bot] at hh
    exact (map_eq_bot_iff_of_injective _ d.componentEquiv.injective).mp hh
  exact Or.inr (Or.inl ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).trans d.componentEquiv⟩)

/-- All original solvable chief actions have the same maximal-overgroup
core. Odd-normalizer control makes that core the actual O₂(H). -/
theorem sourceOrbit_m22_code_inside_core_wreath
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) :
    ∃ hp : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤,
      ChapterB.minimalParabolicCore (T.subtype hH.1.1.2) hp = pCore 2 H ∧
      Nonempty ((H ⧸ pCore 2 H) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) := by
  have hs := D.sourceOrbit_m22_code_inside_core_solvable h hmany hV hnon d hH hcore
  let := hs
  obtain ⟨hp,he,_⟩ :=
    D.sourceOrbit_m22_code_inside_core_solvable_quotients h hmany hV hnon d hH hcore hs
  obtain ⟨c,_,_,_⟩ := D.sourceOrbit_m22_code_inside_core_inputs h hmany hV hnon d hH hcore
  obtain ⟨hU,hchief⟩ := D.sourceOrbit_m22_code_inside_core_chief_sieve h hmany hV hnon d hH hcore
  let := hU
  let U := (conjugateSpan H D.sourceOrbit).subgroupOf H
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hex : ∃ i : Fin s.series.length, ¬ s.Central i := by
    by_contra! hz
    have hz' := s.noncentralCount_eq_zero_iff.mpr hz
    have ht := D.sourceOrbit_m22_code_inside_core_two_chiefs h hmany hV hnon d hH hcore s
    omega
  obtain ⟨i,hi⟩ := hex
  have hk (j : Fin s.series.length) (hj : ¬ s.Central j) :
      (s.factorRepresentation j).ker = ChapterB.minimalParabolicCore (T.subtype hH.1.1.2) hp := by
    let q := actionHom (s.factorRepresentation j)
    have hsol : Group.IsSolvable (actionImage (s.factorRepresentation j)) :=
      Group.isSolvable_of_surjective (f := q)
        (s.factorRepresentation j).asGroupHom.rangeRestrict_surjective
    obtain ⟨⟨e⟩,_⟩ := (hchief s j hj).2 hsol
    let w := RegularWreathProduct.congr SLTwoPermThree.sl2Two_equiv_perm_three.some
      (MulEquiv.refl (Multiplicative (ZMod 2)))
    let f := (e.trans w.symm).toMonoidHom.comp (QuotientGroup.mk' q.ker)
    have hf : Function.Surjective f := (e.trans w.symm).surjective.comp
      (QuotientGroup.mk'_surjective _)
    have hfker : f.ker = q.ker := by
      rw [MonoidHom.ker_comp_of_injective _ _ (e.trans w.symm).injective,QuotientGroup.ker_mk']
    rw [←actionHom_ker_eq,←hfker]
    exact wreath_parabolic_kernel _ hp f hf
  have hJ := common_chief_kernel_eq_twoCore c hp
    (hcore.trans (ChapterD.UniqueFactor.twoCore_le H)) s i hi hk
    (D.sourceOrbit_mathieu_odd_normalizer_le h hmany hV (D.code_mathieu d) hnon)
  have hJ' : ChapterB.minimalParabolicCore (T.subtype hH.1.1.2) hp = pCore 2 H := hJ
  exact ⟨hp,hJ',⟨(QuotientGroup.quotientMulEquivOfEq hJ'.symm).trans he.some⟩⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
