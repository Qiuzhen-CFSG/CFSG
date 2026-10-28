module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeSmallNatural
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuOddControl
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.EssentialKernel

/-!
# The original M22-code chief kernel is the actual two-core

Odd-normalizer control rules out an odd prime divisor in a normal subgroup
of H contained in the original M-centralizer of V: Frattini's argument would
place all of H in M. Apply this to the kernel of the original whole-span
action. Its essential-action kernel has two-group image on that span, so
it too is a two-group and equals O₂(H).

The source application constructs the small natural action on the same
essential section with this exact kernel. It preserves the original sharp
actor and all covering maps. This removes the kernel premise needed by
the remaining symmetric-five overlap calculation; it does not yet exclude
those rows or establish the final M24-cocode selection.
Source: Aschbacher--Smith, 3.1.9(6), pp.577--578, and 8.2.2(1), p.715,
with the odd-normalizer control of 4.4.3, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource MathieuCode Sporadic.Mathieu
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open ChapterD NoncentralChiefRefinement Chapter8.MathieuShadowRows
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

omit [Finite G] in
private theorem marked_code_mathieu
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation) : HasMathieuCentralQuotient D.orbitComponent := by
  have hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M22) := by
    have hz : center D.orbitComponent = ⊥ := by
      have hh := FixedElementary.map_center d.componentEquiv
      rw [m22_center_eq_bot] at hh
      exact (map_eq_bot_iff_of_injective _ d.componentEquiv.injective).mp hh
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans
      d.componentEquiv⟩
  exact Or.inr (Or.inl hq)

set_option backward.isDefEq.respectTransparency false in
/-- Odd-normalizer control identifies the kernel on the original essential
section, without assuming that the canonical minimal-parabolic core is a two-group. -/
theorem sourceOrbit_m22_code_essential_kernel_eq_twoCore
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2)
    [hU : IsElementaryAbelian 2 ((conjugateSpan H D.sourceOrbit).subgroupOf H)]
    (a : Chapter3.EssentialSeedAction H D.sourceOrbit (T.subtype hH.1.1.2)
      (hcore.trans (ChapterD.UniqueFactor.twoCore_le H)))
    {A : Subgroup H} (ha : EssentialChiefActor a A) :
    a.projection.ker = pCore 2 H := by
  have hm := D.marked_code_mathieu d
  obtain ⟨c,_,_,_⟩ := D.sourceOrbit_m22_code_inside_core_inputs h hmany hV hnon d hH hcore
  obtain ⟨s⟩ := SeriesOn.exists_series ((conjugateSpan H D.sourceOrbit).subgroupOf H)
  have hex : ∃ i : Fin s.series.length, ¬ s.Central i := by
    by_contra! hz
    have hz' := s.noncentralCount_eq_zero_iff.mpr hz
    have ht := D.sourceOrbit_m22_code_inside_core_two_chiefs h hmany hV hnon d hH hcore s
    omega
  obtain ⟨i,hi⟩ := hex
  exact essential_kernel_eq_twoCore c a ha s i hi
    (D.sourceOrbit_mathieu_odd_normalizer_le h hmany hV hm hnon)

set_option backward.isDefEq.respectTransparency false in
/-- The constructed small natural essential action has precisely O₂(H) as
kernel, with the same original minimum sharp actor. -/
theorem sourceOrbit_m22_code_inside_core_nonsolvable_small_natural_faithful
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) (hns : ¬ Group.IsSolvable H) :
    let U := (conjugateSpan H D.sourceOrbit).subgroupOf H
    ∃ hU : IsElementaryAbelian 2 U,
      let := hU
      ∃ a : Chapter3.EssentialSeedAction H D.sourceOrbit (T.subtype hH.1.1.2)
          (hcore.trans (ChapterD.UniqueFactor.twoCore_le H)),
        ∃ A ∈ elementaryAbelianMaxSubgroups ((T.subtype hH.1.1.2) : Subgroup H),
          ¬ A ≤ pCore 2 H ∧ IsQuadratic (normalRepresentation U) A ∧
          (∀ B ∈ elementaryAbelianMaxSubgroups ((T.subtype hH.1.1.2) : Subgroup H),
            ¬ B ≤ pCore 2 H → (pCore 2 H).relIndex A ≤ (pCore 2 H).relIndex B) ∧
          EssentialChiefActor a A ∧ ChapterB.ChiefSmallNaturalAlternatives a.imageRepresentation ∧
          a.projection.ker = pCore 2 H := by
  obtain ⟨hU,a,A,hA,hAR,hquad,hmin,ha,hs⟩ :=
    D.sourceOrbit_m22_code_inside_core_nonsolvable_small_natural h hmany hV hnon d hH hcore hns
  let := hU
  exact ⟨hU,a,A,hA,hAR,hquad,hmin,ha,hs,
    D.sourceOrbit_m22_code_essential_kernel_eq_twoCore h hmany hV hnon d hH hcore a ha⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every original noncentral chief action has the same full two-core kernel.
No essential-section, actor, kernel or marking premise is added. -/
theorem sourceOrbit_m22_code_inside_core_nonsolvable_chief_kernel
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) (hns : ¬ Group.IsSolvable H)
    [hU : IsElementaryAbelian 2 ((conjugateSpan H D.sourceOrbit).subgroupOf H)]
    (s : SeriesOn ((conjugateSpan H D.sourceOrbit).subgroupOf H))
    (i : Fin s.series.length) (hi : ¬ s.Central i) :
    (actionHom (s.factorRepresentation i)).ker = pCore 2 H := by
  obtain ⟨hU',a,A,_,_,_,_,ha,_⟩ :=
    D.sourceOrbit_m22_code_inside_core_nonsolvable_small_natural h hmany hV hnon d hH hcore hns
  obtain ⟨e⟩ := (ha.chief s i hi).2
  exact (literal_chief_action_kernel_eq e).symm.trans
    (D.sourceOrbit_m22_code_essential_kernel_eq_twoCore h hmany hV hnon d hH hcore a ha)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
