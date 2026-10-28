module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeFiveActions
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.FiveChiefExclusion

/-!
# Excluding the original single-five M22-code chief action

The original minimum sharp actor centralizes the original orbit and acts
as an offender on every noncentral chief factor. A five-point marking
therefore supplies a transposition in the image of that centralizer. The
full chief kernel is the original O₂(H), so odd-normalizer control and
the actual maximal overlap contradict the single-five quotient.

The final application retains only the paired-five marking in the
nonsolvable inside-core branch. Its kernel, full actor and offender base
remain literal. Exclusion of the paired row and the subsequent M22-code
argument are not asserted here.
Source: Aschbacher--Smith 3.1.9(6), p.578, and 8.2.2(1), p.715.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource MathieuCode Sporadic.Mathieu
open ChapterB.QuasisimpleSource ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
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
/-- The single-five action is impossible on every original noncentral chief factor. -/
theorem sourceOrbit_m22_code_inside_core_not_single_five
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
    ¬ Nonempty (ActionEquiv (Representation.BinaryOffender.imageRepresentation
      (s.factorRepresentation i)) (BinaryPermutation.naturalRepresentation (Fin 5))) := by
  rintro ⟨e⟩
  obtain ⟨c,hn,_,_⟩ := D.sourceOrbit_m22_code_inside_core_inputs h hmany hV hnon d hH hcore
  obtain ⟨hU',a,A,hA,_,_,_,ha,_,hk⟩ :=
    D.sourceOrbit_m22_code_inside_core_nonsolvable_small_natural_faithful
      h hmany hV hnon d hH hcore hns
  let ρ := s.factorRepresentation i
  let q := e.groupEquiv.toMonoidHom.comp (actionHom ρ)
  have hker : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.groupEquiv.injective]
    obtain ⟨l⟩ := (ha.chief s i hi).2
    exact (literal_chief_action_kernel_eq l).symm.trans hk
  have hoff : IsOffender (BinaryPermutation.naturalRepresentation (Fin 5)) (A.map q) := by
    have hh := (ha.chief s i hi).1.map_equivariant _ _ e.groupEquiv.toMonoidHom
      e.groupEquiv.injective e.linearEquiv e.intertwines
    simpa only [actionSubgroup,map_map] using hh
  have hout : ¬ A.map q ≤ alternatingGroup (Fin 5) := by
    obtain ⟨B,hBA,hB⟩ := hoff.exists_bestOffender _
    exact fun hle => ((ChapterB.Offenders.Odd.isBestOffender_natural_iff_caseAFamily
      (Or.inl rfl) B).mp hB).not_le_alternating (hBA.trans hle)
  obtain ⟨b,hb,hbo⟩ := Set.not_subset.mp hout
  let := hoff.1.2
  have hbne : b ≠ 1 := fun he => hbo (he ▸ one_mem _)
  have hbs : b.IsSwap := Equiv.Perm.five_isSwap_of_outer_involution b
    (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian b hb) hbne) hbo
  exact five_chief_impossible c a.original_minimal hn
    (D.sourceOrbit_mathieu_odd_normalizer_le h hmany hV (D.marked_code_mathieu d) hnon)
    q (e.groupEquiv.surjective.comp ρ.asGroupHom.rangeRestrict_surjective)
    (hker ▸ pCore_isPGroup) A hA.1 ha.centralizes ⟨b,hb,hbs⟩

set_option backward.isDefEq.respectTransparency false in
/-- The original nonsolvable inside-core branch retains only the paired-five
chief action, with its full original kernel and offender base unchanged. -/
theorem sourceOrbit_m22_code_inside_core_nonsolvable_paired_five
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
      ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
        (actionHom (s.factorRepresentation i)).ker = pCore 2 H ∧
        ∃ e : ActionEquiv (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
            BinaryPermutation.FivePair.wreathRepresentation,
          (offenderSubgroup (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))).map
            e.groupEquiv.toMonoidHom = BinaryPermutation.FivePair.baseSubgroup := by
  obtain ⟨hU,hf⟩ := D.sourceOrbit_m22_code_inside_core_nonsolvable_five_actions
    h hmany hV hnon d hH hcore hns
  let := hU
  refine ⟨hU,?_⟩
  dsimp only
  intro s i hi
  obtain ⟨hk,hs⟩ := hf s i hi
  exact ⟨hk,hs.resolve_left (D.sourceOrbit_m22_code_inside_core_not_single_five
    h hmany hV hnon d hH hcore hns s i hi)⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
