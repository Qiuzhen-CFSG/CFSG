module
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonComplete

/-!
# Remaining chosen-action exits of the centralizing branch

The completed preparation chooses the whole local module or its literal
proper moved support. This extension retains that choice while separating the
three larger Case-I actions from the dihedral and Omega actions of Section 15.2.
For a proper support encountered in the full action's partition, restriction
of the prepared module preserves core containment and residual centralization;
the existing support coordinates supply its exact Omega action.

This partition does not assert the large-action exclusion of 15.1.15 or
the small-action contradiction of Section 15.2. Their conditional assembly
is provided separately in `SourceCentralizing.Resolver`.

Source: Aschbacher--Smith 15.1.4, 15.1.15 and 15.2.1, pp.1087,1091,1104.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition Chapter14.SourcePreliminaries Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- The literal choice prescribed in 15.1.4. -/
@[expose] def SourceChosenOrigin (T : Sylow 2 G) (M Mc W : Subgroup G)
    [IsElementaryAbelian 2 (localModule T M)] : Prop :=
  W = localModule T M ∨ ∃ U : Submodule (ZMod 2) (Additive (localModule T M)),
    SourceCases.Proper T M Mc (localModule T M)
      (imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)) U ∧
    W = (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map (localModule T M).subtype

/-- The remaining actions treated in Section 15.2, on the chosen subgroup itself. -/
@[expose] def SmallChosenAction (M W : Subgroup G) [IsElementaryAbelian 2 W]
    (hn : M ≤ normalizer (W : Set G)) : Prop :=
  SourceCases.Dihedral (imageRepresentation M W hn) ∨
    SourceCases.Omega (imageRepresentation M W hn)

/-- The three larger actions of 15.1.15. The decomposable row retains its
actual factor data, permutation action and ratio-two guard. -/
@[expose] def LargeChosenAction (T : Sylow 2 G) (M W : Subgroup G) [IsElementaryAbelian 2 W]
    (hn : M ≤ normalizer (W : Set G)) : Prop :=
  let ρ := imageRepresentation M W hn
  let f := (actionHom M W hn).rangeRestrict
  let S := ((T : Subgroup G).subgroupOf M).map f
  SourceCases.Nine ρ S ∨ SourceCases.Extraspecial ρ S ∨
    (cubicRatio ρ = 2 ∧
      ∃ (U : Submodule (ZMod 2) (Additive W)) (c : FactorData ρ (Jhat ρ) U)
        (d : Decomposition c.representation)
        (π : internalActionImage M W hn →* Equiv.Perm d.Index),
        d.FittingFull ∧
        (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
          (c.ambientFactor d (π g i)).actor) ∧
        (∀ g i, (c.ambientFactor d i).space.map (ρ g) =
          (c.ambientFactor d (π g i)).space) ∧
        SourceCases.Decomposable ρ (T : Subgroup G) M f c d π)

/-- Restricting a prepared full module to the source's proper support preserves
preparation and gives the Omega action on that exact subgroup. -/
theorem PreparedChosenModule.proper_support_prepared
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (h : PreparedChosenModule T M (localModule T M)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    ∀ U : Submodule (ZMod 2) (Additive (localModule T M)),
      SourceCases.Proper T M Mc (localModule T M)
        (imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)) U →
      let W := (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map (localModule T M).subtype
      ∃ hp : PreparedChosenModule T M W,
        letI := hp.elementary
        SourceCases.Omega (imageRepresentation M W hp.normalized) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  intro U hU
  let W := (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype
  have hWV : W ≤ V := map_subtype_le _
  have hstable := hU.2.2.2.1
  have hcompl := hU.2.2.2.2.2.2.2.1
  let := Jhat_normal ρ
  obtain ⟨hWM,hnW,hEW,hspan⟩ := source_localAction_complement_generated_seed hG T hM
    U (fixedSpace ρ (Jhat ρ)) hstable (fixedSpace_stable_of_normal ρ (Jhat ρ)) hcompl
  let := hEW
  have hne : W ≠ ⊥ := by
    intro hb
    apply hU.2.2.2.2.1
    apply le_bot_iff.mp
    intro v hv
    have hx : (v.toMul : G) ∈ W := mem_map_of_mem V.subtype hv
    rw [hb] at hx
    have hv0 : v = 0 := Additive.toMul.injective (Subtype.ext (Subgroup.mem_bot.mp hx))
    simpa only [hv0] using (zero_mem (⊥ : Submodule (ZMod 2) (Additive V)))
  have ho := hU.chosen_omega T M Mc V (le_normalizer_conjugateSpanBy _ _) U hnW
  have hq : quadraticRatio (imageRepresentation M W hnW) = 2 :=
    quadraticRatio_eq_two_of_four_cubic _ (by rw [ho.2.2.1])
      (by rw [ho.2.1]; norm_num [ENNReal.lt_div_iff_mul_lt])
      (by rw [ho.2.1, ENNReal.div_le_iff (by norm_num) (by norm_num)]; norm_num)
  exact ⟨⟨hWV,hWM,hne,hnW,hEW,hspan,hq,
    h.seed_residual.trans (centralizer_le hWV),
    fun H hH => (h.intersection_residual H hH).trans (centralizer_le hWV),
    fun H hH => hWV.trans (h.inside_core H hH)⟩,ho⟩

/-- Prepared chosen modules reduce to the original two exits or to precisely
the larger Case-I and small Case-II actions, retaining their source origins. -/
theorem source_prepared_chosen_exits
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M ∨
    Nonempty (NaturalOrthogonalAction M (localModule T M)) ∨
    (∃ hp : PreparedChosenModule T M (localModule T M),
      LargeChosenAction T M (localModule T M) hp.normalized) ∨
    ∃ W : Subgroup G, SourceChosenOrigin T M Mc W ∧
      ∃ hp : PreparedChosenModule T M W,
        letI := hp.elementary
        SmallChosenAction M W hp.normalized := by
  classical
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let f := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  rcases source_prepared_chosen_or_rankTwo_complete hG T hempty hM hmany hJ hu hne with
    hr | hn | ⟨W,hW,hp⟩
  · exact Or.inl hr
  · exact Or.inr (Or.inl hn)
  · rcases hW with rfl | ⟨U,hU,rfl⟩
    · obtain ⟨U,c,d,π,hd,_,_,he,hcases⟩ :=
        source_lemma_15_1_2_centralizing hG T hempty hM hmany hJ hu hne
      rcases hcases with hdi | ho | hdec | hex | hnine | hproper
      · exact Or.inr (Or.inr (Or.inr ⟨V,Or.inl rfl,hp,Or.inl hdi⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨V,Or.inl rfl,hp,Or.inr ho⟩))
      · have hdec_full := hdec
        obtain ⟨hc,p,m,hpm,hmark,i,j,hij,hall,_,_,_,hcompl,t,ht,htij,htji⟩ := hdec
        have hU : U = ⊤ := by
          apply top_unique
          rw [←hcompl.sup_eq_top]
          exact sup_le
            ((le_iSup (fun k => (c.ambientFactor d k).space) i).trans
              (c.ambient_spaces_generate d).le)
            ((le_iSup (fun k => (c.ambientFactor d k).space) j).trans
              (c.ambient_spaces_generate d).le)
        have htrans : ∀ a b, ∃ g : D, π g a = b := by
          intro a b
          rcases hall a with rfl | rfl <;> rcases hall b with rfl | rfl
          · exact ⟨1,by simp⟩
          · exact ⟨f t,htij⟩
          · exact ⟨f t,htji⟩
          · exact ⟨1,by simp⟩
        rcases source_localAction_full_orbit_decomposable_ratio hG T hempty hM hmany hJ
          U c d hd hU π (fun g i => (he g i).2.1) (fun g i => (he g i).2.2)
          htrans (by omega) with hq | hn
        · exact Or.inr (Or.inr (Or.inl ⟨hp,Or.inr (Or.inr
            ⟨hq,U,c,d,π,hd,fun g i => (he g i).2.1,fun g i => (he g i).2.2,hdec_full⟩)⟩))
        · exact Or.inr (Or.inl hn)
      · exact Or.inr (Or.inr (Or.inl ⟨hp,Or.inr (Or.inl hex)⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨hp,Or.inl hnine⟩))
      · obtain ⟨hpW,ho⟩ := hp.proper_support_prepared hG T hM U hproper
        exact Or.inr (Or.inr (Or.inr ⟨_,Or.inr ⟨U,hproper,rfl⟩,hpW,Or.inr ho⟩))
    · let := hp.elementary
      have ho := hU.chosen_omega T M Mc V (le_normalizer_conjugateSpanBy _ _) U hp.normalized
      exact Or.inr (Or.inr (Or.inr ⟨_,Or.inr ⟨U,hU,rfl⟩,hp,Or.inr ho⟩))

end CFSG.Quasithin.Chapter15.Section01
