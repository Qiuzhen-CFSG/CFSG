module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalRecognitionPairAxis
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Full LT action from a TI hyperplane pair

The opposite mutual normalizer lies in M = N_G(L) ∩ N_G(V), by NoEscape.
The image of M has trivial two-core: the original LT image is reduced and
contains the image of the same ambient Sylow two-subgroup. The full-axis
recognition theorem therefore makes the M image GL(V). Its L image is normal
and nontrivial, so simplicity of binary GL in dimension at least three makes
that image full as well. This proves fullness of the literal LT action.

This argument discharges the action comparison needed between the pair and
LT without assuming the natural row, irreducibility or later 12.2.21. The
only remaining pair premise is that its mutual normalizer is a hyperplane.
The original quotient-action marking remains separate for the final consumer.
Source: Aschbacher–Smith, the action comparison in 12.2.10, p.798, and the
construction before 12.2.20, p.802; corrected dual G.3.1 with trivial two-core.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

private theorem image_twoCore_eq_bot_of_sylow {K : Type*} [Group K]
    (T : Sylow 2 G) (J : Subgroup G) (hTJ : (T : Subgroup G) ≤ J)
    (f : G →* K) (hJ : pCore 2 (J.map f) = ⊥) : pCore 2 f.range = ⊥ := by
  let S := T.mapSurjective f.rangeRestrict_surjective
  let F := (J.map f).subgroupOf f.range
  have hSF : (S : Subgroup f.range) ≤ F := by
    rintro x ⟨t, ht, rfl⟩
    exact mem_map_of_mem f (hTJ ht)
  let e : F ≃* J.map f := subgroupOfEquivOfLe (map_le_range (H := J) (f := f))
  have he := pCore_map_iso 2 e
  rw [hJ] at he
  have hF : pCore 2 F = ⊥ := (map_eq_bot_iff_of_injective _ e.injective).mp he
  have hc := pCore_le_map_of_sylow_le S F hSF
  rw [hF, Subgroup.map_bot] at hc
  exact bot_unique hc

private theorem binaryLinear_simple {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hd : 3 ≤ Module.finrank (ZMod 2) W) :
    IsSimpleGroup (BinaryLinear.GL W) := by
  let n := Module.finrank (ZMod 2) W
  let e : W ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space n :=
    LinearEquiv.ofFinrankEq _ _ (by
      simp only [BinaryLinear.OuterCyclic.Space, Module.finrank_pi, Fintype.card_fin]
      rfl)
  let E : BinaryLinear.GL W ≃* BinaryLinear.OuterCyclic.LinearGroup n :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).symm.trans
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv e).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
          (BinaryLinear.OuterCyclic.Space n)))
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :=
    Atlas.psl_simple_high_rank n hd
  let : IsSimpleGroup (BinaryLinear.OuterCyclic.LinearGroup n) :=
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < n)).symm.isSimpleGroup
  exact E.isSimpleGroup

/-- The normalizer image is recognized first, and its normal L image is then
forced to be full. The comparison is proved, not an extra source premise. -/
theorem chosenJoinLinearAction_range_eq_top_of_pair_hyperplane
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (g : G)
    (hhyper : letI := D.elementary
      IsCoatom (pairAxisSpace V (V.map (MulAut.conj g).toMonoidHom))) :
    letI := D.elementary
    (chosenJoinLinearAction D (((structural L h).2.2 V D).1)).range = ⊤ := by
  let := D.elementary
  let hT := ((structural L h).2.2 V D).1
  let M := normalizer (L : Set G) ⊓ normalizer (V : Set G)
  let I := L ⊔ (T : Subgroup G)
  have hTM : (T : Subgroup G) ≤ M := le_inf (structural L h).1 hT
  have hLM : L ≤ M := le_inf L.le_normalizer D.normalizes
  have hIM : I ≤ M := sup_le hLM hTM
  let a : M →* BinaryLinear.GL (Additive V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive V)).toMonoidHom.comp
      (Representation.elementaryRepresentation
        (V.normalizerMonoidHom.comp (inclusion inf_le_right))).asGroupHom
  have happ (m : M) (v : Additive V) : ((a m v).toMul : G) =
      (m : G) * (v.toMul : G) * (m : G)⁻¹ := rfl
  have hJ : (I.subgroupOf M).map a = (chosenJoinLinearAction D hT).range := by
    ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨⟨i, hIM i.property⟩, i.property, rfl⟩
  have hcore : pCore 2 a.range = ⊥ := by
    apply image_twoCore_eq_bot_of_sylow (T.subtype hTM) (I.subgroupOf M)
      (fun t ht => (le_sup_right : (T : Subgroup G) ≤ I) ht) a
    rw [hJ]
    exact chosenJoinLinearAction_twoCore_eq_bot_at h D structural
  obtain ⟨f, hf, hker⟩ := pairAxisSpace_exists_form V _ hhyper
  have hneq : V.map (MulAut.conj g).toMonoidHom ≠ V := by
    intro he
    apply hf
    apply LinearMap.ext
    intro v
    apply (hker v).mpr
    rw [he]
    exact V.le_normalizer v.toMul.property
  let A := V.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hd := ((hTI.eq_or_disjoint_conjugate g).resolve_left hneq).symm
  have hB := pair_opposite_normalizer_le_component_normalizer hnone A hd
    (chosen_pair_axis_ne_bot h D A f hker)
  have hfull : BinaryLinear.radical f.ker ≤ a.range := by
    rw [← pairNormalizerLinearAction_range_eq_radical V A hd hTI (hTI.map_equiv _)
      (card_map_of_injective (MulAut.conj g).injective).symm f hf hker]
    rintro x ⟨b, rfl⟩
    exact ⟨⟨b, hB b.property, b.property.2⟩, rfl⟩
  have hR : a.range = ⊤ := ChapterG.Section03.eq_top_of_full_axis_of_twoCore_eq_bot
    hcore (chosen_finrank_ge_three h D) f hf hfull
  let K := (L.subgroupOf M).map a
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer inf_le_left
  let : K.Normal := Subgroup.Normal.map inferInstance a
    (MonoidHom.range_eq_top.mp hR)
  have hK : K ≠ ⊥ := by
    intro he
    apply D.centralAction_ne_one
    apply MonoidHom.ext
    intro l
    apply D.actionCentralizer_le_centralAction_ker
    intro v hv
    have ha : a ⟨l, hLM l.property⟩ = 1 := mem_bot.mp (he ▸
      (mem_map_of_mem a (show (⟨l, hLM l.property⟩ : M) ∈ L.subgroupOf M from l.property)))
    have hh := congrArg (fun e : BinaryLinear.GL (Additive V) =>
      ((e (Additive.ofMul ⟨v, hv⟩)).toMul : G)) ha
    change (l : G) * v * (l : G)⁻¹ = v at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  let : IsSimpleGroup (BinaryLinear.GL (Additive V)) :=
    binaryLinear_simple (chosen_finrank_ge_three h D)
  have hKtop : K = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal K inferInstance).resolve_left hK
  apply top_unique
  rw [← hKtop, ← hJ]
  exact map_mono (fun l hl => (le_sup_left : L ≤ I) hl)

/-- A literal hyperplane pair supplies the full axis in the original LT action. -/
theorem chosenFullAxis_of_pair_hyperplane
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (g : G)
    (hhyper : letI := D.elementary
      IsCoatom (pairAxisSpace V (V.map (MulAut.conj g).toMonoidHom))) :
    ChosenFullAxis D (((structural L h).2.2 V D).1) := by
  let := D.elementary
  obtain ⟨f, hf, _⟩ := pairAxisSpace_exists_form V _ hhyper
  refine ⟨f, hf, ?_⟩
  rw [chosenJoinLinearAction_range_eq_top_of_pair_hyperplane h D structural hnone hTI g hhyper]
  exact le_top

/-- The original natural-action consumer now needs just the remaining
hyperplane-pair construction and the independent quotient-action marking. -/
theorem natural_action_of_solvable_pair_hyperplane_and_marking
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : Group.IsSolvable H) (hm : ¬ V ≤ H.pCoreIn 2)
    (g : G)
    (hhyper : letI := D.elementary
      IsCoatom (pairAxisSpace V (V.map (MulAut.conj g).toMonoidHom)))
    (markingStep : (letI := D.elementary
      (chosenJoinLinearAction D (((structural L h).2.2 V D).1)).range = ⊤) →
      ∃ d, (3 ≤ d ∧ d ≤ 5) ∧ Nonempty (ChapterB.QuasisimpleSource.ActionEquiv D.quotientAction
        (Representation.specialLinearNatural (k := ZMod 2) d))) :
    ∃ d, (3 ≤ d ∧ d ≤ 5) ∧ Chapter6.Source.IsConjugationModel L V
      (Representation.specialLinearNatural (k := ZMod 2) d) := by
  exact natural_action_of_solvable_axis_and_marking h D structural hnone hTI hH hs hm
    (fun hnone hTI _ _ _ => chosenFullAxis_of_pair_hyperplane h D structural hnone hTI g hhyper)
    markingStep

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
