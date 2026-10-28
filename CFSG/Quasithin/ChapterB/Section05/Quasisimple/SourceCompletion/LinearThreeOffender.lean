module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeCohomology
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LocalMoved

/-!
# The original SL3 offender lies in the component

The two noncentral natural chief factors each require at least half of the
same original offender's rank. The flag codimension inequality forces exact
half ratio on each factor. A quadratic subgroup attaining this lower bound
is best, by comparison with every subgroup and the weight formula.

Full B.4.2 on the actual faithful chief action now places this offender
inside the component. Thus the selected local actor LA is L, and the original
component restriction itself is an FF-module. This source deduction uses no
semisimplicity or central-factor splitting of the original moved module.

Source: Aschbacher--Smith, B.5.1, printed p.101, assertions (a)--(c).
-/

public section
open Representation Representation.BinaryOffender Theory.GroupTheory Subgroup
open scoped ENNReal MatrixGroups IsMulCommutative BigOperators
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

omit [FiniteDimensional (ZMod 2) V] in
private theorem rank_le_twice_codim (hlo : (1/2 : ℝ≥0∞) ≤ quadraticRatio ρ)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A) :
    rank A ≤ 2 * fixedCodim ρ A := by
  have hl := hlo.trans (iInf_le_of_le A (iInf_le_of_le ⟨hA,hq⟩ le_rfl))
  have ht : actionRatio ρ A ≠ ⊤ := ENNReal.div_ne_top (by simp)
    (by exact_mod_cast Nat.ne_of_gt hA.rank_pos)
  have hh := ENNReal.toReal_mono ht hl
  simp only [actionRatio,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast] at hh
  have hp : (0 : ℝ) < rank A := by exact_mod_cast hA.rank_pos
  have hh := (le_div_iff₀ hp).mp hh
  exact_mod_cast (show (rank A : ℝ) ≤ 2 * fixedCodim ρ A by linarith)

/-- An actual quadratic subgroup attaining the half-ratio lower bound is best. -/
theorem bestOffender_of_half_bound (hlo : (1/2 : ℝ≥0∞) ≤ quadraticRatio ρ)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hhi : actionRatio ρ A ≤ 1/2) : IsBestOffender ρ A := by
  have ha := rank_le_twice_codim ρ hlo hA hq
  have hh := ENNReal.toReal_mono (by norm_num : (1/2 : ℝ≥0∞) ≠ ⊤) hhi
  simp only [actionRatio,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast] at hh
  have hp : (0 : ℝ) < rank A := by exact_mod_cast hA.rank_pos
  have hh := (div_le_iff₀ hp).mp hh
  have hau : 2 * fixedCodim ρ A ≤ rank A := by
    exact_mod_cast (show (2 : ℝ) * fixedCodim ρ A ≤ rank A by linarith)
  refine ⟨hA,fun D hD => ?_⟩
  have hd : rank D ≤ 2 * fixedCodim ρ D := by
    by_cases hz : D = ⊥
    · simp [hz,rank]
    · have he : IsElementaryTwo D := hA.of_le hD hz
      exact rank_le_twice_codim ρ hlo he (fun a ha b hb v => hq a (hD ha) b (hD hb) v)
  have hr : rank D ≤ rank A := Nat.log_mono_right (Subgroup.card_le_of_le hD)
  have hda := fixedCodim_add_finrank ρ A
  have hdd := fixedCodim_add_finrank ρ D
  unfold weight
  omega

/-- In the actual SL3 flag, the original minimal offender attains half ratio
on every noncentral factor. This keeps the common subgroup throughout. -/
theorem linearThree_flag_action_half
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hfaith : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (hp : IsPGroup 2 (G ⧸ generalizedFitting G))
    (F : BinaryField) (mark : generalizedFitting G ≃* SL(3,F.Carrier))
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A)
    (hgen : generalizedFitting G ⊔ A = ⊤) :
    ∀ i ∈ f.noncentral,
      actionRatio (sectionRepresentation ρ (f.chain i) (f.chain (i+1))) A = 1/2 ∧
      IsBestOffender (sectionRepresentation ρ (f.chain i) (f.chain (i+1))) A := by
  let τ := fun i => sectionRepresentation ρ (f.chain i) (f.chain (i+1))
  have hlo (i : ℕ) (hi : i ∈ f.noncentral) : (1/2 : ℝ≥0∞) ≤ quadraticRatio (τ i) := by
    have hf := (linearThree_flag_natural ρ hK hsemisimple h36 earlier hsq hfaith hcore hp
      F mark f A hA hgen i hi).1
    rw [← image_ratio_of_faithful (τ i) hf]
    exact linearThree_flag_ratio_lower ρ hK hsemisimple h36 earlier hsq hcore hp F mark f hi
  have hq (i : ℕ) : IsQuadratic (τ i) A := quadratic_section ρ (f.chain i) (f.chain (i+1)) (hA.isQuadratic ρ)
  have hl (i : ℕ) (hi : i ∈ f.noncentral) : (1/2 : ℝ≥0∞) ≤ actionRatio (τ i) A :=
    (hlo i hi).trans (iInf_le_of_le A (iInf_le_of_le ⟨hA.1.1,hq i⟩ le_rfl))
  intro i hi
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp f.multiple
  obtain ⟨j,hj,hij⟩ : ∃ j ∈ f.noncentral, i ≠ j := by
    by_cases hia : i = a
    · exact ⟨b,hb,hia ▸ hab⟩
    · exact ⟨a,ha,hia⟩
  have hpair : actionRatio (τ i) A + actionRatio (τ j) A ≤ 1 := by
    have hs : ({i,j} : Finset ℕ) ⊆ Finset.range f.length := by
      intro k hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with hk | hk
      · rw [hk]; exact Finset.mem_range.mpr ((f.mem_noncentral i).mp hi).1
      · rw [hk]; exact Finset.mem_range.mpr ((f.mem_noncentral j).mp hj).1
    calc
      _ = ∑ k ∈ ({i,j} : Finset ℕ), actionRatio (τ k) A := by simp [hij]
      _ ≤ ∑ k ∈ Finset.range f.length, actionRatio (τ k) A :=
        Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => zero_le)
      _ ≤ actionRatio ρ A := sum_actionRatio_flag_le ρ f.chain f.monotone f.length A
      _ ≤ 1 := (actionRatio_le_one_iff ρ hA.1.1).mpr (hA.1.isOffender ρ).2
  have htop (k : ℕ) : actionRatio (τ k) A ≠ ⊤ := ENNReal.div_ne_top (by simp)
    (by exact_mod_cast Nat.ne_of_gt hA.1.1.rank_pos)
  have hp' := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hpair
  rw [ENNReal.toReal_add (htop i) (htop j)] at hp'
  have hl' := ENNReal.toReal_mono (htop j) (hl j hj)
  have hhi : actionRatio (τ i) A ≤ 1/2 := by
    apply (ENNReal.toReal_le_toReal (htop i) (by norm_num)).mp
    norm_num [ENNReal.toReal_div] at hp' hl' ⊢
    linarith
  exact ⟨le_antisymm hhi (hl i hi),bestOffender_of_half_bound (τ i) (hlo i hi) hA.1.1 (hq i) hhi⟩

/-- The common half-ratio offender is inside the actual component. Thus
an LA source actor with an SL3 chief flag equals its generalized Fitting subgroup. -/
theorem linearThree_flag_actor_whole
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hfaith : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (hp : IsPGroup 2 (G ⧸ generalizedFitting G))
    (F : BinaryField) (mark : generalizedFitting G ≃* SL(3,F.Carrier))
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A)
    (hgen : generalizedFitting G ⊔ A = ⊤) : generalizedFitting G = ⊤ := by
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < f.noncentral.card from lt_trans Nat.zero_lt_one f.multiple)
  let τ := sectionRepresentation ρ (f.chain i) (f.chain (i+1))
  obtain ⟨hf,hirr,_⟩ := linearThree_flag_natural ρ hK hsemisimple h36 earlier hsq hfaith hcore hp
    F mark f A hA hgen i hi
  have hb := (linearThree_flag_action_half ρ hK hsemisimple h36 earlier hsq hfaith hcore hp
    F mark f A hA hgen i hi).2
  have hsqG : IsSQTK K G := (IsSQTK.equiv
    ((MulEquiv.subgroupCongr hgen).trans (topEquiv : (⊤ : Subgroup G) ≃* G))).mp
      (IrreducibleBranch.local_sqtk hK (generalizedFitting G) A hsq (hA.1.1.2.isPGroup 2 A))
  have hc := earlier G _ τ hsqG inferInstance hf hirr ⟨A,hb⟩
  have hhalf : quadraticRatio τ ≤ 1/2 := by
    rw [← image_ratio_of_faithful τ hf]
    exact linearThree_flag_ratio_bound ρ hK hsemisimple h36 earlier hsq hfaith hcore hp
      F mark f A hA hi
  have hgenerated := generated_of_half τ hc hhalf
  have hAC : A ≤ generalizedFitting G := (hb.le_offenderSubgroup τ).trans_eq hgenerated
  simpa only [sup_of_le_left hAC] using hgen

/-- The original reducible SL3 source has an actual minimal best offender
inside L. Hence its component restriction, not just a chief image, is FF. -/
theorem linearThree_component_offender
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (hnot : ¬ IsIrrPlus ρ L (moved ρ L))
    (F : BinaryField) (mark : L ≃* SL(3,F.Carrier)) :
    ∃ A : Subgroup G, IsMinimalBestOffender ρ A ∧ A ≤ L := by
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  obtain ⟨A,hA,⟨f⟩⟩ := reducible_source_flag ρ h hnot
  let H := L ⊔ A
  let σ := ρ.comp H.subtype
  have hp : IsPGroup 2 A := hA.1.1.2.isPGroup 2 A
  have hfit : generalizedFitting H = L.subgroupOf H :=
    IrreducibleBranch.local_generalizedFitting L A h.fitting h.twoCore hp
  let : IsQuasisimple (L.subgroupOf H) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).symm
  let : IsQuasisimple (generalizedFitting H) := hfit.symm ▸ inferInstance
  have hsq : IsSQTK K (generalizedFitting H) := by
    rw [hfit]
    exact (IsSQTK.equiv (subgroupOfEquivOfLe (show L ≤ H from le_sup_left))).mpr h.sqtk
  have hq : IsPGroup 2 (H ⧸ generalizedFitting H) :=
    (IrreducibleBranch.local_quotient_isTwoGroup L A hp).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hfit.symm)
  have hcore : pCore 2 H = ⊥ :=
    IrreducibleBranch.local_twoCore_eq_bot L H h.fitting h.twoCore le_sup_left
  let e := (MulEquiv.subgroupCongr hfit).trans
    ((subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).trans mark)
  have hAH : A ≤ H := le_sup_right
  have hmin : IsMinimalBestOffender σ (A.subgroupOf H) := by
    refine ⟨hA.1.subgroupOf ρ hAH, ?_⟩
    intro B hB hBA
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hAH]
    apply hA.2 _ (hB.map_subtype ρ)
    refine ⟨(map_mono hBA.1).trans_eq (map_subgroupOf_eq_of_le hAH), ?_⟩
    have hw := hBA.2
    rw [weight_comp_map ρ H.subtype H.subtype_injective,
      weight_comp_map ρ H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hAH] at hw
    exact hw
  have hgen : generalizedFitting H ⊔ A.subgroupOf H = ⊤ := by
    rw [hfit]
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left),
      map_subgroupOf_eq_of_le hAH]
    exact H.range_subtype.symm.trans H.subtype.range_eq_map
  have hw := linearThree_flag_actor_whole σ hK hsemisimple h36 earlier hsq
    (h.faithful.comp H.subtype_injective) hcore hq F e f (A.subgroupOf H) hmin hgen
  refine ⟨A,hA,fun a ha => ?_⟩
  have hm : (⟨a,hAH ha⟩ : H) ∈ generalizedFitting H := hw ▸ Subgroup.mem_top _
  rw [hfit] at hm
  exact hm

/-- The component action itself is FF in the reducible SL3 source branch. -/
theorem linearThree_component_isFF
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (hnot : ¬ IsIrrPlus ρ L (moved ρ L))
    (F : BinaryField) (mark : L ≃* SL(3,F.Carrier)) : IsFFModule (ρ.comp L.subtype) := by
  obtain ⟨A,hA,hAL⟩ := linearThree_component_offender ρ hK hsemisimple h36 earlier h hnot F mark
  exact ⟨A.subgroupOf L,(hA.1.isOffender ρ).subgroupOf ρ hAL⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
