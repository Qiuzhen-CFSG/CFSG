module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.LocalGroups
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree
public import CFSG.Quasithin.ChapterB.Section01.IrreducibleSections
public import Mathlib.Order.OrderIsoNat
public import Theory.Representation.SimpleHeadQuotient
public import Theory.Representation.BinaryOffender.GeneratedCore
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.DimensionRatio

/-!
# Genuine chief-factor descent in the reducible B.5.1 branch

Choose a minimal best offender A of the original faithful module. B.1.5(3)
makes an actual Irr⁺ subspace I invariant under LA. Refine a chief flag through
I. Perfectness collapses any string of central factors, so noncentral factors
occur both below I and above it when [V,L] is not in Irr⁺. This constructs the
source's r > 1 rather than assuming it.

The complete set of noncentral indices carries the actual quotient actions.
Each factor is LA-irreducible, has strictly smaller binary dimension, and
contains a best offender in the image of A. The proved flag inequalities give
the full numerical conclusion (+), including its attained minimum at most 1/2.
No factor is assumed L-irreducible, natural or semisimple. Those structural
conclusions, and the later socle assembly, remain the next induction steps.

Source: Aschbacher--Smith, B.5.1, printed p.100, from the choice of A through (+).
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped BigOperators ENNReal
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion

private theorem saturated_chain {α : Type*} [PartialOrder α] [Finite α]
    {x y : α} (hxy : x ≤ y) :
    ∃ (c : ℕ → α) (n : ℕ), Monotone c ∧ c 0 = x ∧ c n = y ∧
      ∀ i < n, c i ⋖ c (i + 1) := by
  classical
  obtain ⟨a, ha0, n, han, ha⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le hxy
  let c : ℕ → α := fun i => a (min i n)
  have hc : Monotone c := by
    apply monotone_nat_of_le_succ
    intro i
    by_cases hi : i < n
    · simpa only [c, Nat.min_eq_left (Nat.le_of_lt hi), Nat.min_eq_left hi]
        using (ha i hi).le
    · simp only [c, Nat.min_eq_right (by omega : n ≤ i),
        Nat.min_eq_right (by omega : n ≤ i + 1), le_refl]
  refine ⟨c, n, hc, ?_, ?_, ?_⟩
  · simpa only [c, Nat.zero_min] using ha0
  · simpa only [c, Nat.min_self] using han
  · intro i hi
    simpa only [c, Nat.min_eq_left (Nat.le_of_lt hi), Nat.min_eq_left hi] using ha i hi

private theorem chief_flag_through {H X : Type*} [Group H] [AddCommGroup X]
    [Module (ZMod 2) X] [Finite X]
    (τ : Representation (ZMod 2) H X) (S : Subrepresentation τ) :
    ∃ (c : ℕ → Subrepresentation τ) (m n : ℕ),
      Monotone c ∧ c 0 = ⊥ ∧ c n = ⊤ ∧ c m = S ∧ m ≤ n ∧
        ∀ i < n, c i ⋖ c (i + 1) := by
  obtain ⟨a, m, ha, ha0, ham, hachief⟩ := saturated_chain (show ⊥ ≤ S from bot_le)
  obtain ⟨b, k, hb, hb0, hbk, hbchief⟩ := saturated_chain (show S ≤ ⊤ from le_top)
  let c : ℕ → Subrepresentation τ := fun i => if i < m then a i else b (i - m)
  have hleft (i : ℕ) (hi : i ≤ m) : c i = a i := by
    by_cases hil : i < m
    · simp [c, hil]
    · have he : i = m := by omega
      subst i
      simp [c, hb0, ham]
  have hright (i : ℕ) (hi : m ≤ i) : c i = b (i - m) := by simp [c, not_lt.mpr hi]
  have hchief (i : ℕ) (hi : i < m + k) : c i ⋖ c (i + 1) := by
    by_cases hil : i < m
    · rw [hleft i (by omega), hleft (i + 1) (by omega)]
      exact hachief i hil
    · rw [hright i (by omega), hright (i + 1) (by omega),
        show i + 1 - m = (i - m) + 1 by omega]
      exact hbchief (i - m) (by omega)
  have hc : Monotone c := by
    apply monotone_nat_of_le_succ
    intro i
    by_cases hi : i < m + k
    · exact (hchief i hi).le
    · rw [hright i (by omega), hright (i + 1) (by omega)]
      exact hb (by omega)
  refine ⟨c, m, m + k, hc, ?_, ?_, ?_, by omega, hchief⟩
  · rw [hleft 0 (by omega), ha0]
  · rw [hright (m + k) (by omega), Nat.add_sub_cancel_left, hbk]
  · rw [hright m le_rfl, Nat.sub_self, hb0]

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem commutator_le_of_central_flag_above
    (L : Subgroup G) [Group.IsPerfect L] (S : Subrepresentation ρ)
    (c : ℕ → Subrepresentation ρ) (n : ℕ) (hstart : c 0 ≤ S)
    (hcentral : ∀ i < n, ∀ l ∈ L, ∀ v,
      sectionRepresentation ρ (c i) (c (i + 1)) l v = v) :
    subspaceCommutator ρ (c n).toSubmodule L ≤ S.toSubmodule := by
  let d := fun i => S.quotientImage (c i)
  have hzero : d 0 = ⊥ := (Subrepresentation.quotientImage_eq_bot_iff S (c 0)).mpr hstart
  have hc : ∀ i < n, ∀ l ∈ L, ∀ v,
      sectionRepresentation S.quotientRepresentation (d i) (d (i + 1)) l v = v := by
    intro i hi l hl v
    apply (sectionRepresentation_trivial_iff S.quotientRepresentation (d i) (d (i + 1)) l).mpr
    rintro w ⟨x, hx, rfl⟩
    refine ⟨ρ l x - x,
      (sectionRepresentation_trivial_iff ρ (c i) (c (i + 1)) l).mp
        (hcentral i hi l hl) x hx, ?_⟩
    rw [Subrepresentation.quotientRepresentation_mk]
    exact (map_sub S.toSubmodule.mkQ (ρ l x) x).symm
  have hfixed := le_fixedSpace_of_central_flag S.quotientRepresentation L d hzero n hc
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, v, hv, rfl⟩
  have hmem : S.toSubmodule.mkQ v ∈ (d n).toSubmodule := ⟨v, hv, rfl⟩
  have hfix := hfixed hmem ⟨l, hl⟩
  exact (Submodule.Quotient.eq S.toSubmodule).mp hfix

private theorem section_central_of_commutator_eq_bot (U W : Subrepresentation ρ)
    (L : Subgroup G)
    (hz : subspaceCommutator (sectionRepresentation ρ U W) ⊤ L = ⊥) :
    ∀ l ∈ L, ∀ v, sectionRepresentation ρ U W l v = v := by
  intro l hl v
  exact (subspaceCommutator_eq_bot_iff _ ⊤ L).mp hz (by trivial) ⟨l, hl⟩

/-- A chief flag through a proper invariant Irr⁺ subspace has two distinct
noncentral factors. Neither factor is assumed irreducible on restriction to L. -/
private theorem chief_flag_two_noncentral [Finite V]
    (L : Subgroup G) [Group.IsPerfect L]
    (I : Subrepresentation ρ) (hI : IsIrrPlus ρ L I.toSubmodule)
    (hnot : ¬ IsIrrPlus ρ L (subspaceCommutator ρ ⊤ L)) :
    ∃ (c : ℕ → Subrepresentation ρ) (n : ℕ) (J : Finset ℕ),
      Monotone c ∧ c 0 = ⊥ ∧ c n = ⊤ ∧
      (∀ i < n, c i ⋖ c (i + 1)) ∧ J ⊆ Finset.range n ∧ 1 < J.card ∧
      ∀ i ∈ J, subspaceCommutator (sectionRepresentation ρ (c i) (c (i + 1))) ⊤ L ≠ ⊥ := by
  classical
  obtain ⟨c, m, n, hc, hzero, htop, hm, hmn, hchief⟩ := chief_flag_through ρ I
  have hex1 : ∃ i < m,
      subspaceCommutator (sectionRepresentation ρ (c i) (c (i + 1))) ⊤ L ≠ ⊥ := by
    by_contra! hh
    have hfix := le_fixedSpace_of_central_flag ρ L c hzero m
      (fun i hi => section_central_of_commutator_eq_bot ρ _ _ L (hh i hi))
    rw [hm] at hfix
    exact hI.not_le_fixedSpace ρ hfix
  have hex2 : ∃ j, m ≤ j ∧ j < n ∧
      subspaceCommutator (sectionRepresentation ρ (c j) (c (j + 1))) ⊤ L ≠ ⊥ := by
    by_contra! hh
    have hle := commutator_le_of_central_flag_above ρ L I
      (fun i => c (m + i)) (n - m) (by simp [hm]) (by
        intro i hi
        apply section_central_of_commutator_eq_bot ρ _ _ L
        exact hh (m + i) (by omega) (by omega))
    have hind : m + (n - m) = n := by omega
    simp only [hind, htop] at hle
    have hrev : I.toSubmodule ≤ subspaceCommutator ρ ⊤ L := by
      rw [← hI.choose_spec.1]
      exact subspaceCommutator_mono_left ρ le_top L
    exact hnot ((le_antisymm hle hrev).symm ▸ hI)
  obtain ⟨i, hi, hinc⟩ := hex1
  obtain ⟨j, hmj, hj, hjnc⟩ := hex2
  refine ⟨c, n, {i, j}, hc, hzero, htop, hchief, ?_, ?_, ?_⟩
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
  · simp [show i ≠ j by omega]
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hinc
    · exact hjnc



/-- The literal chief flag and its complete set of noncentral indices. -/
structure ReducibleChiefFlag (L : Subgroup G) where
  chain : ℕ → Subrepresentation ρ
  length : ℕ
  monotone : Monotone chain
  bottom : chain 0 = ⊥
  top : chain length = ⊤
  chief : ∀ i < length, chain i ⋖ chain (i + 1)
  noncentral : Finset ℕ
  mem_noncentral : ∀ i, i ∈ noncentral ↔ i < length ∧
    subspaceCommutator (sectionRepresentation ρ (chain i) (chain (i + 1))) ⊤ L ≠ ⊥
  multiple : 1 < noncentral.card

private theorem reducibleChiefFlag_of_invariant_IrrPlus [Finite V]
    (L : Subgroup G) [Group.IsPerfect L]
    (I : Subrepresentation ρ) (hI : IsIrrPlus ρ L I.toSubmodule)
    (hnot : ¬ IsIrrPlus ρ L (subspaceCommutator ρ ⊤ L)) :
    Nonempty (ReducibleChiefFlag ρ L) := by
  classical
  obtain ⟨c, n, J, hc, hzero, htop, hchief, hJn, hJcard, hJncentral⟩ :=
    chief_flag_two_noncentral ρ L I hI hnot
  let S := (Finset.range n).filter (fun i =>
    subspaceCommutator (sectionRepresentation ρ (c i) (c (i + 1))) ⊤ L ≠ ⊥)
  have hJS : J ⊆ S := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨hJn hi, hJncentral i hi⟩
  refine ⟨⟨c, n, hc, hzero, htop, hchief, S, ?_, hJcard.trans_le (Finset.card_le_card hJS)⟩⟩
  intro i
  simp [S]

private theorem chief_section_irreducible {U W : Subrepresentation ρ} (h : U ⋖ W) :
    IsIrreducible (sectionRepresentation ρ U W) := by
  apply SimpleHeadQuotient.irreducible_quotient_of_isCoatom
  refine ⟨?_, ?_⟩
  · intro he
    have hWU : W ≤ U := by
      intro v hv
      have hm : (⟨v, hv⟩ : W.toSubmodule) ∈ sectionLower ρ U W := by rw [he]; trivial
      exact hm
    exact (not_le_of_gt h.lt) hWU
  · intro P hP
    let T : Subrepresentation ρ := {
      toSubmodule := P.toSubmodule.map W.toSubmodule.subtype
      apply_mem_toSubmodule g := by
        rintro _ ⟨v, hv, rfl⟩
        exact ⟨W.toRepresentation g v, P.apply_mem_toSubmodule g hv, rfl⟩ }
    have hUT : U ≤ T := by
      intro v hv
      exact ⟨⟨v, h.le hv⟩, hP.le hv, rfl⟩
    have hTW : T ≤ W := Submodule.map_subtype_le _ _
    rcases h.eq_or_eq hUT hTW with ht | ht
    · have hPN : P ≤ sectionLower ρ U W := by
        intro v hv
        have : v.val ∈ T := ⟨v, hv, rfl⟩
        rw [ht] at this
        exact this
      exact ((not_le_of_gt hP) hPN).elim
    · apply Subrepresentation.toSubmodule_injective
      apply top_unique
      intro v _
      have : v.val ∈ T := by rw [ht]; exact v.property
      obtain ⟨w, hw, he⟩ := this
      exact (Subtype.ext he : w = v) ▸ hw

/-- Each flag factor is irreducible for its actual ambient group. -/
theorem ReducibleChiefFlag.irreducible {L : Subgroup G} (f : ReducibleChiefFlag ρ L)
    {i : ℕ} (hi : i < f.length) :
    IsIrreducible (sectionRepresentation ρ (f.chain i) (f.chain (i + 1))) :=
  chief_section_irreducible ρ (f.chief i hi)

/-- The flag supplies dimension descent and the complete B.5.1 (+) budget. -/
theorem ReducibleChiefFlag.estimates [Finite G] [FiniteDimensional (ZMod 2) V]
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (hfaith : Function.Injective ρ) (hL : IsQuasisimple (generalizedFitting G))
    (hcore : pCore 2 G = ⊥) (A : Subgroup G) (hA : IsMinimalBestOffender ρ A) :
    let q := fun i => quadraticRatio
      (imageRepresentation (sectionRepresentation ρ (f.chain i) (f.chain (i + 1))))
    (∀ i ∈ f.noncentral, sectionDimension ρ (f.chain i) (f.chain (i + 1)) <
      Module.finrank (ZMod 2) V) ∧
    (∑ i ∈ f.noncentral, q i ≤ 1) ∧
    (∀ i ∈ f.noncentral, 0 < q i ∧ q i < 1) ∧
    (∀ i ∈ f.noncentral, ∀ j ∈ f.noncentral, i ≠ j → q i + q j ≤ 1) ∧
    ∃ k ∈ f.noncentral, (∀ i ∈ f.noncentral, q k ≤ q i) ∧
      q k ≤ 1 / (f.noncentral.card : ℝ≥0∞) ∧ 1 / (f.noncentral.card : ℝ≥0∞) ≤ 1 / 2 := by
  exact quasisimple_flag_estimates ρ hfaith hL hcore f.chain f.monotone f.length
    f.noncentral (fun i hi => Finset.mem_range.mpr ((f.mem_noncentral i).mp hi).1)
    f.multiple A hA (fun i hi => ((f.mem_noncentral i).mp hi).2)

private theorem minimal_subgroupOf {A H : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hAH : A ≤ H) : IsMinimalBestOffender (ρ.comp H.subtype) (A.subgroupOf H) := by
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

/-- The actual LA-chief flag in the reducible B.5.1 branch. Its two or more
noncentral factors are constructed from the source hypotheses. -/
theorem reducible_source_flag [Finite G]
    {K : GroupClass} {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (hnot : ¬ IsIrrPlus ρ L (moved ρ L)) :
    ∃ A : Subgroup G, IsMinimalBestOffender ρ A ∧
      Nonempty (ReducibleChiefFlag (ρ.comp (L ⊔ A).subtype)
        (generalizedFitting ↥(L ⊔ A))) := by
  classical
  let := h.finite_module
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  obtain ⟨B, hB⟩ := ExtensionConsequences.source_isFF h
  obtain ⟨B', _, hB'⟩ := hB.exists_bestOffender ρ
  obtain ⟨A, hA, _⟩ := hB'.exists_minimal ρ
  refine ⟨A, hA, ?_⟩
  let H := L ⊔ A
  let σ := ρ.comp H.subtype
  let L₀ := L.subgroupOf H
  let A₀ := A.subgroupOf H
  have hLA : L₀ ⊔ A₀ = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup]
    change (L.subgroupOf H).map H.subtype ⊔ (A.subgroupOf H).map H.subtype =
      (⊤ : Subgroup H).map H.subtype
    rw [map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left),
      map_subgroupOf_eq_of_le (show A ≤ H from le_sup_right)]
    exact H.range_subtype.symm.trans H.subtype.range_eq_map
  have hA₀ : IsMinimalBestOffender σ A₀ := minimal_subgroupOf ρ hA le_sup_right
  have hp : IsPGroup 2 A := hA.1.1.2.isPGroup 2 A
  have hp₀ : IsPGroup 2 A₀ := hA₀.1.1.2.isPGroup 2 A₀
  have hfit : generalizedFitting H = L₀ :=
    IrreducibleBranch.local_generalizedFitting L A h.fitting h.twoCore hp
  have hcore : pCore 2 H = ⊥ :=
    IrreducibleBranch.local_twoCore_eq_bot L H h.fitting h.twoCore le_sup_left
  let : IsQuasisimple L₀ :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).symm
  have hquasi : IsQuasisimple (generalizedFitting H) := hfit.symm ▸ inferInstance
  have hcomm : ⁅L₀, A₀⁆ = L₀ := by
    simpa only [hfit] using QuasisimpleSections.commutator_fitting_eq hcore hquasi hA₀.1.1.1 hp₀
  have hr : pResidual 2 L₀ = ⊤ := by
    apply (pResidual_eq_top_iff 2 L₀).mpr
    intro N hN hpN
    let := hN
    have hsub : Subsingleton (L₀ ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (L₀ ⧸ N) hpN.isNilpotent
    apply top_unique
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
  have hchief : HasCentralPChiefFactors 2 L₀ :=
    hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient
      (⊥ : Subgroup L₀) (by simp)
      (IsQuasisimple.of_mulEquiv QuotientGroup.quotientBot.symm)
  let : IsSimpleGroup (L₀ ⧸ center L₀) := IsQuasisimple.simple
  let : Nontrivial L₀ := (QuotientGroup.mk'_surjective (center L₀)).nontrivial
  have hfaith : Function.Injective σ := h.faithful.comp H.subtype_injective
  obtain ⟨I, hI⟩ := exists_isIrrPlus_of_faithful σ hfaith L₀
    ((nontrivial_iff_ne_bot L₀).mp inferInstance)
  have hAI := source_lemma_B_1_5_3 σ hfaith hA₀ hr hcomm hchief hI
  have hstable : (⊤ : Subgroup H) ≤ subspaceStabilizer σ I := by
    rw [← hLA]
    exact sup_le hI.choose hAI
  let Irep : Subrepresentation σ := ⟨I, fun g v hv => (hstable (Subgroup.mem_top g) v).2 hv⟩
  have hmov : subspaceCommutator σ ⊤ L₀ = moved ρ L := by
    unfold subspaceCommutator moved
    congr 1
    ext v
    constructor
    · rintro ⟨l, hl, w, hw, rfl⟩
      exact ⟨l.val, hl, w, hw, rfl⟩
    · rintro ⟨l, hl, w, hw, rfl⟩
      exact ⟨⟨l, (show L ≤ H from le_sup_left) hl⟩, hl, w, hw, rfl⟩
  have hnot₀ : ¬ IsIrrPlus σ L₀ (subspaceCommutator σ ⊤ L₀) := by
    intro hi
    rw [hmov] at hi
    exact hnot ((IsIrrPlus.subgroupOf_iff ρ L H le_sup_left _).mp hi)
  have hout := reducibleChiefFlag_of_invariant_IrrPlus σ L₀ Irep hI hnot₀
  change Nonempty (ReducibleChiefFlag σ (generalizedFitting H))
  rw [hfit]
  exact hout



/-- Source-facing dimension reduction on the actual LA chief sections.
Every selected image contains a best offender from the original actor, and
the complete set of noncentral factors has the source's total ratio budget. -/
theorem reducible_source_reduction [Finite G]
    {K : GroupClass} {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (hnot : ¬ IsIrrPlus ρ L (moved ρ L)) :
    ∃ A : Subgroup G, IsMinimalBestOffender ρ A ∧
      ∃ f : ReducibleChiefFlag (ρ.comp (L ⊔ A).subtype) (generalizedFitting ↥(L ⊔ A)),
        let σ := ρ.comp (L ⊔ A).subtype
        let q := fun i => quadraticRatio
          (imageRepresentation (sectionRepresentation σ (f.chain i) (f.chain (i + 1))))
        (∀ i ∈ f.noncentral,
          sectionDimension σ (f.chain i) (f.chain (i + 1)) < Module.finrank (ZMod 2) V ∧
          ∃ B ≤ actionSubgroup (sectionRepresentation σ (f.chain i) (f.chain (i + 1)))
            (A.subgroupOf (L ⊔ A)),
            IsBestOffender (imageRepresentation
              (sectionRepresentation σ (f.chain i) (f.chain (i + 1)))) B) ∧
        (∑ i ∈ f.noncentral, q i ≤ 1) ∧
        (∀ i ∈ f.noncentral, 0 < q i ∧ q i < 1) ∧
        (∀ i ∈ f.noncentral, ∀ j ∈ f.noncentral, i ≠ j → q i + q j ≤ 1) ∧
        ∃ k ∈ f.noncentral, (∀ i ∈ f.noncentral, q k ≤ q i) ∧
          q k ≤ 1 / (f.noncentral.card : ℝ≥0∞) ∧
          1 / (f.noncentral.card : ℝ≥0∞) ≤ 1 / 2 := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  obtain ⟨A, hA, ⟨f⟩⟩ := reducible_source_flag ρ h hnot
  let H := L ⊔ A
  let σ := ρ.comp H.subtype
  have hA₀ := minimal_subgroupOf ρ hA (show A ≤ H from le_sup_right)
  have hp : IsPGroup 2 A := hA.1.1.2.isPGroup 2 A
  have hfit : generalizedFitting H = L.subgroupOf H :=
    IrreducibleBranch.local_generalizedFitting L A h.fitting h.twoCore hp
  have hcore : pCore 2 H = ⊥ :=
    IrreducibleBranch.local_twoCore_eq_bot L H h.fitting h.twoCore le_sup_left
  let : IsQuasisimple (L.subgroupOf H) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).symm
  have hquasi : IsQuasisimple (generalizedFitting H) := hfit.symm ▸ inferInstance
  have hfaith : Function.Injective σ := h.faithful.comp H.subtype_injective
  obtain ⟨hd, hs, hv, hpairs, hmin⟩ := f.estimates σ hfaith hquasi hcore _ hA₀
  refine ⟨A, hA, f, ?_, hs, hv, hpairs, hmin⟩
  intro i hi
  exact ⟨hd i hi, (source_lemma_B_1_5_8 σ hfaith hA₀.1 hquasi hcore
    (f.chief i ((f.mem_noncentral i).mp hi).1).le
    ((f.mem_noncentral i).mp hi).2).2.2.1⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
