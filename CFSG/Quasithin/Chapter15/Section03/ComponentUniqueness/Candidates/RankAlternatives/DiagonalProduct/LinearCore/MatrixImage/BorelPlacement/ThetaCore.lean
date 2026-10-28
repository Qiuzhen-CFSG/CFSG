module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.MatrixImage.BorelPlacement.Orientation
public import Theory.GroupTheory.PerfectCentralSupplement
public import Theory.SpecificGroups.PSL3.CubicBorel.OuterParameter
public import Theory.SpecificGroups.PSL3.CubicBorel.Roots
public import Theory.SpecificGroups.PSL3.CubicBorel.ThetaQuotient
public import Theory.GroupTheory.SolvableResidual.Transport

/-!
# The theta-core of the actual Borel, including central two-covers

Cubic diagonal elements generate all three positive roots for every even
field degree. Sylow conjugacy puts the specified projective Sylow in the
theta subgroup of its normalizer. Cubic elements lift through a two-kernel.
For a perfect central cover, transfer then absorbs the full central kernel:
theta of the Borel preimage is the full preimage of projective theta.
Its normal Sylow subgroup is therefore exactly its two-core.

The core identity is proved here for every positive even exponent. The outer
cubic actor preserves the original Sylow by the explicit local stability
hypothesis, so its field degree is prime to three. The intrinsic projective
theta quotient then has order three, and transport through the actual marking
gives the same order for the central cover. These calculations discharge both
theta premises of the oriented-plane construction. Local stability remains
explicit; neither ambient product generation nor an n = 2 assumption is used.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.11--12,
15.3.33 and the proof of 15.3.38, printed pp.1123--1125 and 1134--1136.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceBorel

variable {J D : Type*} [Group J] [Group D] [Finite J]

/-- Cubic lifting and transfer retain the whole central two-kernel of a perfect cover. -/
theorem theta_preimage_eq_of_central_kernel [Group.IsPerfect J]
    (f : J →* D) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hz : f.ker ≤ center J)
    (P : Sylow 2 D) (hgen : (P : Subgroup D) ≤ theta (normalizer (P : Set D))) :
    theta ((normalizer (P : Set D)).comap f) =
      (theta (normalizer (P : Set D))).comap f := by
  let A := theta ((normalizer (P : Set D)).comap f)
  have hm : A.map f = theta (normalizer (P : Set D)) := by
    rw [FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.theta_map_of_twoGroup_ker f hk,
      map_comap_eq_self (by intro x _; exact hf x)]
  have he : (theta (normalizer (P : Set D))).comap f = A ⊔ f.ker := by
    rw [← hm, comap_map_eq]
  let Q := P.comapOfKerIsPGroup f hk (by rw [f.range_eq_top_of_surjective hf]; exact le_top)
  have hQ : (Q : Subgroup J) ≤ A ⊔ f.ker := by
    rw [← he]
    exact comap_mono hgen
  have hi : ¬ 2 ∣ (A ⊔ f.ker).index := fun hh =>
    Q.not_dvd_index (hh.trans (index_dvd_of_le hQ))
  rw [he, sup_central_pSubgroup_eq A f.ker hz hk hi]

/-- The full lifted Sylow is the intrinsic theta-core, with no splitting premise. -/
theorem theta_preimage_core [Group.IsPerfect J]
    (f : J →* D) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hz : f.ker ≤ center J)
    (P : Sylow 2 D) (hgen : (P : Subgroup D) ≤ theta (normalizer (P : Set D))) :
    (theta ((normalizer (P : Set D)).comap f)).pCoreIn 2 = (P : Subgroup D).comap f := by
  let A := theta ((normalizer (P : Set D)).comap f)
  let Q := P.comapOfKerIsPGroup f hk (by rw [f.range_eq_top_of_surjective hf]; exact le_top)
  have hQA : (Q : Subgroup J) ≤ A := by
    dsimp only [A]
    rw [theta_preimage_eq_of_central_kernel f hf hk hz P hgen]
    exact comap_mono hgen
  have hAN : A ≤ normalizer (Q : Set J) := by
    change A ≤ normalizer ((P : Subgroup D).comap f : Set J)
    rw [← comap_normalizer_eq_of_surjective _ hf]
    exact theta_le _
  apply le_antisymm
  · have hh := pCoreIn_le_sylow A (Q.subtype hQA)
    exact hh.trans_eq (map_subgroupOf_eq_of_le hQA)
  · exact le_pCoreIn_of_normalizes Q.isPGroup' hQA hAN

/-- The quotient by the two-core is unchanged on pulling back through a two-kernel. -/
theorem theta_preimage_quotient_card [Finite D]
    (f : J →* D) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (B : Subgroup D) :
    Nat.card (theta (B.comap f) ⧸ pCore 2 (theta (B.comap f))) =
      Nat.card (theta B ⧸ pCore 2 (theta B)) := by
  let A := theta (B.comap f)
  have hm : A.map f = theta B := by
    rw [FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.theta_map_of_twoGroup_ker f hk,
      map_comap_eq_self (by intro x _; exact hf x)]
  have hk' : IsPGroup 2 (f.subgroupMap A).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  have hc := Nat.card_congr ((f.subgroupMap A).pCoreQuotientEquiv
    (f.subgroupMap_surjective A) hk').toEquiv
  rw [hm] at hc
  exact hc

/-- Cubic root generation for every even degree, transported to the specified Sylow. -/
theorem sylow_le_theta_normalizer {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hn : 0 < n) (heven : Even n) (hF : Nat.card F = 2 ^ n)
    (P : Sylow 2 PSL(3,F)) :
    (P : Subgroup PSL(3,F)) ≤ theta (normalizer (P : Set PSL(3,F))) := by
  obtain ⟨g, hP, hB⟩ := Matrix.PSL3.CartanActions.BorelQuotient.sylow_normalizer_conjugate F hn hF P
  rw [← hB, ← theta_map_of_injective _ (MulAut.conj g).injective, ← hP]
  exact map_mono (Matrix.PSL3.CubicBorel.unipotent_le_cubicClosure F heven hF)

variable {G : Type*} [Group G] [Finite G]
variable {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}

/-- The actual Borel theta-core is S ∩ L for every positive even field degree.
This includes the genuine central two-cover over the field of order four. -/
theorem theta_borel_core (h : Setup d I L) (e : Earlier d)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n)) :
    (theta (borel d.S L)).pCoreIn 2 = d.S ⊓ L := by
  let := h.perfect
  obtain ⟨P, hP, hpre⟩ := h.projective_sylow e c
  have hz : (projectiveMap c).ker ≤ center L := by
    rw [projectiveMap_ker]
    exact h.core_central e
  have hk : IsPGroup 2 (projectiveMap c).ker := by
    rw [projectiveMap_ker]
    exact pCore_isPGroup
  have hc := theta_preimage_core (projectiveMap c) (projectiveMap_surjective c) hk hz P
    (sylow_le_theta_normalizer hn heven c.card P)
  rw [borel_eq_projectivePreimage c P hpre]
  change (theta (((normalizer (P : Set PSL(3,c.F))).comap (projectiveMap c)).map L.subtype)).pCoreIn 2 = _
  rw [← theta_map_of_injective _ L.subtype_injective,
    ← map_pCoreIn_of_ker_isPGroup L.subtype (by
      rw [L.ker_subtype]
      exact IsPGroup.of_bot)]
  rw [hc]
  exact hpre

/-- Reduce the actual quotient order to the projective normalizer through the same marking. -/
theorem theta_borel_quotient_card_eq_projective {n : ℕ}
    (c : ProjectiveMarking L (2 ^ n)) (P : Sylow 2 PSL(3,c.F))
    (hpre : projectivePreimage c P = d.S ⊓ L) :
    Nat.card (theta (borel d.S L) ⧸ pCore 2 (theta (borel d.S L))) =
      Nat.card (theta (normalizer (P : Set PSL(3,c.F))) ⧸
        pCore 2 (theta (normalizer (P : Set PSL(3,c.F))))) := by
  rw [borel_eq_projectivePreimage c P hpre]
  let A := theta ((normalizer (P : Set PSL(3,c.F))).comap (projectiveMap c))
  have hm : A.map L.subtype = theta (projectivePreimage c (normalizer (P : Set PSL(3,c.F)))) :=
    theta_map_of_injective L.subtype L.subtype_injective _
  have hk : IsPGroup 2 (L.subtype.subgroupMap A).ker := by
    rw [ker_subgroupMap]
    exact (IsPGroup.ker_isPGroup_of_injective (p := 2) L.subtype_injective).comap_subtype
  have hi := Nat.card_congr ((L.subtype.subgroupMap A).pCoreQuotientEquiv
    (L.subtype.subgroupMap_surjective A) hk).toEquiv
  rw [hm] at hi
  apply hi.symm.trans
  apply theta_preimage_quotient_card (projectiveMap c) (projectiveMap_surjective c)
  rw [projectiveMap_ker]
  exact pCore_isPGroup

/-- The explicit local invariance hypothesis preserves the original marked Sylow. -/
theorem marked_sylow_invariant (h : Setup d I L) (e : Earlier d)
    {n : ℕ} (c : ProjectiveMarking L (2 ^ n))
    (hstable : d.Yplus ⊔ d.S ≤ normalizer (d.S ⊓ L : Subgroup G))
    (P : Sylow 2 PSL(3,c.F))
    (hP : (d.S.subgroupOf L).map (projectiveMap c) = P)
    (y : d.Yplus) :
    (P : Subgroup PSL(3,c.F)).map
      (markedAction c ⟨y, h.normalizes_component e (h.outside.1.2 (mem_sup_left y.property))⟩).toMonoidHom = P := by
  let yn : normalizer (L : Set G) :=
    ⟨y, h.normalizes_component e (h.outside.1.2 (mem_sup_left y.property))⟩
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨a, ha, rfl⟩
    rw [← hP] at ha ⊢
    obtain ⟨l, hl, rfl⟩ := ha
    change markedAction c yn (projectiveMap c l) ∈ (d.S.subgroupOf L).map (projectiveMap c)
    rw [markedAction_apply]
    refine mem_map_of_mem _ ?_
    exact ((mem_normalizer_iff.mp (hstable (mem_sup_left y.property)) (l : G)).mp
      ⟨hl, l.property⟩).1
  · exact (Subgroup.card_map_of_injective (markedAction c yn).injective).ge

/-- Transfer the intrinsic outer cubic parameter restriction to the actual actor.
This transport interface keeps the matrix parameter theorem explicit. -/
theorem three_not_dvd_parameter_of_stability (h : Setup d I L) (e : Earlier d)
    {n : ℕ} (c : ProjectiveMarking L (2 ^ n))
    (hstable : d.Yplus ⊔ d.S ≤ normalizer (d.S ⊓ L : Subgroup G))
    (hparameter : ∀ P : Sylow 2 PSL(3,c.F), ∀ a : Matrix.GeneralLinearGroup (Fin 3) c.F,
      let α := Matrix.PSL3.OuterSolvable.linearConj c.F a
      α ∉ MulAut.innerSubgroup PSL(3,c.F) → α ^ 3 = 1 →
      (P : Subgroup PSL(3,c.F)).map α.toMonoidHom = P → ¬ 3 ∣ n)
    {y : G} (hy : y ∈ d.Yplus) (hdiag : c.Diagonal y) : ¬ 3 ∣ n := by
  obtain ⟨P, hP, _⟩ := h.projective_sylow e c
  obtain ⟨hy3, a, ha, hr⟩ := hdiag
  let yn : normalizer (L : Set G) :=
    ⟨y, h.normalizes_component e (h.outside.1.2 (mem_sup_left hy))⟩
  have heq := markedAction_eq_of_realizes c yn hr
  apply hparameter P a ha
  · rw [← heq, ← map_pow]
    have hyc : yn ^ 3 = 1 := by
      apply Subtype.ext
      exact hy3 ▸ pow_orderOf_eq_one y
    rw [hyc, map_one]
  · rw [← heq]
    exact marked_sylow_invariant h e c hstable P hP ⟨y,hy⟩

/-- Assemble the requested calculations from the two independent projective inputs.
This transport interface keeps those inputs explicit; `theta_borel_calculations`
below discharges them using the intrinsic matrix theorems. -/
theorem theta_borel_calculations_of_projective (h : Setup d I L) (e : Earlier d)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n))
    (hstable : d.Yplus ⊔ d.S ≤ normalizer (d.S ⊓ L : Subgroup G))
    (hparameter : ∀ P : Sylow 2 PSL(3,c.F), ∀ a : Matrix.GeneralLinearGroup (Fin 3) c.F,
      let α := Matrix.PSL3.OuterSolvable.linearConj c.F a
      α ∉ MulAut.innerSubgroup PSL(3,c.F) → α ^ 3 = 1 →
      (P : Subgroup PSL(3,c.F)).map α.toMonoidHom = P → ¬ 3 ∣ n)
    (hquotient : ¬ 3 ∣ n → ∀ P : Sylow 2 PSL(3,c.F),
      Nat.card (theta (normalizer (P : Set PSL(3,c.F))) ⧸
        pCore 2 (theta (normalizer (P : Set PSL(3,c.F))))) = 3)
    {y : G} (hy : y ∈ d.Yplus) (hdiag : c.Diagonal y) :
    (theta (borel d.S L)).pCoreIn 2 = d.S ⊓ L ∧
      Nat.card (theta (borel d.S L) ⧸ pCore 2 (theta (borel d.S L))) = 3 := by
  refine ⟨theta_borel_core h e hn heven c, ?_⟩
  have hn3 := three_not_dvd_parameter_of_stability h e c hstable hparameter hy hdiag
  obtain ⟨P, _, hpre⟩ := h.projective_sylow e c
  exact (theta_borel_quotient_card_eq_projective c P hpre).trans (hquotient hn3 P)

/-- The actual outer cubic actor preserving the marked Sylow forces the field
degree to be prime to three. -/
theorem three_not_dvd_parameter_of_marked_stability (h : Setup d I L) (e : Earlier d)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n))
    (hstable : d.Yplus ⊔ d.S ≤ normalizer (d.S ⊓ L : Subgroup G))
    {y : G} (hy : y ∈ d.Yplus) (hdiag : c.Diagonal y) : ¬ 3 ∣ n := by
  exact three_not_dvd_parameter_of_stability h e c hstable
    (Matrix.PSL3.CubicBorel.three_not_dvd_parameter hn heven c.card) hy hdiag

/-- Theta of the actual Borel has quotient of order three by its two-core.
The parameter restriction is derived from the given actor and local stability. -/
theorem theta_borel_quotient_card (h : Setup d I L) (e : Earlier d)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n))
    (hstable : d.Yplus ⊔ d.S ≤ normalizer (d.S ⊓ L : Subgroup G))
    {y : G} (hy : y ∈ d.Yplus) (hdiag : c.Diagonal y) :
    Nat.card (theta (borel d.S L) ⧸ pCore 2 (theta (borel d.S L))) = 3 := by
  have hn3 := three_not_dvd_parameter_of_marked_stability h e hn heven c hstable hy hdiag
  obtain ⟨P, _, hpre⟩ := h.projective_sylow e c
  exact (theta_borel_quotient_card_eq_projective c P hpre).trans
    (Matrix.PSL3.CubicBorel.ThetaQuotient.card_cubicNormalizer_quotient
      c.F hn heven c.card hn3 P)

/-- Both Borel theta calculations from the marked local hypotheses, including
central two-covers. No projective or central-cover calculation is assumed. -/
theorem theta_borel_calculations (h : Setup d I L) (e : Earlier d)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n))
    (hstable : d.Yplus ⊔ d.S ≤ normalizer (d.S ⊓ L : Subgroup G))
    {y : G} (hy : y ∈ d.Yplus) (hdiag : c.Diagonal y) :
    (theta (borel d.S L)).pCoreIn 2 = d.S ⊓ L ∧
      Nat.card (theta (borel d.S L) ⧸ pCore 2 (theta (borel d.S L))) = 3 :=
  ⟨theta_borel_core h e hn heven c,
    theta_borel_quotient_card h e hn heven c hstable hy hdiag⟩

/-- Construct the original oriented Borel planes with the theta calculations
discharged. Actual Sylow stability is the remaining explicit local input. -/
theorem orientedBorelData_of_marked_stability
    (hI : I ∈ d.Hplus) (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hrL : primeRank 3 L = 2) (hrY : primeRank 3 d.Yplus = 2) (e : Earlier d)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n))
    {y : G} (hy : y ∈ d.Yplus) (hdiag : c.Diagonal y)
    (hstable : d.Yplus ⊔ d.S ≤ normalizer (d.S ⊓ L : Subgroup G)) :
    Nonempty (OrientedBorelData d.M d.Yplus d.S L d.V₁ d.V₂ c) := by
  obtain ⟨hcore, hquot⟩ := theta_borel_calculations
    (setup_of_marked_actor hI hLI hL hrL hrY c hy hdiag) e hn heven c hstable hy hdiag
  exact orientedBorelData_of_marked_local hI hLI hL hrL hrY e hn heven c hy hdiag
    hstable hcore hquot

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceBorel
