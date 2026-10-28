module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingBranch
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.StarQuotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SeedAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.StarQuotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.Component
public import Theory.Representation.BinaryConjugationSection.ActionKernel

/-!
# Alternating-branch uniqueness at the same G,T

Count the actual point parabolic to obtain index five. The faithful S₅ section action and the original TI conclusion give normalizer escape. Maximality of the point parabolic then proves the literal singleton equality for H_z. This uniqueness is used only after the alternating branch is known.

Only Structural1222At at the original G,T is used. Independent model and
section lemmas are reused from LocalReduction; its universal APIs are preserved.
Source: Aschbacher–Smith, final paragraph of 14.7.40, printed p.1063,
and 14.7.52–63, printed pp.1065–1069. Earlier structural source discharge
and the unconditional classification remain with their existing owners.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
local notation "B" => (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)

omit [Finite G] in
private theorem point_le_H : B ≤ F.H :=
  sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)

omit [Finite G] in
private theorem marking_kernel (e : HStar F.H ≃* ChapterJ.S5) :
    (quotientMarking e).ker = pCore 2 F.H := by
  rw [quotientMarking, MonoidHom.ker_comp_of_injective _ _ e.injective]
  exact QuotientGroup.ker_mk' _

/-- The actual point parabolic has index five in H in the S₅ branch. -/
theorem point_index_five_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (e : HStar F.H ≃* ChapterJ.S5) : ((B).subgroupOf F.H).index = 5 := by
  let q := quotientMarking e
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let f : B →* ChapterJ.S5 := q.comp (inclusion point_le_H)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (q.ker.comap (inclusion point_le_H))
    rw [marking_kernel]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective point_le_H)
  have hc := point_image_ratio_at h structural f hk
  let S : Sylow 2 ChapterJ.S5 := (T.subtype (F.invariant 1)).mapSurjective hq
  have hS : (S : Subgroup ChapterJ.S5) ≤ f.range := by
    change ((T.subtype (F.invariant 1) : Sylow 2 F.H) : Subgroup F.H).map q ≤ f.range
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨⟨t.val, (show (T : Subgroup G) ≤ B from le_sup_right) ht⟩, rfl⟩
  have hSc : Nat.card S = 8 := by
    rw [S.card_eq_multiplicity]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    decide +kernel
  have h8 : 8 ∣ Nat.card f.range := hSc ▸ card_dvd_of_le hS
  have hS5 : Nat.card ChapterJ.S5 = 120 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hd : Nat.card f.range ∣ 120 := hS5 ▸ f.range.card_subgroup_dvd_card
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := f.range)).exists_card_eq
  have hb := Nat.le_of_dvd (by decide : 0 < 120) hd
  have hnle : n ≤ 4 := by
    by_contra hh
    have hp : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hn] at hc
    norm_num at hp
    omega
  have hcard : Nat.card f.range = 24 := by
    interval_cases n <;> norm_num at hn <;> simp_all
  have hr : f.range = ((B).subgroupOf F.H).map q := by
    ext g
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨inclusion point_le_H b, b.property, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b.val, hb⟩, rfl⟩
  have hi := f.range.card_mul_index
  rw [hcard, hS5] at hi
  have hfindex : f.range.index = 5 := by omega
  have hker : q.ker ≤ (B).subgroupOf F.H := by
    rw [marking_kernel]
    intro a ha
    exact (pCoreIn_le 2 B) (core_le_point_core (mem_map_of_mem _ ha))
  rw [hr, ((B).subgroupOf F.H).index_map_eq hq hker] at hfindex
  exact hfindex

private theorem no_faithful_symmetric_four_points [Finite W]
    (σ : Representation (ZMod 2) ChapterJ.S5 W) (hf : Function.Injective σ)
    (hc : Nat.card W = 4) : False := by
  classical
  let f : ChapterJ.S5 → Equiv.Perm W := fun g =>
    (LinearMap.GeneralLinearGroup.toLinearEquiv (σ.asGroupHom g)).toEquiv
  have hi : Function.Injective f := by
    intro a b he
    apply hf
    ext w
    exact congrArg (fun k : Equiv.Perm W => k w) he
  have hb := Nat.card_le_card_of_injective f hi
  let := Fintype.ofFinite W
  have hp : Nat.card (Equiv.Perm W) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hc]
    rfl
  have hs : Nat.card ChapterJ.S5 = 120 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  omega

/-- The faithful star action and TI exclude H ≤ M without an escape callback. -/
theorem alternating_escape_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (e : HStar F.H ≃* ChapterJ.S5) : ¬ F.H ≤ normalizer (L : Set G) := by
  intro hHM
  have hHN : F.H ≤ normalizer (V : Set G) := by
    have hne : F.Vi 1 ≠ ⊥ := by
      intro he
      have hc := F.card 1 (by decide)
      rw [he, Subgroup.card_bot] at hc
      norm_num at hc
    exact (le_inf hHM le_rfl).trans
      (inf_normalizer_le_of_trivial_intersections
        ((structural L h.source).2.2 V h.chosen).2.2.1 hne (F.le_seed 1))
  have hU : F.U = V := le_antisymm (conjugateSpanBy_le le_rfl hHN)
    (le_conjugateSpanBy V F.H)
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ, ⟨c⟩⟩ := exists_section F
  obtain ⟨σ, _, hσ⟩ := exists_faithful_symmetric_representation h e c
  have hc := c.card_section
  have hV : Nat.card V = 8 := by simpa only [F.last, Nat.reducePow] using F.card 3 (by decide)
  have hP : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hUc : Nat.card F.U = 8 := (Nat.card_congr (MulEquiv.subgroupCongr hU).toEquiv).trans hV
  rw [hUc, hP] at hc
  exact no_faithful_symmetric_four_points σ hσ (by omega)

/-- Uniqueness in the A₅ residual branch follows from the actual index-five
point parabolic and the original normalizer exclusion. -/
theorem unique_of_alternating_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hAlt : AlternatingResidual F) :
    F.Hz L (normalizer (L : Set G)) = {F.H} := by
  obtain ⟨e⟩ := exists_symmetric_star_at h structural hAlt
  have hi := point_index_five_at h structural e
  have hmax : IsCoatom ((B).subgroupOf F.H) := by
    refine ⟨?_, ?_⟩
    · intro he
      simp [he] at hi
    · intro J hJ
      have hd := index_dvd_of_le hJ.le
      rw [hi] at hd
      rcases (Nat.dvd_prime Nat.prime_five).mp hd with he | he
      · exact index_eq_one.mp he
      · have hs := index_strictAnti hJ
        omega
  have hBM : B ≤ normalizer (L : Set G) :=
    sup_le ((F.Li_le L 1).trans (inf_le_left.trans L.le_normalizer))
      (h.sylow_normalizes_at structural)
  ext J
  constructor
  · intro hJ
    have hBJ : B ≤ J := sup_le (fun _ hx => hJ.1.2 (Or.inl hx))
      (fun _ hx => hJ.1.2 (Or.inr hx))
    have hJH : J ≤ F.H := hJ.2.1
    rcases hmax.le_iff.mp (subgroupOf_mono F.H hBJ) with ht | he
    · have hh := congrArg (map F.H.subtype) ht
      rw [map_subgroupOf_eq_of_le hJH, ← MonoidHom.range_eq_map, range_subtype] at hh
      exact Set.mem_singleton_iff.mpr hh
    · have hh := congrArg (map F.H.subtype) he
      rw [map_subgroupOf_eq_of_le hJH,
        map_subgroupOf_eq_of_le (show B ≤ F.H from point_le_H)] at hh
      exact (hJ.2.2 (hh.le.trans hBM)).elim
  · intro hJ
    obtain rfl := Set.mem_singleton_iff.mp hJ
    exact F.H_mem_Hz (by decide) L _ (alternating_escape_at h hab structural e)

/-- Actual application to the published source-branch constructor. Uniqueness
and the component condition now follow after the independent G₂ exclusion. -/
theorem exists_data_of_recognition_branches_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (h52 : AlternatingResidual F ∨ G2Residual F)
    (h53 : ¬ G2Residual F)
    (h40 : AlternatingResidual F → NaturalRecognition F) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      Nonempty (Data T L V F W) :=
  exists_data_of_source_branches d h hab
    (unique_of_alternating_at h hab structural (h52.resolve_right h53))
    (component_of_residual_alternatives h52) h52 h53 h40

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
