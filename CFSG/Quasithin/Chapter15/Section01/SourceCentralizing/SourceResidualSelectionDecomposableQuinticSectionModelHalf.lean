module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionModelRows

/-!
# Exact original actor cost on a whole B.5 seed

When the actual prepared seed is the whole faithful module, its literal
actor image has exactly the original rank and fixed codimension. The same
quadratic actor on a moved central quotient then has ratio at most one-half.
This excludes the symplectic and symmetric-eight rows while retaining the
literal linear model markings. The whole-seed equality is an explicit
proved geometric input; it is not inferred from the component carrier.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ComponentReduction
open ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- The literal whole-seed image loses neither original rank nor fixed cost. -/
theorem seed_cost_of_whole
    (σ : Representation (ZMod 2) G W) (hf : Function.Injective σ)
    {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) (hA : IsElementaryTwo A)
    (ht : naturalSeedSpace σ L A = ⊤) :
    rank (seedOffenderImage σ hLA) = rank A ∧
      fixedCodim (seedQuotientAction σ hLA) (seedOffenderImage σ hLA) =
        fixedCodim σ A := by
  have hAI := (le_sup_right : A ≤ L ⊔ A).trans (seedSpace_stable σ hLA)
  have hk : subspaceKernel σ (naturalSeedSpace σ L A) A = ⊥ := by
    apply (subspaceKernel_eq_bot_iff σ _ A).mpr
    intro a _ ha
    apply hf
    apply LinearMap.ext
    intro w
    simpa only [map_one, Module.End.one_apply] using ha w (ht ▸ Submodule.mem_top)
  let : IsElementaryAbelian 2 A := hA.2
  have hr := rank_subspaceKernel_add_image σ (naturalSeedSpace σ L A) A hAI
    (IsElementaryAbelian.isPGroup 2 A)
  constructor
  · rw [seedOffenderImage_rank]
    simpa only [hk, Representation.BinaryOffender.rank_bot, zero_add] using hr
  · rw [seedOffenderImage_fixedCodim]
    exact fixedCodim_restricted_eq_of_sup σ _ hAI (by rw [ht, top_sup_eq])

/-- The original exact half-cost actor gives the same-actor moved quotient
quadratic ratio at most one-half. -/
theorem moved_section_ratio_le_half_of_exact_cost
    (σ : Representation (ZMod 2) G W) {A L : Subgroup G}
    (hA : IsElementaryTwo A) (hq : IsQuadratic σ A)
    (hcost : (rank A = 2 ∧ fixedCodim σ A = 1) ∨
      (rank A = 4 ∧ fixedCodim σ A = 2)) (s : MovedSection σ L) :
    quadraticRatio s.action ≤ 1 / 2 := by
  have hqs : IsQuadratic s.action A :=
    quadratic_of_equivariant_surjection s.space.toRepresentation s.action
      s.central.toSubmodule.mkQ s.central.toSubmodule.mkQ_surjective
      (fun _ _ => rfl) A (quadratic_subrepresentation σ s.space hq)
  have hb : fixedCodim s.action A ≤ fixedCodim σ A := by
    have hq := fixedCodim_quotient_add_subrepresentation_le s.space.toRepresentation s.central A
    have hs := fixedCodim_subrepresentation_le σ s.space A
    exact (Nat.le_add_right _ _).trans (hq.trans hs)
  apply (quadraticRatio_le_iff s.action (by norm_num : (1 / 2 : ENNReal) ≠ ⊤)).mpr
  refine ⟨A, hA, hqs, ?_⟩
  rcases hcost with ⟨hr, hc⟩ | ⟨hr, hc⟩
  · rw [actionRatio, hr]
    rw [hc] at hb
    exact ENNReal.div_le_div_right (by exact_mod_cast hb) 2
  · rw [actionRatio, hr]
    rw [hc] at hb
    calc
      (fixedCodim s.action A : ENNReal) / 4 ≤ 2 / 4 :=
        ENNReal.div_le_div_right (by exact_mod_cast hb) 4
      _ = 1 / 2 := by
        apply (ENNReal.toReal_eq_toReal_iff'
          (ENNReal.div_ne_top (by norm_num) (by norm_num)) (by norm_num)).mp
        norm_num [ENNReal.toReal_div]

/-- Prepared whole-seed geometry supplies the half-ratio on its literal
moved central quotient, using the actual seed-offender image. -/
theorem prepared_whole_seed_moved_ratio_le_half
    (σ : Representation (ZMod 2) G W) (hf : Function.Injective σ)
    {A L : Subgroup G} {K : GroupClass} (hLA : ⁅L,A⁆ = L)
    (p : Prepared σ K hLA) (hA : IsElementaryTwo A)
    (ht : naturalSeedSpace σ L A = ⊤)
    (hcost : (rank A = 2 ∧ fixedCodim σ A = 1) ∨
      (rank A = 4 ∧ fixedCodim σ A = 2))
    (s : MovedSection (seedQuotientAction σ hLA) (seedComponentImage σ hLA)) :
    quadraticRatio s.action ≤ 1 / 2 := by
  obtain ⟨hr, hc⟩ := seed_cost_of_whole σ hf hLA hA ht
  apply moved_section_ratio_le_half_of_exact_cost (seedQuotientAction σ hLA)
    p.minimal.1.1 (p.minimal.isQuadratic _) _ s
  simpa only [hr, hc] using hcost

omit [Finite G] [FiniteDimensional (ZMod 2) W] in
/-- At half-ratio the marked strong-plane catalogue retains only its
natural linear three and binary linear four/five actions. -/
theorem linear_rows_of_half_ratio
    (σ : Representation (ZMod 2) G W) {L : Subgroup G}
    (hrows : StrongPlaneActionRows σ L) (hq : quadraticRatio σ ≤ 1 / 2) :
    (∃ F : BinaryField, F.degree ≤ 2 ∧ offenderSubgroup σ = L ∧
      Nonempty (ActionEquiv (σ.comp L.subtype) (linearNatural F 3)) ∧
      quadraticRatio σ = 1 / 2) ∨
    (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ offenderSubgroup σ = L ∧
      Nonempty (ActionEquiv (σ.comp L.subtype) (linearNatural BinaryField.two n)) ∧
      quadraticRatio σ = 1 / (n - 1 : ℕ)) := by
  rcases hrows with h | ⟨F, hF, hg, e, hr⟩ | ⟨e, hr⟩ | h | ⟨hg, e, hr⟩
  · exact Or.inl h
  · rw [hr] at hq
    have hh := ENNReal.toReal_mono (by norm_num : (1 / 2 : ENNReal) ≠ ⊤) hq
    norm_num [ENNReal.toReal_div] at hh
  · rw [hr] at hq
    have hh := ENNReal.toReal_mono (by norm_num : (1 / 2 : ENNReal) ≠ ⊤) hq
    norm_num [ENNReal.toReal_div] at hh
  · exact Or.inr h
  · rw [hr] at hq
    have hh := ENNReal.toReal_mono (by norm_num : (1 / 2 : ENNReal) ≠ ⊤) hq
    norm_num [ENNReal.toReal_div] at hh

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl
