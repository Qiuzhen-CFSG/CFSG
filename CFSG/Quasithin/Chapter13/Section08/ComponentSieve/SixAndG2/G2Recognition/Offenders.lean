module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.G2Binary
public import CFSG.Quasithin.ChapterB.Section01.IrreducibleSections

/-!
# Derived binary G₂ has no faithful strong-FF or transvection modules

A minimal best offender stabilizes an actual Irr⁺ section by B.1.5(3).
Its central-section kernel centralizes the self-centralizing normal component,
so the section action is faithful. The proved binary G₂ cubic recognition
identifies its natural six-space, whose full linear normalizer is G₂(2).
Every natural offender has rank and fixed codimension three. Section
codimension and quadratic replacement give the asserted exclusions on the
original module, including reducible modules and outer actors.

Source: Aschbacher–Smith B.1.5, B.4.2, B.4.6 and K.3, as used in
13.8.27, printed p.963. The actual component is G₂(2)′ throughout.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition

variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) (L : Subgroup D) [L.Normal] [IsQuasisimple L]

omit [Finite D] in
private theorem component_commutator {A : Subgroup D} (hne : A ≠ ⊥)
    (hc : centralizer (L : Set D) = ⊥) : ⁅L, A⁆ = L := by
  have hL : IsComponent D L := ⟨(inferInstance : L.Normal).isSubnormal, inferInstance⟩
  rcases hL.commutator_dichotomy A with hz | he
  · have hAC : A ≤ centralizer (L : Set D) :=
      commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm A L).trans hz)
    exact (hne (bot_unique (hAC.trans hc.le))).elim
  · simpa only [MulEquiv.toMonoidHom_eq_coe, Subgroup.Normal.map_conj_eq, iSup_const] using he

/-- Minimal best offenders on any faithful binary module have rank three,
and their fixed codimension is at least three. -/
theorem minimal_offender_bounds (hf : Function.Injective ρ)
    (hc : centralizer (L : Set D) = ⊥)
    (e : L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    {A : Subgroup D} (hA : IsMinimalBestOffender ρ A) :
    rank A = 3 ∧ 3 ≤ fixedCodim ρ A := by
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hr : pResidual 2 L = ⊤ := by
    apply (pResidual_eq_top_iff 2 L).mpr
    intro N hN hp
    let := hN
    have hsub : Subsingleton (L ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (L ⧸ N) hp.isNilpotent
    apply top_unique
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
  have hchief : HasCentralPChiefFactors 2 L :=
    hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient
      (⊥ : Subgroup L) (by simp)
      (IsQuasisimple.of_mulEquiv QuotientGroup.quotientBot.symm)
  obtain ⟨I, hI⟩ := exists_isIrrPlus_of_faithful ρ hf L
    ((nontrivial_iff_ne_bot L).mp inferInstance)
  have hAI := ChapterB.source_lemma_B_1_5_3 ρ hf hA hr
    (component_commutator L hA.1.1.1 hc) hchief hI
  let H := L ⊔ A
  have hLH : L ≤ H := le_sup_left
  have hAH : A ≤ H := le_sup_right
  have hHI : H ≤ subspaceStabilizer ρ I := sup_le hI.choose hAI
  let σ := centralSectionRepresentation ρ L H I hHI le_normalizer_of_normal
  let L₀ := L.subgroupOf H
  let : L₀.Normal := inferInstance
  let W := invariantSubspace ρ H I hHI
  let U : Subrepresentation (ρ.comp H.subtype) := ⟨fixedSpace ρ L, fun h _ hv =>
    (fixedSpace_stable_of_normalizes ρ (show H ≤ normalizer (L : Set D) from
      le_normalizer_of_normal) h.property _).2 hv⟩
  have hcod : fixedCodim σ (A.subgroupOf H) ≤ fixedCodim ρ A := by
    have hb := fixedCodim_section_le (ρ.comp H.subtype) U W (A.subgroupOf H)
    rw [fixedCodim_subgroupOf ρ hAH] at hb
    exact hb
  have hσ : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have h := (centralSection_kernel_le_centralizer ρ L H hLH I hI hHI
      le_normalizer_of_normal (mem_map_of_mem H.subtype hx)).2
    change (x : D) ∈ centralizer (L : Set D) at h
    rw [hc, mem_bot] at h
    exact Subtype.ext h
  have hi : IsIrreducible (σ.comp L₀.subtype) := by
    let f : L₀ ≃* L := subgroupOfEquivOfLe hLH
    have he : σ.comp L₀.subtype =
        (centralQuotientRepresentation ρ L I hI.choose).comp f.toMonoidHom := rfl
    rw [he]
    exact (irreducible_comp_surjective_iff f.toMonoidHom f.surjective _).mpr hI.choose_spec.2
  let := hi
  have hAo : IsOffender σ (A.subgroupOf H) := by
    refine ⟨(hA.1.subgroupOf ρ hAH).1, ?_⟩
    rw [rank_subgroupOf hAH]
    exact hcod.trans (hA.1.isOffender ρ).2
  have hsmall : cubicRatio σ ≤ 2 := (cubicRatio_le_quadraticRatio σ).trans
    (((isFFModule_iff_quadraticRatio_le_one σ).mp ⟨_, hAo⟩).trans (by norm_num))
  obtain ⟨e', f, hnat⟩ := ChapterK.Exceptional.SourceAssembly.g2_binary_natural σ L₀
    ((subgroupOfEquivOfLe hLH).trans e) hσ hsmall
  let f₂ : centralQuotient ρ L I ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2) :=
    LinearEquiv.ofBijective (f.toAddMonoidHom.toZModLinearMap 2) f.bijective
  obtain ⟨j, hj, _, hjact⟩ := Atlas.G2.Natural.BinaryNormalizer.ambient_embedding
    σ L₀ e' f₂ (fun g v => hnat g v) hσ
  have ho := hAo.map_equivariant σ (Atlas.G2.Natural.action (ZMod 2)) j hj f₂ hjact
  have ha := Atlas.G2.NaturalOffenders.natural_offender_rank
    (n := 1) (by norm_num) (by decide) _ ho
  have hd := Atlas.G2.NaturalOffenders.natural_offender_fixedCodim
    (n := 1) (by norm_num) (by decide) _ ho
  rw [rank_map_injective j hj, rank_subgroupOf hAH] at ha
  have htransport := fixedCodim_map_equivariant σ
    (Atlas.G2.NaturalOffenders.binaryNatural (F := ZMod 2)) j
    (LinearEquiv.ofBijective (f.toAddMonoidHom.toZModLinearMap 2) f.bijective)
    (fun g v => hjact g v) (A.subgroupOf H)
  rw [← htransport] at hd
  exact ⟨by simpa using ha, by simpa only [mul_one] using hd.ge.trans hcod⟩

/-- No faithful binary module for an almost simple derived G₂ actor is strong FF. -/
theorem no_strong (hf : Function.Injective ρ) (hc : centralizer (L : Set D) = ⊥)
    (e : L ≃* commutator (Atlas.G2.Model (ZMod 2))) : ¬ IsStrongFFModule ρ := by
  rintro ⟨A, hA⟩
  obtain ⟨B, _, hB, _, hs⟩ := hA.exists_quadratic_minimalBestOffender ρ
  obtain ⟨hr, hd⟩ := minimal_offender_bounds ρ L hf hc e hB
  have hh := hs.2
  omega

/-- Every offender has rank at least three, even on a reducible faithful module. -/
theorem offender_rank_ge_three (hf : Function.Injective ρ)
    (hc : centralizer (L : Set D) = ⊥)
    (e : L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    {A : Subgroup D} (hA : IsOffender ρ A) : 3 ≤ rank A := by
  obtain ⟨B, hBA, hB, _, _⟩ := hA.exists_quadratic_minimalBestOffender ρ
  obtain ⟨hr, _⟩ := minimal_offender_bounds ρ L hf hc e hB
  exact hr.symm.le.trans (Nat.log_mono_right (Nat.card_le_card_of_injective _ (inclusion_injective hBA)))

/-- A faithful binary module admits no transvection from an involution. -/
theorem no_transvection (hf : Function.Injective ρ)
    (hc : centralizer (L : Set D) = ⊥)
    (e : L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (a : D) (hne : a ≠ 1) (hpow : a ^ 2 = 1) :
    fixedCodim ρ (zpowers a) ≠ 1 := by
  intro hdim
  have ha : orderOf a = 2 := (orderOf_eq_prime_iff (p := 2)).mpr ⟨hpow, hne⟩
  have hr : rank (zpowers a) = 1 := by
    rw [rank, Nat.card_zpowers, ha]
    decide
  have he : IsElementaryTwo (zpowers a) :=
    ⟨by simpa using hne, IsElementaryAbelian.zpowers_of_pow_eq_one hpow⟩
  have hb := offender_rank_ge_three ρ L hf hc e (show IsOffender ρ (zpowers a) from
    ⟨he, by rw [hdim, hr]⟩)
  omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition
