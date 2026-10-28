module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometrySplitting
public import CFSG.Quasithin.Chapter6.Section01.EscapeSize.Natural

/-!
# Natural submodules in the field branch

A nonzero equivariant homomorphism to a natural SL₂ module is surjective.
For an invariant subgroup of one-copy order inside two copies, at least one
coordinate projection is nonzero; cardinality makes that projection an
equivalence. The field-fixed splitting therefore gives an actual natural
marking on every residual-invariant subgroup of the original layer of
order 2ⁿ. This supplies the representation step for the conjugate of Z_S
in 6.1.14(5); the group-theoretic construction of that invariant conjugate
remains with the contained-branch assembly owner.

Source: Aschbacher–Smith, 6.1.14(5), printed pp.671–672.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] {K U A B : Subgroup G} {m : ℕ}

/-- An equivariant group equivalence preserves the actual natural coordinates. -/
theorem natural_of_equivariant_equiv (hnatural : IsNaturalModule K U m)
    (hKA : K ≤ normalizer (A : Set G)) (e : A ≃* U)
    (he : ∀ (k : K) (a a' : A),
      (a' : G) = (k : G) * (a : G) * (k : G)⁻¹ →
      (e a' : G) = (k : G) * (e a : G) * (k : G)⁻¹) :
    IsNaturalModule K A m := by
  obtain ⟨F, _, _, _, hF, q, f, hf⟩ := hnatural
  refine ⟨F, inferInstance, inferInstance, inferInstance, hF, q, e.trans f, ?_⟩
  intro k a
  let a' : A := ⟨(k : G) * (a : G) * (k : G)⁻¹,
    (mem_normalizer_iff.mp (hKA k.property) a).mp a.property⟩
  have hv : f (e a') = Multiplicative.ofAdd
      (Representation.specialLinearNatural 2 (q (QuotientGroup.mk' (pCore 2 K) k))
        (f (e a)).toAdd) := by
    apply f.symm.injective
    apply Subtype.ext
    simpa only [MulEquiv.symm_apply_apply] using (he k a a' rfl).trans (hf k (e a)).symm
  change ((e.trans f).symm (Multiplicative.ofAdd
    (Representation.specialLinearNatural 2 (q (QuotientGroup.mk' (pCore 2 K) k))
      (f (e a)).toAdd)) : G) = _
  rw [← hv]
  simp only [MulEquiv.symm_trans_apply, MulEquiv.symm_apply_apply]
  rfl

/-- A nonzero equivariant homomorphism onto a natural module is surjective. -/
theorem natural_equivariant_surjective (hnatural : IsNaturalModule K U m)
    (hKA : K ≤ normalizer (A : Set G)) (p : A →* U)
    (hp : ∀ (k : K) (a a' : A),
      (a' : G) = (k : G) * (a : G) * (k : G)⁻¹ →
      (p a' : G) = (k : G) * (p a : G) * (k : G)⁻¹)
    (hne : ∃ a, p a ≠ 1) : Function.Surjective p := by
  let J := (U.subtype.comp p).range
  have hJU : J ≤ U := by
    rintro _ ⟨a, rfl⟩
    exact (p a).property
  have hKJ : K ≤ normalizer (J : Set G) := by
    apply le_normalizer_iff.mpr
    intro k hk y hy
    obtain ⟨a, rfl⟩ := hy
    let a' : A := ⟨k * (a : G) * k⁻¹, (mem_normalizer_iff.mp (hKA hk) a).mp a.property⟩
    exact ⟨a', hp ⟨k, hk⟩ a a' rfl⟩
  have hJ : J ≠ ⊥ := by
    intro hz
    obtain ⟨a, ha⟩ := hne
    have hm : (p a : G) ∈ J := ⟨a, rfl⟩
    rw [hz] at hm
    exact ha (Subtype.ext (mem_bot.mp hm))
  have hJUeq := (hnatural.invariant_subgroup J hJU hKJ).resolve_left hJ
  intro v
  have hv : (v : G) ∈ J := hJUeq.symm ▸ v.property
  obtain ⟨a, ha⟩ := hv
  exact ⟨a, Subtype.ext ha⟩

variable [Finite G]

/-- An invariant subgroup of one-copy order in two copies is a natural module. -/
theorem natural_of_double_equiv (hnatural : IsNaturalModule K U m)
    (hAB : A ≤ B) (hKA : K ≤ normalizer (A : Set G))
    (hAne : A ≠ ⊥) (hcard : Nat.card A = Nat.card U)
    (e : B ≃* (U × U))
    (he : ∀ (k : K) (b b' : B),
      (b' : G) = (k : G) * (b : G) * (k : G)⁻¹ →
      ((e b').1 : G) = (k : G) * ((e b).1 : G) * (k : G)⁻¹ ∧
      ((e b').2 : G) = (k : G) * ((e b).2 : G) * (k : G)⁻¹) :
    IsNaturalModule K A m := by
  let p₁ := (MonoidHom.fst U U).comp (e.toMonoidHom.comp (inclusion hAB))
  let p₂ := (MonoidHom.snd U U).comp (e.toMonoidHom.comp (inclusion hAB))
  have he₁ : ∀ (k : K) (a a' : A),
      (a' : G) = (k : G) * (a : G) * (k : G)⁻¹ →
      (p₁ a' : G) = (k : G) * (p₁ a : G) * (k : G)⁻¹ :=
    fun k a a' ha => (he k (inclusion hAB a) (inclusion hAB a') ha).1
  have he₂ : ∀ (k : K) (a a' : A),
      (a' : G) = (k : G) * (a : G) * (k : G)⁻¹ →
      (p₂ a' : G) = (k : G) * (p₂ a : G) * (k : G)⁻¹ :=
    fun k a a' ha => (he k (inclusion hAB a) (inclusion hAB a') ha).2
  have hp : (∃ a, p₁ a ≠ 1) ∨ ∃ a, p₂ a ≠ 1 := by
    by_contra! hz
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
    have hea : e (inclusion hAB a) = 1 := Prod.ext (hz.1 a) (hz.2 a)
    have hab : inclusion hAB a = 1 := e.injective (hea.trans e.map_one.symm)
    exact ha (Subtype.ext (congrArg (fun b : B => (b : G)) hab))
  rcases hp with hp | hp
  · have hs := natural_equivariant_surjective hnatural hKA p₁ he₁ hp
    exact natural_of_equivariant_equiv hnatural hKA
      (MulEquiv.ofBijective p₁ ((Nat.bijective_iff_surjective_and_card p₁).mpr ⟨hs, hcard⟩)) he₁
  · have hs := natural_equivariant_surjective hnatural hKA p₂ he₂ hp
    exact natural_of_equivariant_equiv hnatural hKA
      (MulEquiv.ofBijective p₂ ((Nat.bijective_iff_surjective_and_card p₂).mpr ⟨hs, hcard⟩)) he₂
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition


open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {L M B U A : Subgroup G} {n : ℕ}

/-- The residual action on an invariant subgroup of the half-degree order. -/
theorem field_fixedSpace_invariant_natural
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥) (hn : 2 < n)
    (hAB : A ≤ B) (hcard : Nat.card A = 2 ^ n)
    (hRA : fieldLocalResidual L U ≤ normalizer (A : Set G)) :
    ∃ m, n = 2 * m ∧ IsNaturalModule (fieldLocalResidual L U) A m := by
  obtain ⟨m, hnm, _, hRU⟩ := field_fixedSpace_natural hn hnatural hfield hUne
  obtain ⟨e, he⟩ := field_fixedSpace_double_equiv hnatural hfield hUne
  have hUcard : Nat.card U = 2 ^ n := by
    rw [hRU.card, Nat.mul_comm m 2, ← hnm]
  have hAne : A ≠ ⊥ := by
    intro hz
    rw [hz, card_bot] at hcard
    have : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
    omega
  refine ⟨m, hnm, natural_of_double_equiv hRU hAB hRA hAne
    (hcard.trans hUcard.symm) e ?_⟩
  intro k b b' hb
  exact he (inclusion (map_subtype_le _) k) b b' hb

/-- The source corank convention gives exactly the order required above. -/
theorem field_fixedSpace_corank_invariant_natural [IsElementaryAbelian 2 B]
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥) (hn : 2 < n)
    (hAB : A ≤ B) (hcor : ChapterE.subgroupCorank B A = n)
    (hRA : fieldLocalResidual L U ≤ normalizer (A : Set G)) :
    ∃ m, n = 2 * m ∧ IsNaturalModule (fieldLocalResidual L U) A m :=
  field_fixedSpace_invariant_natural hnatural hfield hUne hn hAB
    (ConjugateFixedSpaces.corank_half_card hAB hnatural.card hcor) hRA
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
