module
public import CFSG.Quasithin.Chapter7.NormalizedSource.Automizer
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Source
public import Theory.Representation.BinaryOffender.PerfectNormalizer
public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms.Unconditional
public import Theory.SpecificGroups.Suzuki.TwoRank

/-!
# Automizer two-ranks in the unitary and Suzuki source rows

The literal ambient automizer embeds into the full linear normalizer of a
marked normal component action. Schur's lemma makes the conjugation action
faithful on elementary two-subgroups, and perfectness gives faithful descent
to the component's central quotient. The actual PSU and Suzuki automorphism
bounds therefore give the two-rank column of Table 7.2.1.

These are local rank bounds, not the global weak-closure exclusions. Their
chosen-module applications retain the original orbit and component.
Source: Aschbacher--Smith, Table 7.2.1 and Lemma 7.5.2, printed pp.698,700.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource

/-- A normal component marking embeds the literal automizer in its full linear
normalizer, retaining the complete conjugation action in the same coordinates. -/
theorem automizer_marked_normalizer
    {G K E : Type*} [Group G] [Finite G] [Group K]
    [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (W L : Subgroup G) [IsElementaryAbelian 2 W]
    (hLN : L ≤ normalizer (W : Set G))
    (hNL : normalizer (W : Set G) ≤ normalizer (L : Set G))
    (ρ : Representation (ZMod 2) K E) (f : L →* K) (hf : Function.Surjective f)
    (e : E ≃ₗ[ZMod 2] Additive W)
    (he : ∀ (l : L) (v : E),
      e (ρ (f l) v) = Additive.ofMul
        ⟨(l : G) * ((e v).toMul : G) * (l : G)⁻¹,
          (mem_normalizer_iff.mp (hLN l.property) _).mp (e v).toMul.property⟩) :
    ∃ j : ChapterE.Automizer W →* linearNormalizer ρ,
      Function.Injective j ∧ ∀ a v,
        e (normalizerRepresentation ρ (j a) v) = ChapterE.automizerRepresentation W a (e v) := by
  let : Finite E := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) E) := Finite.of_injective
    (fun f : Module.End (ZMod 2) E => (f : E → E)) DFunLike.coe_injective
  let N := normalizer (W : Set G)
  let q := W.normalizerMonoidHom.rangeRestrict
  let i : L →* ChapterE.Automizer W := q.comp (inclusion hLN)
  have hi : i.range = (L.subgroupOf N).map q := by
    ext a
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨inclusion hLN l, l.property, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, hl⟩, rfl⟩
  let : (L.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hNL
  let : i.range.Normal := hi ▸ Normal.map inferInstance q
    W.normalizerMonoidHom.rangeRestrict_surjective
  let γ : Representation (ZMod 2) (ChapterE.Automizer W) E :=
    e.symm.conjRingEquiv.toMonoidHom.comp (ChapterE.automizerRepresentation W)
  have hγ : Function.Injective γ :=
    e.symm.conjRingEquiv.injective.comp (ChapterE.automizerRepresentation_injective W)
  have hres (l : L) : γ (i l) = ρ (f l) := by
    ext v
    apply e.injective
    change e (e.symm (ChapterE.automizerRepresentation W (i l) (e v))) = _
    rw [e.apply_symm_apply, he]
    rfl
  have himage : i.range.map γ.asGroupHom = actionImage ρ := by
    ext z
    constructor
    · rintro ⟨_, ⟨l, rfl⟩, rfl⟩
      exact ⟨f l, Units.ext (hres l).symm⟩
    · rintro ⟨k, rfl⟩
      obtain ⟨l, rfl⟩ := hf k
      exact ⟨i l, ⟨l, rfl⟩, Units.ext (hres l)⟩
  have hn (a : ChapterE.Automizer W) : γ.asGroupHom a ∈ linearNormalizer ρ := by
    change γ.asGroupHom a ∈ normalizer (actionImage ρ : Set _)
    rw [← himage]
    exact i.range.le_normalizer_map γ.asGroupHom
      (mem_map_of_mem _ (le_normalizer_of_normal (mem_top a)))
  let j : ChapterE.Automizer W →* linearNormalizer ρ := γ.asGroupHom.codRestrict _ hn
  refine ⟨j, (fun _ _ hxy =>
    hγ (congrArg (fun z : linearNormalizer ρ => z.val.val) hxy)), ?_⟩
  intro a v
  exact e.apply_symm_apply _


/-- Coordinates for a normal component bound the literal ambient automizer by
its full linear normalizer. The marking may have a kernel in the original group. -/
theorem automizer_rank_le_marked_normalizer
    {G K E : Type*} [Group G] [Finite G] [Group K]
    [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (W L : Subgroup G) [IsElementaryAbelian 2 W]
    (hLN : L ≤ normalizer (W : Set G))
    (hNL : normalizer (W : Set G) ≤ normalizer (L : Set G))
    (ρ : Representation (ZMod 2) K E) (f : L →* K) (hf : Function.Surjective f)
    (e : E ≃ₗ[ZMod 2] Additive W)
    (he : ∀ (l : L) (v : E),
      e (ρ (f l) v) = Additive.ofMul
        ⟨(l : G) * ((e v).toMul : G) * (l : G)⁻¹,
          (mem_normalizer_iff.mp (hLN l.property) _).mp (e v).toMul.property⟩) :
    primeRank 2 (ChapterE.Automizer W) ≤ primeRank 2 (linearNormalizer ρ) := by
  obtain ⟨j, hj, _⟩ := automizer_marked_normalizer W L hLN hNL ρ f hf e he
  let : Finite E := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) E) := Finite.of_injective
    (fun f : Module.End (ZMod 2) E => (f : E → E)) DFunLike.coe_injective
  exact Theory.GroupTheory.primeRank_le_of_injective 2 j hj

variable {A E : Type*} [Group A] [Finite A]
  [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
  {ρ : Representation (ZMod 2) A E} {Q : Subgroup A}

omit [Finite A] in
/-- The unitary row's rank bound for the full normalizer of the original
component action, using the actual PSU quotient and arbitrary Hermitian form. -/
theorem unitary_normalizer_rank
    (h : ChapterK.RankOne.SourceHypotheses ρ Q) {s : ℕ} (hs : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (Q ⧸ center Q) 3 (2 ^ s)) :
    primeRank 2 (linearNormalizer (ρ.comp Q.subtype)) ≤ s + 1 := by
  let := h.quasisimple
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hq
  exact (PerfectNormalizer.primeRank_le (ρ.comp Q.subtype)
    (h.faithful.comp Q.subtype_injective) h.irreducible e).trans
    (HermitianForm.EvenTwoRank.automorphism_two_rank_le J hs hcard hconj)

omit [Finite A] in
/-- The Suzuki row's rank bound for the full normalizer of the original
component action, with the literal central quotient marking. -/
theorem suzuki_normalizer_rank
    (h : ChapterK.RankOne.SourceHypotheses ρ Q) {m : ℕ} (hm : 1 ≤ m)
    (e : (Q ⧸ center Q) ≃* SuzukiMatrixGroup m) :
    primeRank 2 (linearNormalizer (ρ.comp Q.subtype)) ≤ 2 * m + 1 := by
  let := h.quasisimple
  exact (PerfectNormalizer.primeRank_le (ρ.comp Q.subtype)
    (h.faithful.comp Q.subtype_injective) h.irreducible e).trans
    (suzuki_automorphism_two_rank m (by omega))

end CFSG.Quasithin.Chapter7.NormalizedSource
