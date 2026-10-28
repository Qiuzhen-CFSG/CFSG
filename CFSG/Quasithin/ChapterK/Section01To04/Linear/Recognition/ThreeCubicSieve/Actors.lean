module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.Setup
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.Transport
public import Theory.Representation.Quotient
public import Theory.Representation.BinaryOffender.CubicConjugateBound.CentralQuotient
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# The actual SL₃ cover and its ambient cubic actor

Inflating along the supplied central cover preserves irreducibility and has
exactly the covering kernel. Its image is the original component image, so the
original ambient action embeds in the same linear normalizer even when the
SL₃ action is not faithful. The elementary cubic actor, its rank, and its fixed
codimension are transported through this literal embedding. Its membership in
the component image is equivalent to membership of the original actor in L.

Source: Aschbacher–Smith, K.3.2 and Chapter K standing hypotheses, printed
pp.451,454–456; GM04 Proposition 4.6/Table 7. No structural hypothesis on the
full linear normalizer or cubic bound on the restricted action is used.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve

open Representation Representation.BinaryOffender Theory.GroupTheory Subgroup
open ChapterB.QuasisimpleSource

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {L : Subgroup G}
    {B : BinaryField} (C : LinearCover B 3 L)

/-- The literal action to which the absolute SL₃ catalogue applies. -/
abbrev inflated : Representation (ZMod 2)
    (Matrix.SpecialLinearGroup (Fin 3) B.Carrier) V :=
  (ρ.comp L.subtype).comp C.projection

/-- The kernel is the supplied covering kernel, not necessarily trivial. -/
theorem inflated_kernel (hf : Function.Injective ρ) :
    (inflated ρ C).ker = C.projection.ker := by
  ext g
  change ρ (C.projection g : G) = 1 ↔ C.projection g = 1
  constructor
  · intro hg
    apply Subtype.ext
    apply hf
    change ρ (C.projection g : G) = ρ 1
    exact hg.trans ρ.map_one.symm
  · intro hg
    rw [hg]
    exact ρ.map_one

theorem inflated_central_kernel (hf : Function.Injective ρ) :
    (inflated ρ C).ker ≤ center _ := by
  rw [inflated_kernel ρ C hf]
  exact C.central_kernel

/-- Surjectivity of the actual covering map preserves irreducibility. -/
theorem inflated_irreducible (hi : IsIrreducible (ρ.comp L.subtype)) :
    IsIrreducible (inflated ρ C) :=
  (irreducible_comp_surjective_iff C.projection C.surjective
    (ρ.comp L.subtype)).mpr hi

/-- Faithfulness on the nontrivial quasisimple component gives nontrivial
inflated action, without asserting faithfulness on the cover. -/
theorem inflated_nontrivial {K : GroupClass} (h : SourceHypothesis K ρ L) :
    ∃ g, inflated ρ C g ≠ 1 := by
  let : IsQuasisimple L := h.quasisimple
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  obtain ⟨l, hl⟩ := exists_ne (1 : L)
  obtain ⟨g, hg⟩ := C.surjective l
  refine ⟨g, ?_⟩
  intro he
  apply hl
  apply L.subtype_injective
  apply h.faithful
  change ρ (l : G) = ρ 1
  change ρ (C.projection g : G) = 1 at he
  rw [hg] at he
  exact he.trans ρ.map_one.symm

/-- Inflation changes neither the literal component image nor its normalizer. -/
theorem inflated_image : actionImage (inflated ρ C) = actionImage (ρ.comp L.subtype) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨C.projection g, Units.ext rfl⟩
  · rintro ⟨l, rfl⟩
    obtain ⟨g, rfl⟩ := C.surjective l
    exact ⟨g, Units.ext rfl⟩

/-- The original ambient action, marked in the inflated action's normalizer. -/
def ambientToNormalizer [L.Normal] : G →* linearNormalizer (inflated ρ C) :=
  ρ.asGroupHom.codRestrict _ (by
    intro g
    have hg := actionImage_le_linearNormalizer ρ L ⟨g, rfl⟩
    change ρ.asGroupHom g ∈ normalizer (actionImage (inflated ρ C) : Set _)
    rwa [inflated_image])

theorem ambientToNormalizer_injective [L.Normal] (hf : Function.Injective ρ) :
    Function.Injective (ambientToNormalizer ρ C) := by
  intro g k he
  exact hf (congrArg (fun x : linearNormalizer (inflated ρ C) => x.val.val) he)

@[simp] theorem ambientToNormalizer_apply [L.Normal] (g : G) (v : V) :
    normalizerRepresentation (inflated ρ C) (ambientToNormalizer ρ C g) v = ρ g v := rfl

/-- Inner and outer operators are distinguished using the actual image of the
possibly nonfaithful cover. -/
theorem ambientToNormalizer_mem_image_iff [L.Normal] (hf : Function.Injective ρ) (g : G) :
    (ambientToNormalizer ρ C g).val ∈ actionImage (inflated ρ C) ↔ g ∈ L := by
  rw [inflated_image]
  constructor
  · rintro ⟨l, hl⟩
    have he : (l : G) = g := hf (congrArg Units.val hl)
    exact he ▸ l.property
  · intro hg
    exact ⟨⟨g, hg⟩, Units.ext rfl⟩

/-- The source central quotient bounds the original ambient rank. -/
theorem source_twoRank_le {K : GroupClass} (h : SourceHypothesis K ρ L)
    (e : L ⧸ center L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) B.Carrier)
    (hr : primeRank 2 (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) B.Carrier))
      ≤ 2 * B.degree) : primeRank 2 G ≤ 2 * B.degree := by
  let : Finite G := h.finite_group
  let : L.Normal := h.fitting ▸ inferInstance
  let : IsQuasisimple L := h.quasisimple
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  exact (primeRank_le_central_quotient_automorphisms_of_irreducible ρ L h.faithful e).trans hr

/-- The original cubic actor is retained in the normalizer, including its
fixed codimension and the intrinsic rank bound. -/
theorem source_actor {K : GroupClass} (h : SourceHypothesis K ρ L)
    (e : L ⧸ center L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) B.Carrier)
    (hr : primeRank 2 (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) B.Carrier))
      ≤ 2 * B.degree) :
    ∃ A : Subgroup (linearNormalizer (inflated ρ C)),
      IsElementaryTwo A ∧ IsCubic (normalizerRepresentation (inflated ρ C)) A ∧
      rank A ≤ 2 * B.degree ∧
      fixedCodim (normalizerRepresentation (inflated ρ C)) A ≤ 2 * rank A := by
  let : Finite G := h.finite_group
  let : L.Normal := h.fitting ▸ inferInstance
  obtain ⟨D, hD, hc, hd⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.cubic_le_two
  have hcard := (primeRank_le_iff_elementary_card_le G).mp
    (source_twoRank_le ρ h e hr) D hD.2
  have hD_rank : rank D ≤ 2 * B.degree := by
    have hh := Nat.log_mono_right (b := 2) hcard
    simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh
  let f := ambientToNormalizer ρ C
  have hf := ambientToNormalizer_injective ρ C h.faithful
  obtain ⟨he, hc', hd'⟩ := Exceptional.cubic_actor_map_equivariant ρ
    (normalizerRepresentation (inflated ρ C)) f hf (LinearEquiv.refl _ _)
    (fun _ _ => rfl) hD hc hd
  exact ⟨D.map f, he, hc', (rank_map_injective f hf D).trans_le hD_rank, hd'⟩

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve
