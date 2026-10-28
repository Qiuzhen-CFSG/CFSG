module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Contracts
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Actors
public import Theory.Representation.BinaryNaturalDual.FiveActors.ModuleGeometry.Rank
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Rank four and standard graph operators on the original binary module

The existing S₆ elementary-rank calculation sharpens the outer actor bound
from five to four. Faithful conjugation transports that bound to the original
linear normalizer. Symmetric Gram factorization then conjugates any outer
involution to inverse transpose, using an operator from the actual SL₅ image.
Conjugacy preserves its fixed codimension, which is bounded by the common
fixed-space codimension of the original actor.

The resulting witness is used in `Graph` with the two standard displacement
contracts. No representation classification or fixed-space estimate is inferred
from the automorphism-group geometry alone.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 4.8(3),
manuscript p.27. The fixed-group normalization is the checked degree-five
geometry of Aschbacher–Smith E.6.23 and H.9.2(1).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open BinaryLinear.OuterCyclic

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) SL5TenDimensional.Group V)

/-- The fixed S₆ has elementary two-rank three; the graph quotient adds one. -/
theorem outer_rank_le_four (hf : Function.Injective σ) (hi : IsIrreducible σ)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hout : ¬ A ≤ (actionImage σ).subgroupOf (linearNormalizer σ)) : rank A ≤ 4 := by
  let : IsElementaryAbelian 2 A := hA.2
  let f := linearConjugation σ hf
  let E := A.map f
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map f
  have hE : ¬ E ≤ MulAut.innerSubgroup (LinearGroup 5) := by
    intro hE
    apply hout
    intro t ht
    apply involution_mem_image_of_inner σ hf hi t
      (elemPow_eq_one_of_isElementaryAbelian t ht)
    obtain ⟨x, hx⟩ := hE (mem_map_of_mem f ht)
    obtain ⟨g, hg⟩ := (MulAut.congr_inner_iff (slEquivLinear 5)
      (conjugation σ hf t)).mp ⟨x, hx.symm⟩
    exact ⟨g, hg.symm⟩
  have hr := BinaryNaturalDual.FiveActors.ModuleGeometry.outer_elementary_rank_le_four E hE
  have hj : Function.Injective (f.comp A.subtype) :=
    (MulAut.congr (slEquivLinear 5)).injective.comp
      (conjugation_injective_on_elementary σ hf hi A)
  have heq : Nat.card A = Nat.card E := by
    have he : (f.comp A.subtype).range = E := by
      ext x
      change (∃ a : A, f a = x) ↔ ∃ a, a ∈ A ∧ f a = x
      constructor
      · rintro ⟨a, ha⟩
        exact ⟨a, a.property, ha⟩
      · rintro ⟨a, ha, hax⟩
        exact ⟨⟨a, ha⟩, hax⟩
    rw [← he]
    exact Nat.card_congr (MonoidHom.ofInjective hj).toEquiv
  have ht : IsElementaryAbelian 2 (⊤ : Subgroup E) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) x.val)) }
  have hcard := (primeRank_le_iff_elementary_card_le E).mp hr ⊤ ht
  have hcardA : Nat.card A ≤ 2 ^ 4 := by
    rw [heq]
    simpa only [Nat.card_congr Subgroup.topEquiv.toEquiv] using hcard
  have hl := Nat.log_mono_right (b := 2) hcardA
  simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hl

/-- Conjugation by a literal image operator induces the marked inner automorphism. -/
theorem conjugation_embedding (hf : Function.Injective σ) (g : SL5TenDimensional.Group) :
    conjugation σ hf (normalizerEmbedding σ g) = MulAut.conj g := by
  ext x : 1
  apply (show Function.Injective σ.asGroupHom from fun _ _ h => hf (congrArg Units.val h))
  rw [conjugation_apply]
  change σ.asGroupHom g * σ.asGroupHom x * (σ.asGroupHom g)⁻¹ =
    σ.asGroupHom (g * x * g⁻¹)
  simp only [map_mul, map_inv]

/-- The same identity in the binary linear-group coordinates. -/
theorem linearConjugation_embedding (hf : Function.Injective σ)
    (g : SL5TenDimensional.Group) :
    linearConjugation σ hf (normalizerEmbedding σ g) =
      MulAut.conj (slEquivLinear 5 g) := by
  change MulAut.congr (slEquivLinear 5)
    (conjugation σ hf (normalizerEmbedding σ g)) = _
  rw [conjugation_embedding, MulAut.congr_conj]

/-- Conjugation by an actual SL₅ operator normalizes an outer involution to inverse transpose. -/
theorem exists_standard_graph_conjugate (hf : Function.Injective σ)
    (hi : IsIrreducible σ) (t : linearNormalizer σ) (ht : t ^ 2 = 1)
    (hout : t.val ∉ actionImage σ) :
    ∃ g : SL5TenDimensional.Group,
      linearConjugation σ hf
        (normalizerEmbedding σ g * t * (normalizerEmbedding σ g)⁻¹) = graphLinear 5 := by
  let f := linearConjugation σ hf
  have ht' : (f t) ^ 2 = 1 := by rw [← map_pow, ht, map_one]
  have hout' : f t ∉ MulAut.innerSubgroup (LinearGroup 5) := by
    rintro ⟨x, hx⟩
    obtain ⟨g, hg⟩ := (MulAut.congr_inner_iff (slEquivLinear 5)
      (conjugation σ hf t)).mp ⟨x, hx.symm⟩
    exact hout (involution_mem_image_of_inner σ hf hi t ht ⟨g, hg.symm⟩)
  obtain ⟨g, hg⟩ := BinaryNaturalDual.FiveActors.outer_conjugate_graph (f t) ht' hout'
  refine ⟨(slEquivLinear 5).symm g, ?_⟩
  rw [map_mul, map_mul, map_inv, linearConjugation_embedding,
    (slEquivLinear 5).apply_symm_apply]
  exact hg

variable [FiniteDimensional (ZMod 2) V]

/-- A standard graph involution displaces at most the common fixed-space codimension of A.
The chosen operator is conjugate to a member of A; membership in A after conjugation is not claimed. -/
theorem exists_standard_graph_with_codim_le (hf : Function.Injective σ)
    (hi : IsIrreducible σ) (A : Subgroup (linearNormalizer σ))
    (hA : IsElementaryTwo A)
    (hout : ¬ A ≤ (actionImage σ).subgroupOf (linearNormalizer σ)) :
    ∃ t : linearNormalizer σ, IsStandardGraph σ t ∧
      fixedCodim (normalizerRepresentation σ) (zpowers t) ≤
        fixedCodim (normalizerRepresentation σ) A := by
  obtain ⟨t, htA, ht2, htout, _⟩ := exists_graph_actor σ hf hi A hA hout
  obtain ⟨g, hg⟩ := exists_standard_graph_conjugate σ hf hi t ht2 htout
  let c := normalizerEmbedding σ g
  let s := c * t * c⁻¹
  have hs2 : s ^ 2 = 1 := by
    change (MulAut.conj c t) ^ 2 = 1
    rw [← map_pow, ht2, map_one]
  have hs : conjugation σ hf s = graphSL 5 := by
    apply (MulAut.congr (slEquivLinear 5)).injective
    exact hg
  refine ⟨s, ⟨hs2, ?_⟩, ?_⟩
  · intro x
    rw [← conjugation_apply σ hf, hs]
  · change fixedCodim (normalizerRepresentation σ) (zpowers (c * t * c⁻¹)) ≤ _
    rw [fixedCodim_zpowers_conj]
    have hfix := Submodule.finrank_mono
      (fixedSpace_antitone (normalizerRepresentation σ) (zpowers_le.mpr htA))
    have h1 := fixedCodim_add_finrank (normalizerRepresentation σ) (zpowers t)
    have h2 := fixedCodim_add_finrank (normalizerRepresentation σ) A
    omega

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph
