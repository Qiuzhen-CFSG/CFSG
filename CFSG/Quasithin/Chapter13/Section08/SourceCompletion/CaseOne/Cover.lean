module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.Commutators
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.CoverSeed
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.MarkedModels

/-!
# The five-dimensional cover branch of the nonabelian-span exclusion

On the original critical pair, the full-denominator commutator is A₁.
Its image in the literal augmentation cover is a transvection center,
so it cannot enter any H-conjugate of V₃. Critical distance three would
force exactly that containment. Thus the distance exceeds three and
F.9 proves that U_L is abelian.

The final application constructs the cover coordinates from the supplied
StarAction and the earlier compatible whole-module marking. Consequently
any nonabelian case has the four-dimensional natural model, with the same
actor and seed marking. No abelianness, chief count or strict denominator
is assumed. Full denominators are the case-(1) branch assumptions.
The natural nonabelian branch and the subsequent Steinberg/permutation
comparisons remain obligations of `qt-d-138-a6-endgame-source`.

Source: Aschbacher--Smith, Lemma 13.8.33, printed pp.966--967. The earlier
ordinary setup and markings remain with `qt-d-138-six-g2-source`.
-/

public section
open Subgroup BinaryPermutation
open scoped IsMulCommutative


namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open CriticalGeometry CriticalGeometry.AsymmetricPair.CoverHyperplanes
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.SixAndG2.Overgroup
open Representation.SixLetterRadicalDisplacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The original endpoint line misses every H-conjugate of the seed in
the marked cover branch. -/
theorem cover_center_avoids_seed
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (C : CoverCoordinates H V₃ V₁) (hseed : C.image V₃ = W) :
    ∀ h : H, ¬ c.Aone V₁ ≤ V₃.conjBy (h : G) := by
  intro h
  have hg := local_earlierGeometry d hF9 c
  have hB : Source.starImage H c.Vgamma ≠ ⊥ := by
    intro he
    apply full_denominators_escape d hF9 c hDH hDg hcentral
    intro x hx
    let xH : H := ⟨x, hg.Vgamma_H hx⟩
    have hq : QuotientGroup.mk' (pCore 2 H) xH ∈ Source.starImage H c.Vgamma :=
      ⟨xH, hx, rfl⟩
    rw [he, mem_bot] at hq
    exact ⟨xH, (QuotientGroup.eq_one_iff xH).mp hq, rfl⟩
  have hcard : Nat.card (c.Aone V₁) = 2 := by
    change Nat.card (V₁.map (MulAut.conj (c.gb : G)).toMonoidHom) = 2
    rw [card_map_of_injective (MulAut.conj (c.gb : G)).injective, d.line_card]
  exact A6Endgame.ActionAnalysis33.cover_center_not_le_seed_conjugate C hseed
    c.Vgamma (c.Aone V₁) hg.Vgamma_H hB hcard hg.lines_disjoint
    (endpoint_commutator d hF9 c hDH hDg hcentral).1 h

/-- The source cover branch has critical distance strictly greater than three. -/
theorem cover_length_gt_three
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (C : CoverCoordinates H V₃ V₁) (hseed : C.image V₃ = W) :
    3 < c.path.length := by
  have hb := (local_earlierGeometry d hF9 c).length
  by_contra hn
  have he : c.path.length = 3 := by omega
  obtain ⟨h, hh⟩ := seed_placement_of_length_three d hF9 c hDH hDg hcentral he
  exact cover_center_avoids_seed d hF9 c hDH hDg hcentral C hseed h hh

/-- The nonabelian-span alternative is impossible for the marked cover. -/
theorem cover_span_abelian
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (C : CoverCoordinates H V₃ V₁) (hseed : C.image V₃ = W) :
    IsMulCommutative (Source.UL L H V₃) := by
  apply f9_UL_abelian_of_length_gt_three
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H) hF9 c
  exact cover_length_gt_three d hF9 c hDH hDg hcentral C hseed

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne

namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open CriticalGeometry CriticalGeometry.AsymmetricPair.CoverHyperplanes
open TransvectionRecognition.Component.ModelExtension
open A6Endgame.IntersectionBalance
open Representation.SixLetterRadicalDisplacement
variable {G : Type*} [Group G] {H V₃ V₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

private noncomputable def augmentationCoordinates
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] U)
    (hF : ∀ g v, F (tildeRepresentation H _ V₁ a g v) =
      coreRepresentation (Fin 6) (e g) (F v)) : CoverCoordinates H V₃ V₁ where
  groupEquiv := e
  linearEquiv := F
  normalizes := le_normalizer_conjugateSpanBy V₃ H
  intertwines h u := (hF (QuotientGroup.mk' (pCore 2 H) h)
    (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u))).symm.trans
      (congrArg (fun x => F (Additive.ofMul x)) (a.conjugation h u))

private theorem augmentationCoordinates_image
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] U)
    (hF : ∀ g v, F (tildeRepresentation H _ V₁ a g v) =
      coreRepresentation (Fin 6) (e g) (F v)) (X : Subgroup G) :
    (augmentationCoordinates a e F hF).image X =
      (quotientSpace (Source.UH H V₃) V₁ X).map F.toLinearMap := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u.toMul),
      ⟨u.toMul, hu, rfl⟩, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨u, hu, he⟩ := hv
    exact ⟨Additive.ofMul u, hu, congrArg (fun x => F (Additive.ofMul x)) he⟩

variable [Finite G] {T : Sylow 2 G} {L V V₂ M G₁ : Subgroup G}

/-- The surviving nonabelian branch has the actual natural coordinates,
including the unchanged actor and seed marking. -/
theorem natural_model_of_nonabelian
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (hn : ¬ IsMulCommutative (Source.UL L H V₃)) :
    ∃ F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6),
      (∀ g v, F (tildeRepresentation H _ V₁ a g v) =
        naturalRepresentation (Fin 6) (e g) (F v)) ∧
      (quotientSpace (Source.UH H V₃) V₁ V₃).map F.toLinearMap =
        Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.canonicalPlane := by
  rcases model.marked_cases a e with hm | ⟨F, hF, hp⟩
  · exact hm
  · exact (hn (cover_span_abelian d hF9 c hDH hDg hcentral
      (augmentationCoordinates a e F hF) (by rw [augmentationCoordinates_image, hp]))).elim

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
