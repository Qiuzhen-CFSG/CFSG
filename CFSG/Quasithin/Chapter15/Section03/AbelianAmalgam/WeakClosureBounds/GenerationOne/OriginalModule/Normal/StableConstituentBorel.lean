module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Normal.StableConstituent
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.RankTwoMarkings.SLThree
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.RankTwoMarkings.SpFour
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.BorelMarkings.RankOne

/-!
# The Borel calculation for recognized stable constituents

Sylow conjugacy aligns the component Borel with the classifier's natural
module while conjugating the module coordinates by the same element. The
proved SL₂, Suzuki, SL₃ and Sp₄ Borel calculations then give zero fixed space.

For an original irreducible component action, the nontrivial central-kernel
argument preserves the common quadratic actor's rank in the faithful image.
The whole generalized Fitting subgroup is its embedded component. Recognition
and pullback therefore prove the Borel assertion on the original representation,
without an assumed classification or an assumed compatible Borel marking.

Source: Aschbacher–Smith, F.9.18(3–4), pp.325–326; B.4.2–5, pp.86–87;
and the fixed-space deduction in 15.3.65, p.1152.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Matrix
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal
open RepresentationReduction.SourceRestrictions.Cases
open Single.SmallRatio RepresentationReduction.SourceRestrictions
open RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity
universe u v
variable {D : Type u} [Group D] [Finite D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) {L H : Subgroup D} {f : ℕ}

section BorelConsumer
open RepresentationReduction
open RepresentationReduction.SourceRestrictions.Cases.Single.RankTwoMarkings
open RepresentationReduction.SourceRestrictions.Cases.Exchanged.BorelMarkings

private theorem fixedSpace_eq_bot_of_natural_normalizer
    {J E W X : Type*} [Group J] [Group E] [Finite J] [Finite E]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) J W} {τ : Representation (ZMod 2) E X}
    (a : ActionEquiv σ τ) (B : Subgroup J) (C : Subgroup E)
    (hB : ∃ P : Sylow 2 J, normalizer (P : Set J) = B)
    (hC : ∃ P : Sylow 2 E, normalizer (P : Set E) = C)
    (hzero : fixedSpace τ C = ⊥) : fixedSpace σ B = ⊥ := by
  obtain ⟨g, hg, he⟩ := exists_innerIntertwiner_sylowNormalizer B C hB hC
    σ τ a.groupEquiv a.linearEquiv a.intertwines
  exact fixedSpace_eq_bot_of_equivariant σ τ
    (a.groupEquiv.trans (MulAut.conj g)).toMonoidHom
    (a.linearEquiv.trans (innerIntertwiner τ g)) he B C hg hzero

/-- Every recognized natural constituent has zero fixed space for the actual
Sylow-two normalizer, independently of the classifier's initial marking. -/
theorem fixedSpace_eq_bot_of_naturalConstituent
    (h : NaturalConstituent ρ L f) (hf : 1 < f) (B : Subgroup L)
    (hB : ∃ P : Sylow 2 L, normalizer (P : Set L) = B) :
    fixedSpace (ρ.comp L.subtype) B = ⊥ := by
  cases h with
  | linearTwo F hF a =>
    exact fixedSpace_eq_bot_of_natural_normalizer a B
      (Matrix.SpecialLinearGroup.rankOneBorel F.Carrier) hB slTwo_borel_normalizer
      (slTwo_borel_fixedSpace_eq_bot (field_card_gt_two hF hf))
  | suzuki m hm he hF a =>
    exact fixedSpace_eq_bot_of_natural_normalizer a B (SuzukiBorelSubgroup m) hB
      (suzuki_borel_normalizer m hm) (RemainingModels.suzuki_borel_fixedSpace_eq_bot m hm)
  | linearThree F hF a =>
    exact fixedSpace_eq_bot_of_natural_normalizer a B (Matrix.PSL3.LinearThree.borelSL F.Carrier) hB
      (slThree_borel_normalizer hF (by omega))
      (slThree_borel_fixedSpace_eq_bot (field_card_gt_two hF hf))
  | symplecticFour F hF a =>
    exact fixedSpace_eq_bot_of_natural_normalizer a B
      (Theory.SpecificGroups.SymplecticFour.borel (F := F.Carrier)) hB
      (spFour_borel_normalizer hF (by omega))
      (spFour_borel_fixedSpace_eq_bot (field_card_gt_two hF hf))

variable [FiniteDimensional (ZMod 2) V]

/-- The source recognition and marked Borel calculation on the original action. -/
theorem fixedSpace_eq_bot_of_sourceModel
    (hyp : ChapterK.RankOne.SourceHypotheses ρ L) (hq : quadraticRatio ρ ≤ 2)
    (hs : SourceModel (L ⧸ center L) f) (hf : 1 < f) (ho : Odd f)
    (hz : center L = ⊥) (B : Subgroup L)
    (hB : ∃ P : Sylow 2 L, normalizer (P : Set L) = B) :
    fixedSpace (ρ.comp L.subtype) B = ⊥ :=
  fixedSpace_eq_bot_of_naturalConstituent ρ (natural_of_sourceModel ρ hyp hq hs hf ho hz) hf B hB


/-- The same vanishing for a subgroup of the whole actor, using its literal
intersection with the recognized component. -/
theorem fixedSpace_eq_bot_of_sourceModel_ambient
    (hyp : ChapterK.RankOne.SourceHypotheses ρ L) (hq : quadraticRatio ρ ≤ 2)
    (hs : SourceModel (L ⧸ center L) f) (hf : 1 < f) (ho : Odd f)
    (hz : center L = ⊥) (B : Subgroup D)
    (hB : ∃ P : Sylow 2 L, normalizer (P : Set L) = B.subgroupOf L) :
    fixedSpace ρ B = ⊥ := by
  have hzero := fixedSpace_eq_bot_of_sourceModel ρ hyp hq hs hf ho hz (B.subgroupOf L) hB
  apply bot_unique
  intro v hv
  have hv' : v ∈ fixedSpace (ρ.comp L.subtype) (B.subgroupOf L) := by
    intro b
    exact hv ⟨b.val.val, b.property⟩
  simpa only [hzero] using hv'

end BorelConsumer


section ComponentConsumer
variable {D V : Type u} [Group D] [Finite D] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal]
    [IsQuasisimple K] {f : ℕ}
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure

/-- Recognize the original irreducible component action through its faithful
image, preserving the component map and the original quadratic actor. -/
theorem natural_of_irreducible_component
    (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hquot : IsPGroup 2 (D ⧸ K)) (hZ : center K = ⊥)
    (hi : IsIrreducible (ρ.comp K.subtype)) (hn : ¬ (⊤ : Submodule (ZMod 2) V) ≤ fixedSpace ρ K)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A) (hAC : A ⊓ centralizer (K : Set D) = ⊥)
    (hm : SourceModel (K ⧸ center K) f) (hf : 1 < f) (ho : Odd f) :
    NaturalConstituent ρ K f := by
  have hnact : ¬ ∀ k ∈ K, ∀ v, ρ k v = v := by
    intro h
    apply hn
    intro v _ k
    exact h k k.property v
  have hsurvive : ¬ K ≤ (actionHom ρ).ker := by
    intro h
    exact hnact (fun k hk v => (actionHom_eq_one_iff ρ k).mp (h hk) v)
  have hfaith := faithful_on_section_of_central_kernel ρ K A hAC
    (central_kernel_of_quasisimple ρ K hnact)
  have hbound : quadraticRatio (imageRepresentation ρ) ≤ 2 := by
    apply (quadraticRatio_le_two_iff _).mpr
    refine ⟨actionSubgroup ρ A, hA.actionSubgroup ρ hfaith, ?_, ?_⟩
    · rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩ v
      exact hq x hx y hy v
    · rw [fixedCodim_actionSubgroup, actionSubgroup_rank ρ A hfaith]
      exact hc
  obtain ⟨hqs, hirr, hfit⟩ := image_structure ρ K hsurvive hquot hi
  let e : K ≃* generalizedFitting (actionImage ρ) :=
    (componentEquiv ρ K hsurvive hZ).trans (MulEquiv.subgroupCongr hfit.symm)
  have hyp : B4Hypotheses KnownSimple.IsKnownSimple (imageRepresentation ρ) := by
    refine ⟨image_sqtk ρ K hsurvive hs hquot hZ, imageRepresentation_injective ρ, ?_, ?_⟩
    · rw [hfit]
      exact hqs
    · rw [hfit]
      exact hirr
  have hrec := natural_of_B4_source (imageRepresentation ρ) hyp hbound
    (hm.transport (centralQuotientCongr e).symm) hf ho (centerless_of_equiv hZ e)
  cases hrec with
  | linearTwo F hF a =>
    exact .linearTwo F hF ⟨e.trans a.groupEquiv, a.linearEquiv, fun k v => a.intertwines (e k) v⟩
  | suzuki m hm he hF a =>
    exact .suzuki m hm he hF ⟨e.trans a.groupEquiv, a.linearEquiv, fun k v => a.intertwines (e k) v⟩
  | linearThree F hF a =>
    exact .linearThree F hF ⟨e.trans a.groupEquiv, a.linearEquiv, fun k v => a.intertwines (e k) v⟩
  | symplecticFour F hF a =>
    exact .symplecticFour F hF ⟨e.trans a.groupEquiv, a.linearEquiv, fun k v => a.intertwines (e k) v⟩

/-- The Borel calculation on a literal irreducible component action, with all
faithful-image recognition and marking transport discharged. -/
theorem fixedSpace_eq_bot_of_irreducible_component
    (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hquot : IsPGroup 2 (D ⧸ K)) (hZ : center K = ⊥)
    (hi : IsIrreducible (ρ.comp K.subtype)) (hn : ¬ (⊤ : Submodule (ZMod 2) V) ≤ fixedSpace ρ K)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A) (hAC : A ⊓ centralizer (K : Set D) = ⊥)
    (hm : SourceModel (K ⧸ center K) f) (hf : 1 < f) (ho : Odd f)
    (B : Subgroup K) (hB : ∃ P : Sylow 2 K, normalizer (P : Set K) = B) :
    fixedSpace (ρ.comp K.subtype) B = ⊥ :=
  fixedSpace_eq_bot_of_naturalConstituent ρ
    (natural_of_irreducible_component ρ K hs hquot hZ hi hn A hA hq hc hAC hm hf ho) hf B hB

end ComponentConsumer


end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal
