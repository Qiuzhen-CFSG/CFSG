module
public import Theory.Representation.G2.NaturalBorelFixed
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.G2Recognition
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Normal.QuadraticModules

/-!
# Normal G₂ components and their original Borel fixed spaces

On each nontrivial irreducible factor, pass through the actual faithful image.
The quadratic actor retains its rank and codimension bound there, so the genuine
B.4.2 recognition theorem identifies the component action with the natural G₂
six-space. Sylow conjugacy aligns its Borel with the original one. The natural
Borel has zero fixed space; odd-index traces extend the fixed-space equality
through arbitrary invariant extensions. Restriction to the component and the
common actor then gives the literal original-action statement.

The source consumer in Classification/Sieve/G2 discharges these premises from
the original terminal setup and excludes the G₂ model. No action recognition,
Borel marking, or irreducible-factor callback is assumed by that consumer.
Source: Aschbacher--Smith 14.6.20, p.1037, and B.4.2(4), p.86.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.NormalG2
open ChapterB.QuasisimpleSource
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open OriginalModule.Normal RepresentationReduction
open RepresentationReduction.SourceRestrictions
open RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity
open Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure
universe u
variable {D V : Type u} [Group D] [Finite D] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal] [IsQuasisimple K]

/-- Recognize the literal nontrivial component action through its faithful image. -/
theorem natural_of_irreducible_component
    (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hquot : IsPGroup 2 (D ⧸ K)) (hZ : center K = ⊥)
    (hi : IsIrreducible (ρ.comp K.subtype))
    (hn : ¬ (⊤ : Submodule (ZMod 2) V) ≤ fixedSpace ρ K)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A) (hAC : A ⊓ centralizer (K : Set D) = ⊥)
    (F : BinaryField) (hF : 1 < F.degree)
    (eK : (K ⧸ center K) ≃* Atlas.G2.Model F.Carrier) :
    Nonempty (ActionEquiv (ρ.comp K.subtype) (binaryG2 F)) := by
  let : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
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
    refine ⟨actionSubgroup ρ A,hA.actionSubgroup ρ hfaith,?_,?_⟩
    · rintro a ⟨x,hx,rfl⟩ b ⟨y,hy,rfl⟩ v
      exact hq x hx y hy v
    · rw [fixedCodim_actionSubgroup,actionSubgroup_rank ρ A hfaith]
      exact hc
  obtain ⟨hqs,hirr,hfit⟩ := image_structure ρ K hsurvive hquot hi
  let e : K ≃* generalizedFitting (actionImage ρ) :=
    (componentEquiv ρ K hsurvive hZ).trans (MulEquiv.subgroupCongr hfit.symm)
  have hyp : ChapterK.RankOne.SourceHypotheses (imageRepresentation ρ)
      (generalizedFitting (actionImage ρ)) := by
    refine ⟨image_sqtk ρ K hsurvive hs hquot hZ,rfl,?_,imageRepresentation_injective ρ,?_,?_⟩
    · rw [hfit]; exact hqs
    · rw [hfit]; exact hirr
    · exact (cubicRatio_le_quadraticRatio _).trans hbound
  obtain ⟨a⟩ := ChapterB.SourceClassification.g2_natural_action hyp F hF
    ((centralQuotientCongr e).symm.trans eK)
  exact ⟨⟨e.trans a.groupEquiv,a.linearEquiv,fun k v => a.intertwines (e k) v⟩⟩

/-- The original marked Borel has zero fixed space on every nontrivial irreducible factor. -/
theorem fixedSpace_eq_bot_of_irreducible_component
    (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hquot : IsPGroup 2 (D ⧸ K)) (hZ : center K = ⊥)
    (hi : IsIrreducible (ρ.comp K.subtype))
    (hn : ¬ (⊤ : Submodule (ZMod 2) V) ≤ fixedSpace ρ K)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A) (hAC : A ⊓ centralizer (K : Set D) = ⊥)
    (F : BinaryField) (hF : 1 < F.degree)
    (eK : (K ⧸ center K) ≃* Atlas.G2.Model F.Carrier)
    (B : Subgroup K) (hB : ∃ P : Sylow 2 K, normalizer (P : Set K) = B) :
    fixedSpace (ρ.comp K.subtype) B = ⊥ := by
  obtain ⟨a⟩ := natural_of_irreducible_component ρ K hs hquot hZ hi hn A hA hq hc hAC F hF eK
  have hmodel : ∃ P : Sylow 2 (Atlas.G2.Model F.Carrier),
      normalizer (P : Set (Atlas.G2.Model F.Carrier)) = Atlas.G2.borel :=
    ⟨Atlas.G2.LieParabolicSetup.sylow,Atlas.G2.SylowNormalizer.normalizer_unipotent⟩
  obtain ⟨g,hg,he⟩ := exists_innerIntertwiner_sylowNormalizer B Atlas.G2.borel hB hmodel
    (ρ.comp K.subtype) (binaryG2 F) a.groupEquiv a.linearEquiv a.intertwines
  apply fixedSpace_eq_bot_of_equivariant (ρ.comp K.subtype) (binaryG2 F)
    (a.groupEquiv.trans (MulAut.conj g)).toMonoidHom
    (a.linearEquiv.trans (innerIntertwiner (binaryG2 F) g)) he B Atlas.G2.borel hg
  apply Atlas.G2.Natural.BorelFixed.fixedSpace_eq_bot
  rw [F.card_eq]
  exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hF

/-- Odd-index traces carry the irreducible calculation through the entire module. -/
theorem fixedSpace_le_of_quadratic_supplement
    (hZ : center K = ⊥) (A : Subgroup D) (hgen : K ⊔ A = ⊤)
    (hs : IsSQTK KnownSimple.IsKnownSimple D) (hquot : IsPGroup 2 (D ⧸ K))
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A) (hAC : A ⊓ centralizer (K : Set D) = ⊥)
    (F : BinaryField) (hF : 1 < F.degree)
    (eK : (K ⧸ center K) ≃* Atlas.G2.Model F.Carrier)
    (B : Subgroup K) (hB : ∃ P : Sylow 2 K, normalizer (P : Set K) = B) :
    fixedSpace (ρ.comp K.subtype) B ≤ fixedSpace (ρ.comp K.subtype) ⊤ := by
  obtain ⟨P,hP⟩ := hB
  have hindex : Odd B.index := odd_index_of_sylow_le P B (hP ▸ le_normalizer)
  apply fixedSpace_le_by_quadratic_irreducibles K A B hindex ?_ ρ hq hc
  intro W _ _ _ σ hi hq hc
  by_cases hn : (⊤ : Submodule (ZMod 2) W) ≤ fixedSpace σ K
  · intro w hw k
    exact hn Submodule.mem_top k.val
  · have hK := component_irreducible_of_quadratic_supplement σ K A hZ hgen hA hq hc hAC hi hn
    rw [fixedSpace_eq_bot_of_irreducible_component σ K hs hquot hZ hK hn
      A hA hq hc hAC F hF eK B ⟨P,hP⟩]
    exact bot_le

/-- Restrict to the actual component and common actor, retaining the original Borel. -/
theorem fixedSpace_le_of_quadratic_actor
    (hZ : center K = ⊥) (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A) (hAC : A ⊓ centralizer (K : Set D) = ⊥)
    (F : BinaryField) (hF : 1 < F.degree)
    (eK : (K ⧸ center K) ≃* Atlas.G2.Model F.Carrier)
    (B : Subgroup K) (hB : ∃ P : Sylow 2 K, normalizer (P : Set K) = B) :
    fixedSpace (ρ.comp K.subtype) B ≤ fixedSpace (ρ.comp K.subtype) ⊤ := by
  let : IsQuasisimple (K.subgroupOf (K ⊔ A)) := componentInSup_quasisimple K A
  apply fixedSpace_le_of_componentInSup ρ K A B
  exact fixedSpace_le_of_quadratic_supplement (ρ.comp (K ⊔ A).subtype)
    (K.subgroupOf (K ⊔ A)) (componentInSup_center K A hZ) (A.subgroupOf (K ⊔ A))
    (componentInSup_generated K A) (hs.subgroup (K ⊔ A)) (componentInSup_quotient K A hA)
    (actorInSup_elementary K A hA) (actorInSup_quadratic ρ K A hq)
    (actorInSup_bound ρ K A hc) (actorInSup_faithful K A hAC) F hF
    ((centralQuotientCongr (componentInSupEquiv K A)).trans eK)
    (borelInSup K A B) (borelInSup_sylow K A B hB)

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.NormalG2
