module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Normal.QuadraticModules

public import Theory.Representation.OrthogonalFourMinusRankOne.BorelFixed

/-!
# The normal PSL₂ Borel above field order four

Pass through the faithful image of each nontrivial irreducible component
factor. K.3.1 recognizes either the natural column module or the Hermitian
module over its actual half-field. Both have zero Borel fixed space when
the defining field has more than four elements. Sylow conjugacy aligns the
literal Borel; odd-index traces reassemble invariant extensions of these
factors and preserve the original common quadratic actor.

Classification/Sieve/LinearTwo supplies all these inputs on the original
KT span quotient. The field-order-four endpoint is retained; its Hermitian
Borel has nonzero fixed space and cannot be excluded by this argument.
Source: Aschbacher--Smith K.3.1, pp.453--454; 14.6.20, p.1037.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.NormalLinearTwo
open ChapterB.QuasisimpleSource
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open OriginalModule.Normal RepresentationReduction
open RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio
open RepresentationReduction.SourceRestrictions
open RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity
open Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure
universe u v

private theorem fixedSpace_eq_bot_of_marked_normalizer
    {D E V W : Type*} [Group D] [Group E] [Finite D] [Finite E]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D V) (σ : Representation (ZMod 2) E W)
    (a : D ≃* E) (c : V ≃ₗ[ZMod 2] W)
    (he : ∀ g v, c (ρ g v) = σ (a g) (c v))
    (B : Subgroup D) (C : Subgroup E)
    (hB : ∃ P : Sylow 2 D, normalizer (P : Set D) = B)
    (hC : ∃ P : Sylow 2 E, normalizer (P : Set E) = C)
    (hz : fixedSpace σ C = ⊥) : fixedSpace ρ B = ⊥ := by
  obtain ⟨g,hg,hcoord⟩ := exists_innerIntertwiner_sylowNormalizer B C hB hC ρ σ a c he
  exact fixedSpace_eq_bot_of_equivariant ρ σ (a.trans (MulAut.conj g)).toMonoidHom
    (c.trans (innerIntertwiner σ g)) hcoord B C hg hz

/-- Both recognized PSL₂ modules have zero Borel fixed space above field order four. -/
theorem fixedSpace_eq_bot_of_source_model
    {D : Type u} [Group D] [Finite D] {V : Type v}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D)
    (h : ChapterK.RankOne.SourceHypotheses ρ K)
    {f : ℕ} (hf : 2 < f) (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 (2 ^ f))
    (B : Subgroup K) (hB : ∃ P : Sylow 2 K, normalizer (P : Set K) = B) :
    fixedSpace (ρ.comp K.subtype) B = ⊥ := by
  obtain ⟨F,_,_,_,hF,_,_,halt⟩ := h.psl2_module_recognition (by omega) hm
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  rcases halt with ⟨_,_,⟨N⟩⟩ | ⟨s,hrs,_,hs,_,_,⟨N⟩⟩
  · exact fixedSpace_eq_bot_of_marked_normalizer (ρ.comp K.subtype)
      (SL2.BinarySmall.natural (K := F)) N.groupEquiv N.coordinates N.intertwines
      B (Matrix.SpecialLinearGroup.rankOneBorel F) hB
      RepresentationReduction.SourceRestrictions.Cases.Exchanged.BorelMarkings.slTwo_borel_normalizer
      (slTwo_borel_fixedSpace_eq_bot (by
        rw [hF]
        have hp : 4 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ f)
        omega))
  · let : NeZero s := ⟨hs.ne'⟩
    let : Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.fixedField s) := ZMod.algebra _ 2
    let : Module (ZMod 2) (OrthogonalFourMinus.FiniteModel.Space s) :=
      Module.compHom (OrthogonalFourMinus.FiniteModel.Space s)
        (algebraMap (ZMod 2) (OrthogonalFourMinus.FiniteModel.fixedField s))
    exact fixedSpace_eq_bot_of_marked_normalizer (ρ.comp K.subtype)
      (SL2.BinarySmall.hermitian s) N.groupEquiv N.coordinates N.intertwines
      B (Matrix.SpecialLinearGroup.rankOneBorel (OrthogonalFourMinus.FiniteModel.Field s)) hB
      RepresentationReduction.SourceRestrictions.Cases.Exchanged.BorelMarkings.slTwo_borel_normalizer
      (OrthogonalFourMinus.BorelFixed.fixedSpace_eq_bot s (by omega))

variable {D V : Type u} [Group D] [Finite D] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal] [IsQuasisimple K]

/-- Pull the Borel calculation back through the original faithful action image. -/
theorem fixedSpace_eq_bot_of_irreducible_component
    (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hquot : IsPGroup 2 (D ⧸ K)) (hZ : center K = ⊥)
    (hi : IsIrreducible (ρ.comp K.subtype))
    (hn : ¬ (⊤ : Submodule (ZMod 2) V) ≤ fixedSpace ρ K)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A) (hAC : A ⊓ centralizer (K : Set D) = ⊥)
    {f : ℕ} (hf : 2 < f)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 (2 ^ f))
    (B : Subgroup K) (hB : ∃ P : Sylow 2 K, normalizer (P : Set K) = B) :
    fixedSpace (ρ.comp K.subtype) B = ⊥ := by
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
  let C := B.map e.toMonoidHom
  have hC : ∃ P : Sylow 2 (generalizedFitting (actionImage ρ)), normalizer (P : Set _) = C :=
    exists_sylow_normalizer_of_equiv e.symm C B
      ((Subgroup.map_symm_eq_iff_map_eq (e := e) B).mpr rfl) hB
  have hm' : ClassicalGroup.IsPSL
      (generalizedFitting (actionImage ρ) ⧸ center (generalizedFitting (actionImage ρ)))
      2 (2 ^ f) := by
    obtain ⟨E,_,_,hE,⟨eE⟩⟩ := hm
    exact ⟨E,inferInstance,inferInstance,hE,⟨(centralQuotientCongr e).symm.trans eE⟩⟩
  have hzero := fixedSpace_eq_bot_of_source_model (imageRepresentation ρ)
    (generalizedFitting (actionImage ρ)) hyp hf hm' C hC
  apply bot_unique
  intro w hw
  apply hzero.le
  rintro ⟨x,hx⟩
  obtain ⟨b,hb,rfl⟩ := hx
  exact hw ⟨b,hb⟩

/-- Extend the Borel fixed-space calculation through invariant sections. -/
theorem fixedSpace_le_of_quadratic_supplement
    (hZ : center K = ⊥) (A : Subgroup D) (hgen : K ⊔ A = ⊤)
    (hs : IsSQTK KnownSimple.IsKnownSimple D) (hquot : IsPGroup 2 (D ⧸ K))
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A) (hAC : A ⊓ centralizer (K : Set D) = ⊥)
    {f : ℕ} (hf : 2 < f)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 (2 ^ f))
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
      A hA hq hc hAC hf hm B ⟨P,hP⟩]
    exact bot_le

/-- The fixed-space consequence retains the original component and its marked Borel. -/
theorem fixedSpace_le_of_quadratic_actor
    (hZ : center K = ⊥) (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A) (hAC : A ⊓ centralizer (K : Set D) = ⊥)
    {f : ℕ} (hf : 2 < f)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 (2 ^ f))
    (B : Subgroup K) (hB : ∃ P : Sylow 2 K, normalizer (P : Set K) = B) :
    fixedSpace (ρ.comp K.subtype) B ≤ fixedSpace (ρ.comp K.subtype) ⊤ := by
  let : IsQuasisimple (K.subgroupOf (K ⊔ A)) := componentInSup_quasisimple K A
  apply fixedSpace_le_of_componentInSup ρ K A B
  exact fixedSpace_le_of_quadratic_supplement (ρ.comp (K ⊔ A).subtype)
    (K.subgroupOf (K ⊔ A)) (componentInSup_center K A hZ) (A.subgroupOf (K ⊔ A))
    (componentInSup_generated K A) (hs.subgroup (K ⊔ A)) (componentInSup_quotient K A hA)
    (actorInSup_elementary K A hA) (actorInSup_quadratic ρ K A hq)
    (actorInSup_bound ρ K A hc) (actorInSup_faithful K A hAC) hf
    (by
      obtain ⟨E,_,_,hE,⟨eE⟩⟩ := hm
      exact ⟨E,inferInstance,inferInstance,hE,
        ⟨(centralQuotientCongr (componentInSupEquiv K A)).trans eE⟩⟩)
    (borelInSup K A B) (borelInSup_sylow K A B hB)

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.NormalLinearTwo
